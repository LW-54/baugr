//! Kosaraju SCC stratification and observer-local stratified fixed-point quenching
//! over full value-carrying promise states `P -> Option<Body<O, U>>`.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;

use super::cond::{Cond, Obs};
use super::system::{CompatIndex, PromiseSystem};
use super::{
    Binding, Body, BodyAlgebra, BodySpec, DeriveAlgebra, EvalError, LocalView, ObservedOffer,
    ObservedUse, Promise, Resolved,
};

impl<A: Ord + Clone, P: Ord + Clone, D: BodyAlgebra, R> PromiseSystem<A, P, D, R> {
    /// Computes a minimal valid stratification rank per promise via Kosaraju SCC decomposition.
    ///
    /// Positive `Cond` dependencies satisfy `rank(dep) <= rank(p)`; negated `Cond`
    /// dependencies and all value-derivation `Obs` dependencies satisfy `rank(dep) < rank(p)`.
    /// By Lean 4 theorem `stratification_independent` (Apt–Blair–Walker), any valid
    /// stratification yields the exact same resolved value state.
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableCycle`] if any strongly connected component
    /// contains a negated condition edge or value-derivation `Obs` edge.
    pub fn stratify(&self) -> Result<BTreeMap<P, usize>, EvalError<P>> {
        let compat = self.build_compat_index();
        self.stratify_with(&compat)
    }

    pub(crate) fn stratify_with(
        &self,
        compat: &CompatIndex<P>,
    ) -> Result<BTreeMap<P, usize>, EvalError<P>> {
        let mut deps: BTreeMap<P, Vec<(P, bool)>> = BTreeMap::new();
        for (pid, pr) in &self.promises {
            let mut d = Vec::new();
            compat.promise_deps(&pr.cond, pr.obs(), &mut d);
            deps.insert(pid.clone(), d);
        }

        let ids: Vec<P> = self.promises.keys().cloned().collect();
        let mut adj: BTreeMap<P, BTreeSet<P>> = BTreeMap::new();
        let mut rev: BTreeMap<P, BTreeSet<P>> = BTreeMap::new();
        for id in &ids {
            adj.entry(id.clone()).or_default();
            rev.entry(id.clone()).or_default();
        }
        for (p, ds) in &deps {
            for (d, _) in ds {
                if self.promises.contains_key(d) {
                    adj.entry(d.clone()).or_default().insert(p.clone());
                    rev.entry(p.clone()).or_default().insert(d.clone());
                }
            }
        }

        let mut visited = BTreeSet::new();
        let mut order = Vec::with_capacity(ids.len());
        for id in &ids {
            dfs_postorder(id, &adj, &mut visited, &mut order);
        }

        let mut comp_of: BTreeMap<P, usize> = BTreeMap::new();
        let mut comps: Vec<BTreeSet<P>> = Vec::new();
        for u in order.into_iter().rev() {
            if !comp_of.contains_key(&u) {
                let cid = comps.len();
                let mut members = BTreeSet::new();
                dfs_component(&u, cid, &rev, &mut comp_of, &mut members);
                comps.push(members);
            }
        }

        for (p, ds) in &deps {
            let Some(&cp) = comp_of.get(p) else {
                continue;
            };
            for (d, is_strict) in ds {
                if *is_strict
                    && let Some(&cd) = comp_of.get(d)
                    && cp == cd
                    && let Some(scc) = comps.get(cp)
                {
                    return Err(EvalError::UnstratifiableCycle(scc.clone()));
                }
            }
        }

        let mut comp_rank = vec![0usize; comps.len()];
        for (cid, members) in comps.iter().enumerate() {
            let mut r = 0usize;
            for p in members {
                if let Some(ds) = deps.get(p) {
                    for (d, is_strict) in ds {
                        if let Some(&cd) = comp_of.get(d)
                            && cd != cid
                            && let Some(&prev_rank) = comp_rank.get(cd)
                        {
                            let need = if *is_strict {
                                prev_rank.saturating_add(1)
                            } else {
                                prev_rank
                            };
                            if need > r {
                                r = need;
                            }
                        }
                    }
                }
            }
            if let Some(slot) = comp_rank.get_mut(cid) {
                *slot = r;
            }
        }

        let mut strata = BTreeMap::new();
        for (p, cid) in comp_of {
            let rank = comp_rank.get(cid).copied().unwrap_or(0);
            strata.insert(p, rank);
        }
        Ok(strata)
    }

    fn runtime_overlap(
        &self,
        bodies: &BTreeMap<P, Body<D::Offer, D::Use>>,
        offer_id: &P,
        use_id: &P,
    ) -> Option<D::Overlap> {
        match (bodies.get(offer_id), bodies.get(use_id)) {
            (Some(Body::Offer(ob)), Some(Body::Use(ub))) => self.algebra.overlap(ob, ub),
            _ => None,
        }
    }

    fn eval_cond<F>(
        &self,
        compat: &CompatIndex<P>,
        alpha: &F,
        bodies: &BTreeMap<P, Body<D::Offer, D::Use>>,
        me: &A,
        cond: &Cond<P>,
    ) -> bool
    where
        F: Fn(&A, &P) -> bool,
    {
        match cond {
            Cond::SelfPromise(q) => self
                .promises
                .get(q)
                .is_some_and(|pq| &pq.promiser == me && bodies.contains_key(q) && alpha(me, q)),
            Cond::Interior(q) => self.promises.get(q).is_some_and(|pq| {
                self.hierarchy.is_strict_ancestor(me, &pq.promiser)
                    && bodies.contains_key(q)
                    && alpha(me, q)
            }),
            Cond::Assisted {
                use_id,
                min_providers,
            } => {
                let Some(pu) = self.promises.get(use_id) else {
                    return false;
                };
                if &pu.promiser != me
                    || !pu.is_use()
                    || !bodies.contains_key(use_id)
                    || !alpha(me, use_id)
                {
                    return false;
                }
                let n = compat.offers_for_use.get(use_id).map_or(0, |offers| {
                    offers
                        .iter()
                        .filter(|oid| {
                            self.runtime_overlap(bodies, oid, use_id).is_some() && alpha(me, oid)
                        })
                        .count()
                });
                n >= *min_providers
            }
            Cond::Accepted {
                offer_id,
                min_acceptors,
            } => {
                let Some(po) = self.promises.get(offer_id) else {
                    return false;
                };
                if &po.promiser != me
                    || !po.is_offer()
                    || !bodies.contains_key(offer_id)
                    || !alpha(me, offer_id)
                {
                    return false;
                }
                let n = compat
                    .visible_uses_for_offer
                    .get(offer_id)
                    .map_or(0, |uses| {
                        uses.iter()
                            .filter(|uid| {
                                self.runtime_overlap(bodies, offer_id, uid).is_some()
                                    && alpha(me, uid)
                            })
                            .count()
                    });
                n >= *min_acceptors
            }
            Cond::AtLeast(k, cs) => {
                cs.iter()
                    .filter(|c| self.eval_cond(compat, alpha, bodies, me, c))
                    .count()
                    >= *k
            }
            Cond::Not(c) => !self.eval_cond(compat, alpha, bodies, me, c),
        }
    }

    fn build_local_view<'a, F>(
        &'a self,
        compat: &CompatIndex<P>,
        alpha: &F,
        bodies: &'a BTreeMap<P, Body<D::Offer, D::Use>>,
        me: &A,
        obs: &'a [Obs<P>],
    ) -> LocalView<'a, A, P, D>
    where
        F: Fn(&A, &P) -> bool,
    {
        let mut self_bodies = Vec::new();
        let mut assisted_offers = Vec::new();
        let mut accepted_uses = Vec::new();
        let mut interior_bodies = Vec::new();

        for o in obs {
            match o {
                Obs::SelfPromise(q) => {
                    if let (Some(pq), Some(b)) = (self.promises.get(q), bodies.get(q))
                        && &pq.promiser == me
                        && alpha(me, q)
                    {
                        self_bodies.push((&pq.id, b));
                    }
                }
                Obs::Assisted(use_id) => {
                    if let (Some(pu), Some(Body::Use(ub))) =
                        (self.promises.get(use_id), bodies.get(use_id))
                        && &pu.promiser == me
                        && pu.is_use()
                        && alpha(me, use_id)
                        && let Some(offers) = compat.offers_for_use.get(use_id)
                    {
                        for oid in offers {
                            if alpha(me, oid)
                                && let (Some(po), Some(Body::Offer(ob))) =
                                    (self.promises.get(oid), bodies.get(oid))
                                && let Some(ov) = self.algebra.overlap(ob, ub)
                            {
                                assisted_offers.push(ObservedOffer {
                                    use_id: &pu.id,
                                    offer_id: &po.id,
                                    promiser: &po.promiser,
                                    offer: ob,
                                    overlap: ov,
                                });
                            }
                        }
                    }
                }
                Obs::Accepted(offer_id) => {
                    if let (Some(po), Some(Body::Offer(ob))) =
                        (self.promises.get(offer_id), bodies.get(offer_id))
                        && &po.promiser == me
                        && po.is_offer()
                        && alpha(me, offer_id)
                        && let Some(uses) = compat.visible_uses_for_offer.get(offer_id)
                    {
                        for uid in uses {
                            if alpha(me, uid)
                                && let (Some(pu), Some(Body::Use(ub))) =
                                    (self.promises.get(uid), bodies.get(uid))
                                && let Some(ov) = self.algebra.overlap(ob, ub)
                            {
                                accepted_uses.push(ObservedUse {
                                    offer_id: &po.id,
                                    use_id: &pu.id,
                                    consumer: &pu.promiser,
                                    use_body: ub,
                                    overlap: ov,
                                });
                            }
                        }
                    }
                }
                Obs::Interior(q) => {
                    if let (Some(pq), Some(b)) = (self.promises.get(q), bodies.get(q))
                        && self.hierarchy.is_strict_ancestor(me, &pq.promiser)
                        && alpha(me, q)
                    {
                        interior_bodies.push((&pq.id, &pq.promiser, b));
                    }
                }
            }
        }

        LocalView {
            self_bodies,
            assisted_offers,
            accepted_uses,
            interior_bodies,
        }
    }
}

impl<A, P, D, R> PromiseSystem<A, P, D, R>
where
    A: Ord + Clone,
    P: Ord + Clone,
    D: DeriveAlgebra<A, P, R>,
    D::Offer: Clone + PartialEq,
    D::Use: Clone + PartialEq,
{
    fn eval_rule<F>(
        &self,
        compat: &CompatIndex<P>,
        alpha: &F,
        bodies: &BTreeMap<P, Body<D::Offer, D::Use>>,
        pr: &Promise<A, P, D::Offer, D::Use, R>,
    ) -> Option<Body<D::Offer, D::Use>>
    where
        F: Fn(&A, &P) -> bool,
    {
        match &pr.spec {
            BodySpec::Fixed(b) => Some(b.clone()),
            BodySpec::DerivedOffer { obs, rule } => {
                let view = self.build_local_view(compat, alpha, bodies, &pr.promiser, obs);
                self.algebra.derive_offer(rule, &view).map(Body::Offer)
            }
            BodySpec::DerivedUse { obs, rule } => {
                let view = self.build_local_view(compat, alpha, bodies, &pr.promiser, obs);
                self.algebra.derive_use(rule, &view).map(Body::Use)
            }
        }
    }

    /// Resolves quenched promise bodies and active bindings under observer-local
    /// assessment `alpha(observer, promise_id)` (`ADR-0018` A3; `arXiv:2606.08552v1` L1070).
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableCycle`] if the system cannot be stratified.
    pub fn resolve<F>(&self, alpha: F) -> Result<Resolved<A, P, D>, EvalError<P>>
    where
        F: Fn(&A, &P) -> bool,
    {
        let compat = self.build_compat_index();
        let strata = self.stratify_with(&compat)?;
        let max_s = strata.values().copied().max().unwrap_or(0);
        let mut bodies: BTreeMap<P, Body<D::Offer, D::Use>> = BTreeMap::new();

        for s in 0..=max_s {
            let cur_ids: Vec<P> = strata
                .iter()
                .filter(|(_, r)| **r == s)
                .map(|(p, _)| p.clone())
                .collect();

            // Pre-evaluate every promise's rule once on the frozen lower strata `< s`.
            let mut candidates: BTreeMap<P, Body<D::Offer, D::Use>> = BTreeMap::new();
            for pid in &cur_ids {
                if let Some(pr) = self.promises.get(pid)
                    && let Some(body) = self.eval_rule(&compat, &alpha, &bodies, pr)
                {
                    candidates.insert(pid.clone(), body);
                }
            }

            loop {
                let mut next = bodies.clone();
                for pid in &cur_ids {
                    if let Some(pr) = self.promises.get(pid) {
                        if self.eval_cond(&compat, &alpha, &bodies, &pr.promiser, &pr.cond)
                            && let Some(body) = candidates.get(pid)
                        {
                            next.insert(pid.clone(), body.clone());
                        } else {
                            next.remove(pid);
                        }
                    }
                }
                if next == bodies {
                    break;
                }
                bodies = next;
            }
        }

        let mut bindings = Vec::new();
        for po in self.promises.values() {
            if !po.is_offer() {
                continue;
            }
            let Some(Body::Offer(ob)) = bodies.get(&po.id) else {
                continue;
            };
            let Some(use_ids) = compat.uses_for_offer.get(&po.id) else {
                continue;
            };
            for uid in use_ids {
                let Some(Body::Use(ub)) = bodies.get(uid) else {
                    continue;
                };
                let Some(pu) = self.promises.get(uid) else {
                    continue;
                };
                if alpha(&pu.promiser, &po.id)
                    && alpha(&pu.promiser, &pu.id)
                    && let Some(ov) = self.algebra.overlap(ob, ub)
                {
                    bindings.push(Binding {
                        offer_id: po.id.clone(),
                        use_id: pu.id.clone(),
                        promiser: po.promiser.clone(),
                        consumer: pu.promiser.clone(),
                        overlap: ov,
                    });
                }
            }
        }

        Ok(Resolved {
            bodies,
            bindings,
            strata,
        })
    }

    /// Static compile-time resolution under uniform optimistic assessment `α ≡ true`.
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableCycle`] if the system cannot be stratified.
    pub fn resolve_optimistic(&self) -> Result<Resolved<A, P, D>, EvalError<P>> {
        self.resolve(|_, _| true)
    }
}

fn dfs_postorder<P: Ord + Clone>(
    start: &P,
    adj: &BTreeMap<P, BTreeSet<P>>,
    visited: &mut BTreeSet<P>,
    order: &mut Vec<P>,
) {
    if !visited.insert(start.clone()) {
        return;
    }
    let mut stack: Vec<(P, Vec<P>)> = Vec::new();
    let neighbors = adj
        .get(start)
        .map(|s| s.iter().cloned().collect())
        .unwrap_or_default();
    stack.push((start.clone(), neighbors));

    while let Some((node, mut rem)) = stack.pop() {
        if let Some(next) = rem.pop() {
            stack.push((node, rem));
            if visited.insert(next.clone()) {
                let ns = adj
                    .get(&next)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default();
                stack.push((next, ns));
            }
        } else {
            order.push(node);
        }
    }
}

fn dfs_component<P: Ord + Clone>(
    start: &P,
    cid: usize,
    rev: &BTreeMap<P, BTreeSet<P>>,
    comp_of: &mut BTreeMap<P, usize>,
    members: &mut BTreeSet<P>,
) {
    let mut stack = vec![start.clone()];
    while let Some(u) = stack.pop() {
        if comp_of.contains_key(&u) {
            continue;
        }
        comp_of.insert(u.clone(), cid);
        members.insert(u.clone());
        if let Some(ns) = rev.get(&u) {
            for v in ns {
                if !comp_of.contains_key(v) {
                    stack.push(v.clone());
                }
            }
        }
    }
}
