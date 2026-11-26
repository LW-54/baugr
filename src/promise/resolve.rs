//! Kosaraju SCC stratification and observer-local stratified fixed-point quenching.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;

use super::cond::Cond;
use super::system::{CompatIndex, PromiseSystem};
use super::{Binding, Body, BodyAlgebra, EvalError, Resolved};

impl<A: Ord + Clone, P: Ord + Clone, D: BodyAlgebra> PromiseSystem<A, P, D> {
    /// Computes a minimal valid stratification rank per promise via Kosaraju SCC decomposition.
    ///
    /// Positive dependencies satisfy `rank(dep) <= rank(p)`; negated dependencies satisfy
    /// `rank(dep) < rank(p)`. By Lean 4 theorem `stratification_independent` (Apt–Blair–Walker),
    /// any valid stratification yields the exact same resolved fixed point.
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableNegativeCycle`] if any strongly connected component
    /// contains a negated dependency edge.
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
            compat.cond_deps(false, &pr.cond, &mut d);
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
            for (d, is_neg) in ds {
                if *is_neg
                    && let Some(&cd) = comp_of.get(d)
                    && cp == cd
                    && let Some(scc) = comps.get(cp)
                {
                    return Err(EvalError::UnstratifiableNegativeCycle(scc.clone()));
                }
            }
        }

        let mut comp_rank = vec![0usize; comps.len()];
        for (cid, members) in comps.iter().enumerate() {
            let mut r = 0usize;
            for p in members {
                if let Some(ds) = deps.get(p) {
                    for (d, is_neg) in ds {
                        if let Some(&cd) = comp_of.get(d)
                            && cd != cid
                            && let Some(&prev_rank) = comp_rank.get(cd)
                        {
                            let need = if *is_neg {
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

    fn eval_cond<F>(
        &self,
        compat: &CompatIndex<P>,
        alpha: &F,
        qset: &BTreeSet<P>,
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
                .is_some_and(|pq| &pq.promiser == me && qset.contains(q) && alpha(me, q)),
            Cond::Interior(q) => self.promises.get(q).is_some_and(|pq| {
                self.hierarchy.is_strict_ancestor(me, &pq.promiser)
                    && qset.contains(q)
                    && alpha(me, q)
            }),
            Cond::Assisted {
                use_id,
                min_providers,
            } => {
                let Some(pu) = self.promises.get(use_id) else {
                    return false;
                };
                if &pu.promiser != me || !pu.is_use() || !qset.contains(use_id) {
                    return false;
                }
                let n = compat.offers_for_use.get(use_id).map_or(0, |offers| {
                    offers
                        .iter()
                        .filter(|oid| qset.contains(*oid) && alpha(me, oid))
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
                if &po.promiser != me || !po.is_offer() || !qset.contains(offer_id) {
                    return false;
                }
                let n = compat
                    .visible_uses_for_offer
                    .get(offer_id)
                    .map_or(0, |uses| {
                        uses.iter()
                            .filter(|uid| qset.contains(*uid) && alpha(me, uid))
                            .count()
                    });
                n >= *min_acceptors
            }
            Cond::AtLeast(k, cs) => {
                cs.iter()
                    .filter(|c| self.eval_cond(compat, alpha, qset, me, c))
                    .count()
                    >= *k
            }
            Cond::Not(c) => !self.eval_cond(compat, alpha, qset, me, c),
        }
    }

    /// Resolves quenched promises and active bindings under observer-local assessment
    /// `alpha(observer, promise_id)` (`ADR-0018` A3; `arXiv:2606.08552v1` L1070).
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableNegativeCycle`] if the system cannot be stratified.
    pub fn resolve<F>(&self, alpha: F) -> Result<Resolved<A, P, D::Overlap>, EvalError<P>>
    where
        F: Fn(&A, &P) -> bool,
    {
        let compat = self.build_compat_index();
        let strata = self.stratify_with(&compat)?;
        let max_s = strata.values().copied().max().unwrap_or(0);
        let mut quenched: BTreeSet<P> = BTreeSet::new();

        for s in 0..=max_s {
            let cur_ids: Vec<P> = strata
                .iter()
                .filter(|(_, r)| **r == s)
                .map(|(p, _)| p.clone())
                .collect();
            loop {
                let mut next = quenched.clone();
                for pid in &cur_ids {
                    if let Some(pr) = self.promises.get(pid) {
                        if self.eval_cond(&compat, &alpha, &quenched, &pr.promiser, &pr.cond) {
                            next.insert(pid.clone());
                        } else {
                            next.remove(pid);
                        }
                    }
                }
                if next == quenched {
                    break;
                }
                quenched = next;
            }
        }

        let mut bindings = Vec::new();
        for po in self.promises.values() {
            let Body::Offer(ob) = &po.body else {
                continue;
            };
            if !quenched.contains(&po.id) {
                continue;
            }
            let Some(use_ids) = compat.uses_for_offer.get(&po.id) else {
                continue;
            };
            for uid in use_ids {
                if !quenched.contains(uid) {
                    continue;
                }
                let Some(pu) = self.promises.get(uid) else {
                    continue;
                };
                let Body::Use(ub) = &pu.body else {
                    continue;
                };
                if alpha(&pu.promiser, &po.id)
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
            quenched,
            bindings,
            strata,
        })
    }

    /// Static compile-time resolution under uniform optimistic assessment `α ≡ true`.
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableNegativeCycle`] if the system cannot be stratified.
    pub fn resolve_optimistic(&self) -> Result<Resolved<A, P, D::Overlap>, EvalError<P>> {
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
