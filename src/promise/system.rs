//! [`PromiseSystem`] builder, precomputed static compatibility index,
//! dependency extraction, complete-information diagnostics, and static upper bound.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::convert::Infallible;
use core::fmt;

use super::cond::{Cond, Obs};
use super::hierarchy::{Hierarchy, HierarchyError};
use super::{
    AlgebraPromise, Binding, Body, BodyAlgebra, BodySpec, ConditionWarning, IncompleteInfoWarning,
    Promise, PromiseMap, Resolved,
};

/// Precomputed conservative static offer↔use compatibility index for a [`PromiseSystem`].
///
/// For static offer–use pairs, checks exact [`BodyAlgebra::overlap`]; when either
/// endpoint is value-derived, checks structural compatibility (polarity, targeting,
/// scope visibility, and opaque boundaries) and evaluates exact `overlap` at runtime.
pub struct CompatIndex<P> {
    pub offers_for_use: BTreeMap<P, Vec<P>>,
    pub uses_for_offer: BTreeMap<P, Vec<P>>,
    pub visible_uses_for_offer: BTreeMap<P, Vec<P>>,
}

impl<P: Ord + Clone> CompatIndex<P> {
    pub fn cond_deps(&self, neg: bool, cond: &Cond<P>, out: &mut Vec<(P, bool)>) {
        match cond {
            Cond::SelfPromise(q) | Cond::Interior(q) => out.push((q.clone(), neg)),
            Cond::Assisted { use_id, .. } => {
                out.push((use_id.clone(), neg));
                if let Some(offers) = self.offers_for_use.get(use_id) {
                    for oid in offers {
                        out.push((oid.clone(), neg));
                    }
                }
            }
            Cond::Accepted { offer_id, .. } => {
                out.push((offer_id.clone(), neg));
                if let Some(uses) = self.visible_uses_for_offer.get(offer_id) {
                    for uid in uses {
                        out.push((uid.clone(), neg));
                    }
                }
            }
            Cond::AtLeast(_, cs) => {
                for c in cs {
                    self.cond_deps(neg, c, out);
                }
            }
            Cond::Not(c) => self.cond_deps(!neg, c, out),
        }
    }

    pub fn obs_deps(&self, obs: &[Obs<P>], out: &mut Vec<(P, bool)>) {
        for o in obs {
            match o {
                Obs::SelfPromise(q) | Obs::Interior(q) => out.push((q.clone(), true)),
                Obs::Assisted(use_id) => {
                    out.push((use_id.clone(), true));
                    if let Some(offers) = self.offers_for_use.get(use_id) {
                        for oid in offers {
                            out.push((oid.clone(), true));
                        }
                    }
                }
                Obs::Accepted(offer_id) => {
                    out.push((offer_id.clone(), true));
                    if let Some(uses) = self.visible_uses_for_offer.get(offer_id) {
                        for uid in uses {
                            out.push((uid.clone(), true));
                        }
                    }
                }
            }
        }
    }

    pub fn promise_deps(&self, cond: &Cond<P>, obs: &[Obs<P>], out: &mut Vec<(P, bool)>) {
        self.cond_deps(false, cond, out);
        self.obs_deps(obs, out);
    }
}

/// Complete autonomous agent & conditional promise system.
///
/// The rule type parameter `R` defaults to [`Infallible`] for purely static systems
/// (constructed via [`PromiseSystem::new`]). Systems using value-derived promises
/// (`+f(obs) | C`) instantiate `R` via [`PromiseSystem::with_rules`].
pub struct PromiseSystem<A, P, D: BodyAlgebra, R = Infallible> {
    pub(crate) hierarchy: Hierarchy<A>,
    pub(crate) promises: PromiseMap<A, P, D, R>,
    pub(crate) algebra: D,
}

impl<A, P, D, R> Clone for PromiseSystem<A, P, D, R>
where
    A: Clone,
    P: Clone,
    D: BodyAlgebra + Clone,
    D::Offer: Clone,
    D::Use: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        Self {
            hierarchy: self.hierarchy.clone(),
            promises: self.promises.clone(),
            algebra: self.algebra.clone(),
        }
    }
}

impl<A, P, D, R> fmt::Debug for PromiseSystem<A, P, D, R>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra + fmt::Debug,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PromiseSystem")
            .field("agents", &self.hierarchy.agents)
            .field("parent", &self.hierarchy.parent)
            .field("opaque_superagents", &self.hierarchy.opaque_superagents)
            .field("promises", &self.promises)
            .field("algebra", &self.algebra)
            .finish()
    }
}

impl<A: Ord + Clone, P: Ord + Clone, D: BodyAlgebra> PromiseSystem<A, P, D, Infallible> {
    /// Creates an empty static promise system parameterized by `algebra`.
    #[must_use]
    pub const fn new(algebra: D) -> Self {
        Self::with_rules(algebra)
    }

    /// Computes the maximal static upper-bound binding view `B_max(S)` across all
    /// statically compatible offer–use pairs (ignoring conditions and `α`).
    ///
    /// By Lean 4 theorem `static_discharge_universal`, any downward-closed [`crate::ScopeLaw`]
    /// (such as [`crate::ValencyLaw`], [`crate::BudgetBy`], [`crate::DisjointBy`], or
    /// [`crate::AgreementBy`]) that passes on this upper bound is mathematically guaranteed
    /// to hold under **every** possible runtime assessment `α` (including blackout failovers).
    #[must_use]
    pub fn static_upper_bound(&self) -> Resolved<A, P, D>
    where
        D::Offer: Clone,
        D::Use: Clone,
    {
        let mut bodies = BTreeMap::new();
        for (pid, pr) in &self.promises {
            if let BodySpec::Fixed(b) = &pr.spec {
                bodies.insert(pid.clone(), b.clone());
            }
        }

        let mut bindings = Vec::new();
        for po in self.promises.values() {
            let BodySpec::Fixed(Body::Offer(ob)) = &po.spec else {
                continue;
            };
            for pu in self.promises.values() {
                let BodySpec::Fixed(Body::Use(ub)) = &pu.spec else {
                    continue;
                };
                if po.target.contains(&pu.promiser)
                    && po.in_scope(&pu.promiser)
                    && pu.target.contains(&po.promiser)
                    && self.hierarchy.no_opaque_wall(&po.promiser, &pu.promiser)
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

        Resolved {
            bodies,
            bindings,
            strata: BTreeMap::new(),
        }
    }
}

impl<A: Ord + Clone, P: Ord + Clone, D: BodyAlgebra, R> PromiseSystem<A, P, D, R> {
    /// Creates an empty promise system supporting both static promises and value-derived
    /// conditional promises parameterized by rule type `R`.
    #[must_use]
    pub const fn with_rules(algebra: D) -> Self {
        Self {
            hierarchy: Hierarchy::new(),
            promises: BTreeMap::new(),
            algebra,
        }
    }

    /// Registers an autonomous agent.
    pub fn add_agent(&mut self, agent: A) {
        self.hierarchy.add_agent(agent);
    }

    /// Registers a dressed superagent with explicit `opaque` boundary control
    /// (`arXiv:1505.01716v1` §3.7).
    pub fn add_superagent(&mut self, superagent: A, opaque: bool) {
        self.hierarchy.add_superagent(superagent, opaque);
    }

    /// Places `child` inside `superagent` (`superagent +Contains child`).
    ///
    /// # Errors
    /// Returns [`HierarchyError::SelfContainment`] if `superagent == child`, or
    /// [`HierarchyError::Cycle`] if `child` is already an ancestor of `superagent`.
    pub fn contain(&mut self, superagent: A, child: A) -> Result<(), HierarchyError<A>> {
        self.hierarchy.contain(superagent, child)
    }

    /// Inserts a promise into the system (also registering its promiser).
    ///
    /// Returns the previously registered promise with the same identifier, if any,
    /// so accidental duplicate IDs are never silently lost.
    pub fn add_promise(
        &mut self,
        promise: AlgebraPromise<A, P, D, R>,
    ) -> Option<AlgebraPromise<A, P, D, R>> {
        self.hierarchy.add_agent(promise.promiser.clone());
        self.promises.insert(promise.id.clone(), promise)
    }

    /// Returns all registered agents.
    #[must_use]
    pub const fn agents(&self) -> &BTreeSet<A> {
        &self.hierarchy.agents
    }

    /// Returns the superagent containment parent map (`child -> superagent`).
    #[must_use]
    pub const fn parents(&self) -> &BTreeMap<A, A> {
        &self.hierarchy.parent
    }

    /// Returns the immediate containing superagent of `agent`, if any.
    #[must_use]
    pub fn parent_of(&self, agent: &A) -> Option<&A> {
        self.hierarchy.parent_of(agent)
    }

    /// Returns the set of opaque superagents.
    #[must_use]
    pub const fn opaque_superagents(&self) -> &BTreeSet<A> {
        &self.hierarchy.opaque_superagents
    }

    /// Returns all registered promises indexed by identifier.
    #[must_use]
    pub const fn promises(&self) -> &PromiseMap<A, P, D, R> {
        &self.promises
    }

    /// Returns a reference to the underlying [`BodyAlgebra`].
    #[must_use]
    pub const fn algebra(&self) -> &D {
        &self.algebra
    }

    /// Returns `true` if `ancestor` strictly contains `node` in the superagent hierarchy.
    #[must_use]
    pub fn is_strict_ancestor(&self, ancestor: &A, node: &A) -> bool {
        self.hierarchy.is_strict_ancestor(ancestor, node)
    }

    /// Returns `superagent` together with all strict descendants contained within it.
    #[must_use]
    pub fn members_of(&self, superagent: &A) -> BTreeSet<A> {
        self.hierarchy.members_of(superagent)
    }

    pub(crate) fn may_bind(
        &self,
        po: &Promise<A, P, D::Offer, D::Use, R>,
        pu: &Promise<A, P, D::Offer, D::Use, R>,
    ) -> bool {
        if !(po.is_offer()
            && pu.is_use()
            && po.target.contains(&pu.promiser)
            && po.in_scope(&pu.promiser)
            && pu.target.contains(&po.promiser)
            && self.hierarchy.no_opaque_wall(&po.promiser, &pu.promiser))
        {
            return false;
        }
        match (&po.spec, &pu.spec) {
            (BodySpec::Fixed(Body::Offer(ob)), BodySpec::Fixed(Body::Use(ub))) => {
                self.algebra.overlap(ob, ub).is_some()
            }
            _ => true,
        }
    }

    pub(crate) fn build_compat_index(&self) -> CompatIndex<P> {
        let mut offers_for_use: BTreeMap<P, Vec<P>> = BTreeMap::new();
        let mut uses_for_offer: BTreeMap<P, Vec<P>> = BTreeMap::new();
        let mut visible_uses_for_offer: BTreeMap<P, Vec<P>> = BTreeMap::new();

        for po in self.promises.values() {
            if !po.is_offer() {
                continue;
            }
            for pu in self.promises.values() {
                if !pu.is_use() {
                    continue;
                }
                if self.may_bind(po, pu) {
                    offers_for_use
                        .entry(pu.id.clone())
                        .or_default()
                        .push(po.id.clone());
                    uses_for_offer
                        .entry(po.id.clone())
                        .or_default()
                        .push(pu.id.clone());
                    if pu.in_scope(&po.promiser) {
                        visible_uses_for_offer
                            .entry(po.id.clone())
                            .or_default()
                            .push(pu.id.clone());
                    }
                }
            }
        }

        CompatIndex {
            offers_for_use,
            uses_for_offer,
            visible_uses_for_offer,
        }
    }

    /// Static diagnostic pass checking every condition formula and value-derivation
    /// observation for dangling references, autonomy/promiser mismatches, polarity
    /// mismatches, non-interior superagent references, permanently unsatisfiable
    /// `Assisted`/`Accepted` minimum counts, and incomplete promise information.
    #[must_use]
    pub fn lint(&self) -> Vec<ConditionWarning<A, P>> {
        let compat = self.build_compat_index();
        let mut out = Vec::new();
        for pr in self.promises.values() {
            self.lint_cond(&compat, &pr.id, &pr.promiser, &pr.cond, &mut out);
            self.lint_obs(&pr.id, &pr.promiser, pr.obs(), &mut out);
        }
        for w in self.check_complete_information() {
            out.push(ConditionWarning::IncompleteInformation(w));
        }
        out
    }

    fn lint_cond(
        &self,
        compat: &CompatIndex<P>,
        pid: &P,
        promiser: &A,
        cond: &Cond<P>,
        out: &mut Vec<ConditionWarning<A, P>>,
    ) {
        match cond {
            Cond::SelfPromise(q) => self.lint_self_ref(pid, promiser, q, out),
            Cond::Assisted {
                use_id,
                min_providers,
            } => {
                if self.lint_assisted_ref(pid, promiser, use_id, out) {
                    let max_possible = compat.offers_for_use.get(use_id).map_or(0, Vec::len);
                    if max_possible < *min_providers {
                        out.push(ConditionWarning::UnsatisfiableMinCount {
                            promise: pid.clone(),
                            referenced: use_id.clone(),
                            required: *min_providers,
                            max_possible,
                        });
                    }
                }
            }
            Cond::Accepted {
                offer_id,
                min_acceptors,
            } => {
                if self.lint_accepted_ref(pid, promiser, offer_id, out) {
                    let max_possible = compat
                        .visible_uses_for_offer
                        .get(offer_id)
                        .map_or(0, Vec::len);
                    if max_possible < *min_acceptors {
                        out.push(ConditionWarning::UnsatisfiableMinCount {
                            promise: pid.clone(),
                            referenced: offer_id.clone(),
                            required: *min_acceptors,
                            max_possible,
                        });
                    }
                }
            }
            Cond::Interior(q) => self.lint_interior_ref(pid, promiser, q, out),
            Cond::AtLeast(_, cs) => {
                for c in cs {
                    self.lint_cond(compat, pid, promiser, c, out);
                }
            }
            Cond::Not(c) => self.lint_cond(compat, pid, promiser, c, out),
        }
    }

    fn lint_obs(
        &self,
        pid: &P,
        promiser: &A,
        obs: &[Obs<P>],
        out: &mut Vec<ConditionWarning<A, P>>,
    ) {
        for o in obs {
            match o {
                Obs::SelfPromise(q) => self.lint_self_ref(pid, promiser, q, out),
                Obs::Assisted(use_id) => {
                    let _ = self.lint_assisted_ref(pid, promiser, use_id, out);
                }
                Obs::Accepted(offer_id) => {
                    let _ = self.lint_accepted_ref(pid, promiser, offer_id, out);
                }
                Obs::Interior(q) => self.lint_interior_ref(pid, promiser, q, out),
            }
        }
    }

    fn lint_self_ref(&self, pid: &P, promiser: &A, q: &P, out: &mut Vec<ConditionWarning<A, P>>) {
        match self.promises.get(q) {
            None => out.push(ConditionWarning::DanglingRef {
                promise: pid.clone(),
                referenced: q.clone(),
            }),
            Some(pq) if &pq.promiser != promiser => out.push(ConditionWarning::WrongPromiser {
                promise: pid.clone(),
                referenced: q.clone(),
                expected: promiser.clone(),
                actual: pq.promiser.clone(),
            }),
            Some(_) => {}
        }
    }

    fn lint_assisted_ref(
        &self,
        pid: &P,
        promiser: &A,
        use_id: &P,
        out: &mut Vec<ConditionWarning<A, P>>,
    ) -> bool {
        let Some(pu) = self.promises.get(use_id) else {
            out.push(ConditionWarning::DanglingRef {
                promise: pid.clone(),
                referenced: use_id.clone(),
            });
            return false;
        };
        let promiser_ok = if &pu.promiser == promiser {
            true
        } else {
            out.push(ConditionWarning::WrongPromiser {
                promise: pid.clone(),
                referenced: use_id.clone(),
                expected: promiser.clone(),
                actual: pu.promiser.clone(),
            });
            false
        };
        let polarity_ok = if pu.is_use() {
            true
        } else {
            out.push(ConditionWarning::WrongPolarity {
                promise: pid.clone(),
                referenced: use_id.clone(),
                expected_offer: false,
            });
            false
        };
        promiser_ok && polarity_ok
    }

    fn lint_accepted_ref(
        &self,
        pid: &P,
        promiser: &A,
        offer_id: &P,
        out: &mut Vec<ConditionWarning<A, P>>,
    ) -> bool {
        let Some(po) = self.promises.get(offer_id) else {
            out.push(ConditionWarning::DanglingRef {
                promise: pid.clone(),
                referenced: offer_id.clone(),
            });
            return false;
        };
        let promiser_ok = if &po.promiser == promiser {
            true
        } else {
            out.push(ConditionWarning::WrongPromiser {
                promise: pid.clone(),
                referenced: offer_id.clone(),
                expected: promiser.clone(),
                actual: po.promiser.clone(),
            });
            false
        };
        let polarity_ok = if po.is_offer() {
            true
        } else {
            out.push(ConditionWarning::WrongPolarity {
                promise: pid.clone(),
                referenced: offer_id.clone(),
                expected_offer: true,
            });
            false
        };
        promiser_ok && polarity_ok
    }

    fn lint_interior_ref(
        &self,
        pid: &P,
        promiser: &A,
        q: &P,
        out: &mut Vec<ConditionWarning<A, P>>,
    ) {
        match self.promises.get(q) {
            None => out.push(ConditionWarning::DanglingRef {
                promise: pid.clone(),
                referenced: q.clone(),
            }),
            Some(pq) if !self.hierarchy.is_strict_ancestor(promiser, &pq.promiser) => {
                out.push(ConditionWarning::NonInteriorRef {
                    promise: pid.clone(),
                    referenced: q.clone(),
                    superagent: promiser.clone(),
                    actual_promiser: pq.promiser.clone(),
                });
            }
            Some(_) => {}
        }
    }

    /// Information Completeness check (`arXiv:1505.01716v1` Def. L475, `arXiv:2606.08552v1` L671):
    /// flags any conditional or value-derived promise whose target agent lies outside
    /// the observability scope of one of its surface dependencies (`SelfPromise`,
    /// `Assisted`, or `Accepted`). Interior dependencies of superagents are intentionally
    /// exempt so opaque encapsulation (Law II) is respected.
    #[must_use]
    pub fn check_complete_information(&self) -> Vec<IncompleteInfoWarning<A, P>> {
        fn collect_cond_surface<P: Ord + Clone>(c: &Cond<P>, out: &mut BTreeSet<P>) {
            match c {
                Cond::SelfPromise(q) => {
                    out.insert(q.clone());
                }
                Cond::Assisted { use_id, .. } => {
                    out.insert(use_id.clone());
                }
                Cond::Accepted { offer_id, .. } => {
                    out.insert(offer_id.clone());
                }
                Cond::AtLeast(_, cs) => {
                    for x in cs {
                        collect_cond_surface(x, out);
                    }
                }
                Cond::Not(x) => collect_cond_surface(x, out),
                Cond::Interior(_) => {}
            }
        }

        let mut warnings = Vec::new();
        for pr in self.promises.values() {
            let mut deps = BTreeSet::new();
            collect_cond_surface(&pr.cond, &mut deps);
            for o in pr.obs() {
                match o {
                    Obs::SelfPromise(q) | Obs::Assisted(q) | Obs::Accepted(q) => {
                        deps.insert(q.clone());
                    }
                    Obs::Interior(_) => {}
                }
            }
            for dep_id in deps {
                if let Some(pdep) = self.promises.get(&dep_id) {
                    for a in &self.hierarchy.agents {
                        if pr.target.contains(a) && !pdep.in_scope(a) {
                            warnings.push(IncompleteInfoWarning {
                                conditional_promise: pr.id.clone(),
                                dependency: dep_id.clone(),
                                blind_target: a.clone(),
                            });
                        }
                    }
                }
            }
        }
        warnings
    }
}
