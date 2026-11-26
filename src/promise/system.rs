//! [`PromiseSystem`] builder, precomputed static compatibility index,
//! dependency extraction, and complete-information diagnostics.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::fmt;

use super::cond::Cond;
use super::hierarchy::{Hierarchy, HierarchyError};
use super::{Body, BodyAlgebra, IncompleteInfoWarning, Promise, PromiseMap};

/// Precomputed static offer↔use compatibility index for a [`PromiseSystem`].
///
/// Built once per `stratify()`, `resolve()`, or `project_sst()` call so neither
/// `no_opaque_wall` nor [`BodyAlgebra::overlap`] is recomputed inside fixed-point
/// quenching iterations.
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
}

/// Complete autonomous agent & conditional promise system.
pub struct PromiseSystem<A, P, D: BodyAlgebra> {
    pub(crate) hierarchy: Hierarchy<A>,
    pub(crate) promises: PromiseMap<A, P, D>,
    pub(crate) algebra: D,
}

impl<A, P, D> Clone for PromiseSystem<A, P, D>
where
    A: Clone,
    P: Clone,
    D: BodyAlgebra + Clone,
    D::Offer: Clone,
    D::Use: Clone,
{
    fn clone(&self) -> Self {
        Self {
            hierarchy: self.hierarchy.clone(),
            promises: self.promises.clone(),
            algebra: self.algebra.clone(),
        }
    }
}

impl<A, P, D> fmt::Debug for PromiseSystem<A, P, D>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra + fmt::Debug,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
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

impl<A: Ord + Clone, P: Ord + Clone, D: BodyAlgebra> PromiseSystem<A, P, D> {
    /// Creates an empty promise system parameterized by `algebra`.
    #[must_use]
    pub const fn new(algebra: D) -> Self {
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
    pub fn add_promise(&mut self, promise: Promise<A, P, D::Offer, D::Use>) {
        self.hierarchy.add_agent(promise.promiser.clone());
        self.promises.insert(promise.id.clone(), promise);
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
    pub const fn promises(&self) -> &PromiseMap<A, P, D> {
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

    pub(crate) fn build_compat_index(&self) -> CompatIndex<P> {
        let mut offers_for_use: BTreeMap<P, Vec<P>> = BTreeMap::new();
        let mut uses_for_offer: BTreeMap<P, Vec<P>> = BTreeMap::new();
        let mut visible_uses_for_offer: BTreeMap<P, Vec<P>> = BTreeMap::new();

        for po in self.promises.values() {
            let Body::Offer(ob) = &po.body else {
                continue;
            };
            for pu in self.promises.values() {
                let Body::Use(ub) = &pu.body else {
                    continue;
                };
                if po.target.contains(&pu.promiser)
                    && po.in_scope(&pu.promiser)
                    && pu.target.contains(&po.promiser)
                    && self.hierarchy.no_opaque_wall(&po.promiser, &pu.promiser)
                    && self.algebra.overlap(ob, ub).is_some()
                {
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

    /// Information Completeness check (`arXiv:1505.01716v1` Def. L475, `arXiv:2606.08552v1` L671):
    /// flags any conditional promise whose target agent lies outside the observability scope
    /// of one of its assisting `Use` promises.
    #[must_use]
    pub fn check_complete_information(&self) -> Vec<IncompleteInfoWarning<A, P>> {
        fn collect_assisted<P: Clone>(c: &Cond<P>, out: &mut Vec<P>) {
            match c {
                Cond::Assisted { use_id, .. } => out.push(use_id.clone()),
                Cond::AtLeast(_, cs) => {
                    for x in cs {
                        collect_assisted(x, out);
                    }
                }
                Cond::Not(x) => collect_assisted(x, out),
                Cond::SelfPromise(_) | Cond::Accepted { .. } | Cond::Interior(_) => {}
            }
        }

        let mut warnings = Vec::new();
        for pr in self.promises.values() {
            let mut uses = Vec::new();
            collect_assisted(&pr.cond, &mut uses);
            for u in uses {
                if let Some(pu) = self.promises.get(&u) {
                    for a in &self.hierarchy.agents {
                        if pr.target.contains(a) && !pu.in_scope(a) {
                            warnings.push(IncompleteInfoWarning {
                                conditional_promise: pr.id.clone(),
                                assisting_use: u.clone(),
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
