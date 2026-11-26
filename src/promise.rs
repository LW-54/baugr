//! Pure Promise Theory algebra: offers, acceptances, mutual-information overlap,
//! conditional quenching, observer-local assessments, and dressed superagents.
//!
//! Derived directly from Bergstra & Burgess (`arXiv:0810.3294v5`, `1401.3381v1`,
//! `1411.5563`, `1505.01716v1`, `1608.02193`, `2606.08552v1`) and mirrored 1:1
//! by `lean/Baugr/Promise.lean`.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

/// Mutual-information pairing between an offered promise body (`+b`) and an
/// accepted/used demand body (`-b`) (`arXiv:1411.5563` L2289, `arXiv:2606.08552v1` L616).
///
/// Returning `Some(m)` signifies non-empty overlap `b₁ ∩ b₂ = m`; returning
/// `None` signifies incompatibility.
pub trait BodyAlgebra {
    /// Body type of an offer promise (`+b`).
    type Offer;
    /// Body type of an acceptance/use promise (`-b`).
    type Use;
    /// Effective bound overlap `b₁ ∩ b₂` (use `()` for pure boolean compatibility).
    type Overlap;

    /// Computes the effective overlap `b₁ ∩ b₂` when `use_` accepts `offer`.
    fn overlap(&self, offer: &Self::Offer, use_: &Self::Use) -> Option<Self::Overlap>;
}

/// Convenience [`BodyAlgebra`] wrapper for symmetric meet-semilattice bodies
/// where `Offer = Use = Overlap = B` (exact Burgess `+b / -b` notation).
pub struct SymmetricMeet<B, F> {
    meet: F,
    _body: PhantomData<fn(&B, &B) -> Option<B>>,
}

impl<B, F> SymmetricMeet<B, F> {
    /// Wraps a symmetric meet function `(&B, &B) -> Option<B>` as a [`BodyAlgebra`].
    #[must_use]
    pub const fn new(meet: F) -> Self {
        Self {
            meet,
            _body: PhantomData,
        }
    }
}

impl<B, F: Clone> Clone for SymmetricMeet<B, F> {
    fn clone(&self) -> Self {
        Self {
            meet: self.meet.clone(),
            _body: PhantomData,
        }
    }
}

impl<B, F: Copy> Copy for SymmetricMeet<B, F> {}

impl<B, F: fmt::Debug> fmt::Debug for SymmetricMeet<B, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SymmetricMeet").field(&self.meet).finish()
    }
}

impl<B, F> BodyAlgebra for SymmetricMeet<B, F>
where
    F: Fn(&B, &B) -> Option<B>,
{
    type Offer = B;
    type Use = B;
    type Overlap = B;

    fn overlap(&self, offer: &B, use_: &B) -> Option<B> {
        (self.meet)(offer, use_)
    }
}

/// Unified polarity and typed body (ratified in `ADR-0018` A1).
///
/// Illegal polarity/body mismatches are structurally unrepresentable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Body<O, U> {
    /// `+b`: offer / assertion promise made by the promiser.
    Offer(O),
    /// `-b`: acceptance / use promise made by the consumer.
    Use(U),
}

/// Set of agents used for promisee targeting (`target`) and witness visibility (`scope`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentSet<A> {
    /// All agents in the system (`*` / universal scope in Burgess's notation).
    All,
    /// Explicit finite set of agents.
    Set(BTreeSet<A>),
}

impl<A: Ord> AgentSet<A> {
    /// Returns `true` if agent `a` belongs to this set.
    #[must_use]
    pub fn contains(&self, a: &A) -> bool {
        match self {
            Self::All => true,
            Self::Set(s) => s.contains(a),
        }
    }

    /// Constructs a singleton agent set `{a}`.
    #[must_use]
    pub fn single(a: A) -> Self {
        let mut s = BTreeSet::new();
        s.insert(a);
        Self::Set(s)
    }

    /// Constructs an agent set from any iterator.
    #[must_use]
    pub fn of<I: IntoIterator<Item = A>>(iter: I) -> Self {
        Self::Set(iter.into_iter().collect())
    }

    /// Constructs the empty agent set.
    #[must_use]
    pub const fn empty() -> Self {
        Self::Set(BTreeSet::new())
    }
}

/// Condition formula on a promise (`+b | C` or `-b | C`).
///
/// Every atomic condition is structurally grounded in the promiser's own autonomy
/// (no agent may condition directly on an arbitrary unaccepted remote agent):
/// - [`Cond::SelfPromise`][]: self-quenching (`arXiv:2606.08552v1` L689)
/// - [`Cond::Assisted`][]: assisted quenching via own `Use` (`arXiv:1411.5563` L2325)
/// - [`Cond::Accepted`][]: tenancy trigger via own `Offer` (`arXiv:1505.01716v1` L3024)
/// - [`Cond::Interior`][]: irreducible superagent emergence (`arXiv:1505.01716v1` Lemma L1975)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond<P> {
    /// Self-quenching: another promise `q` by the *same* promiser is quenched and locally kept.
    SelfPromise(P),
    /// Assisted quenching: promiser's own `Use` promise `use_id` is bound to at least
    /// `min_providers` quenched offers assessed as kept by this promiser.
    Assisted {
        /// Identifier of the promiser's own `Use` (`-c`) promise.
        use_id: P,
        /// Minimum number of kept upstream offers required.
        min_providers: usize,
    },
    /// Tenancy / acceptance trigger: promiser's own `Offer` promise `offer_id` is accepted
    /// by at least `min_acceptors` quenched `Use` promises visible in scope and assessed kept.
    Accepted {
        /// Identifier of the promiser's own `Offer` (`+R`) promise.
        offer_id: P,
        /// Minimum number of accepting consumers required.
        min_acceptors: usize,
    },
    /// Irreducible superagent emergence: promise `q` made by a strict sub-agent contained
    /// inside this superagent is quenched and assessed kept by this superagent.
    Interior(P),
    /// Monotone `k`-of-`n` threshold combinator (subsumes `always`, `all`, `any`, and quorum).
    AtLeast(usize, Vec<Self>),
    /// Stratified negation for failover/fallback semantics (`battery | !grid`).
    Not(Box<Self>),
}

impl<P> Cond<P> {
    /// Unconditional promise (`AtLeast(0, [])`).
    #[must_use]
    pub const fn always() -> Self {
        Self::AtLeast(0, Vec::new())
    }

    /// Self-quenching condition on another promise by the same agent.
    #[must_use]
    pub const fn self_promise(q: P) -> Self {
        Self::SelfPromise(q)
    }

    /// Assisted quenching requiring at least 1 kept upstream provider for `use_id`.
    #[must_use]
    pub const fn assisted(use_id: P) -> Self {
        Self::Assisted {
            use_id,
            min_providers: 1,
        }
    }

    /// Assisted quenching requiring a quorum of `min_providers` kept upstream providers.
    #[must_use]
    pub const fn assisted_quorum(use_id: P, min_providers: usize) -> Self {
        Self::Assisted {
            use_id,
            min_providers,
        }
    }

    /// Tenancy trigger requiring at least 1 accepting consumer for `offer_id`.
    #[must_use]
    pub const fn accepted(offer_id: P) -> Self {
        Self::Accepted {
            offer_id,
            min_acceptors: 1,
        }
    }

    /// Tenancy trigger requiring at least `min_acceptors` accepting consumers for `offer_id`.
    #[must_use]
    pub const fn accepted_at_least(offer_id: P, min_acceptors: usize) -> Self {
        Self::Accepted {
            offer_id,
            min_acceptors,
        }
    }

    /// Irreducible superagent emergence condition referencing interior promise `q`.
    #[must_use]
    pub const fn interior(q: P) -> Self {
        Self::Interior(q)
    }

    /// Logical conjunction of all sub-conditions.
    #[must_use]
    pub const fn all(cs: Vec<Self>) -> Self {
        Self::AtLeast(cs.len(), cs)
    }

    /// Logical disjunction (at least one sub-condition holds).
    #[must_use]
    pub const fn any(cs: Vec<Self>) -> Self {
        Self::AtLeast(1, cs)
    }

    /// Monotone threshold: at least `k` sub-conditions hold.
    #[must_use]
    pub const fn at_least(k: usize, cs: Vec<Self>) -> Self {
        Self::AtLeast(k, cs)
    }
}

impl<P> core::ops::Not for Cond<P> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Not(Box::new(self))
    }
}

/// A directed conditional promise with distinct promisee `target` and witness `scope`
/// (`arXiv:0810.3294v5` L722, `arXiv:1401.3381v1` L663).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Promise<A, P, O, U> {
    /// Unique identifier of this promise.
    pub id: P,
    /// Autonomous promiser agent.
    pub promiser: A,
    /// Intended promisee(s).
    pub target: AgentSet<A>,
    /// Observability scope `σ` (effective scope always includes `promiser`).
    pub scope: AgentSet<A>,
    /// Polarity and typed body (`Offer(O)` or `Use(U)`).
    pub body: Body<O, U>,
    /// Quenching condition (`Cond::always()` for unconditional promises).
    pub cond: Cond<P>,
}

impl<A: Ord + Clone, P, O, U> Promise<A, P, O, U> {
    /// Creates an unconditional offer promise (`+b`) whose default scope covers `promiser ∪ target`.
    #[must_use]
    pub fn offer(id: P, promiser: A, target: AgentSet<A>, body: O) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            body: Body::Offer(body),
            cond: Cond::always(),
        }
    }

    /// Creates an unconditional acceptance/use promise (`-b`) whose default scope covers `promiser ∪ target`.
    #[must_use]
    pub fn accept(id: P, promiser: A, target: AgentSet<A>, body: U) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            body: Body::Use(body),
            cond: Cond::always(),
        }
    }

    /// Attaches a quenching condition (`+b | cond` or `-b | cond`).
    #[must_use]
    pub fn when(mut self, cond: Cond<P>) -> Self {
        self.cond = cond;
        self
    }

    /// Overrides the observability scope `σ` (effective scope always retains `promiser`).
    #[must_use]
    pub fn with_scope(mut self, scope: AgentSet<A>) -> Self {
        self.scope = scope;
        self
    }

    /// Returns `true` if `obs` can observe this promise (`obs ∈ σ ∪ {promiser}`).
    #[must_use]
    pub fn in_scope(&self, obs: &A) -> bool {
        obs == &self.promiser || self.scope.contains(obs)
    }

    /// Returns `true` if this promise is a positive offer (`+b`).
    #[must_use]
    pub const fn is_offer(&self) -> bool {
        matches!(self.body, Body::Offer(_))
    }

    /// Returns `true` if this promise is a negative acceptance/use (`-b`).
    #[must_use]
    pub const fn is_use(&self) -> bool {
        matches!(self.body, Body::Use(_))
    }
}

fn default_scope<A: Ord + Clone>(promiser: &A, target: &AgentSet<A>) -> AgentSet<A> {
    match target {
        AgentSet::All => AgentSet::All,
        AgentSet::Set(s) => {
            let mut sc = s.clone();
            sc.insert(promiser.clone());
            AgentSet::Set(sc)
        }
    }
}

/// An active cooperative binding between a quenched offer and a quenched acceptance
/// with their non-empty mutual-information overlap `b₁ ∩ b₂`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<A, P, M> {
    /// Identifier of the offering (`+`) promise.
    pub offer_id: P,
    /// Identifier of the accepting (`-`) promise.
    pub use_id: P,
    /// Promiser agent offering `+b`.
    pub promiser: A,
    /// Consumer agent accepting `-b`.
    pub consumer: A,
    /// Non-empty mutual-information overlap `b₁ ∩ b₂`.
    pub overlap: M,
}

/// Error returned when a system's conditional dependency graph contains a negative cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError<P> {
    /// The strongly connected component `0` contains at least one negated dependency edge
    /// and therefore admits no canonical stratified fixed point.
    UnstratifiableNegativeCycle(BTreeSet<P>),
}

impl<P: fmt::Debug> fmt::Display for EvalError<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnstratifiableNegativeCycle(scc) => {
                write!(f, "unstratifiable negative dependency cycle over {scc:?}")
            }
        }
    }
}

/// Diagnostic warning for incomplete promise information.
///
/// Flagged when a target of a conditional promise lies outside the observability
/// scope of the promiser's assisting `Use` promise (`arXiv:1505.01716v1` Def. L475,
/// `arXiv:2606.08552v1` L671).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IncompleteInfoWarning<A, P> {
    /// Conditional promise with incomplete information.
    pub conditional_promise: P,
    /// Assisting `Use` (`-c`) promise whose scope omits `blind_target`.
    pub assisting_use: P,
    /// Target agent unable to observe the assisting acceptance.
    pub blind_target: A,
}

/// Result of resolving a [`PromiseSystem`] under an observer-local assessment `α(a, π)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolved<A, P, M> {
    /// Set of promises quenched (active) in the canonical stratified fixed point.
    pub quenched: BTreeSet<P>,
    /// Active bindings between quenched offers and quenched uses assessed kept by consumers.
    pub bindings: Vec<Binding<A, P, M>>,
    /// Assigned stratification rank per promise.
    pub strata: BTreeMap<P, usize>,
}

/// Indexed collection of typed promises parameterized by a [`BodyAlgebra`].
pub type PromiseMap<A, P, D> =
    BTreeMap<P, Promise<A, P, <D as BodyAlgebra>::Offer, <D as BodyAlgebra>::Use>>;

/// Complete autonomous agent & conditional promise system.
pub struct PromiseSystem<A, P, D: BodyAlgebra> {
    agents: BTreeSet<A>,
    parent: BTreeMap<A, A>,
    opaque_superagents: BTreeSet<A>,
    promises: PromiseMap<A, P, D>,
    algebra: D,
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
            agents: self.agents.clone(),
            parent: self.parent.clone(),
            opaque_superagents: self.opaque_superagents.clone(),
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
            .field("agents", &self.agents)
            .field("parent", &self.parent)
            .field("opaque_superagents", &self.opaque_superagents)
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
            agents: BTreeSet::new(),
            parent: BTreeMap::new(),
            opaque_superagents: BTreeSet::new(),
            promises: BTreeMap::new(),
            algebra,
        }
    }

    /// Registers an autonomous agent.
    pub fn add_agent(&mut self, agent: A) {
        self.agents.insert(agent);
    }

    /// Registers a dressed superagent with explicit `opaque` boundary control
    /// (`arXiv:1505.01716v1` §3.7).
    pub fn add_superagent(&mut self, superagent: A, opaque: bool) {
        self.agents.insert(superagent.clone());
        if opaque {
            self.opaque_superagents.insert(superagent);
        } else {
            self.opaque_superagents.remove(&superagent);
        }
    }

    /// Places `child` inside `superagent` (`superagent +Contains child`).
    pub fn contain(&mut self, superagent: A, child: A) {
        self.agents.insert(superagent.clone());
        self.agents.insert(child.clone());
        self.parent.insert(child, superagent);
    }

    /// Inserts a promise into the system (also registering its promiser).
    pub fn add_promise(&mut self, promise: Promise<A, P, D::Offer, D::Use>) {
        self.agents.insert(promise.promiser.clone());
        self.promises.insert(promise.id.clone(), promise);
    }

    /// Returns all registered agents.
    #[must_use]
    pub const fn agents(&self) -> &BTreeSet<A> {
        &self.agents
    }

    /// Returns the superagent containment parent map (`child -> superagent`).
    #[must_use]
    pub const fn parents(&self) -> &BTreeMap<A, A> {
        &self.parent
    }

    /// Returns the set of opaque superagents.
    #[must_use]
    pub const fn opaque_superagents(&self) -> &BTreeSet<A> {
        &self.opaque_superagents
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
        let mut cur = node;
        for _ in 0..self.agents.len() {
            match self.parent.get(cur) {
                Some(p) if p == ancestor => return true,
                Some(p) => cur = p,
                None => return false,
            }
        }
        false
    }

    /// Returns `superagent` together with all strict descendants contained within it.
    #[must_use]
    pub fn members_of(&self, superagent: &A) -> BTreeSet<A> {
        let mut out = BTreeSet::new();
        if self.agents.contains(superagent) {
            out.insert(superagent.clone());
        }
        for a in &self.agents {
            if self.is_strict_ancestor(superagent, a) {
                out.insert(a.clone());
            }
        }
        out
    }

    pub(crate) fn no_opaque_wall(&self, a: &A, b: &A) -> bool {
        for s in &self.opaque_superagents {
            let a_strict = self.is_strict_ancestor(s, a);
            let b_strict = self.is_strict_ancestor(s, b);
            let a_in = a == s || a_strict;
            let b_in = b == s || b_strict;
            if (a_strict && !b_in) || (b_strict && !a_in) {
                return false;
            }
        }
        true
    }

    pub(crate) fn static_overlap(
        &self,
        po: &Promise<A, P, D::Offer, D::Use>,
        pu: &Promise<A, P, D::Offer, D::Use>,
    ) -> Option<D::Overlap> {
        let (Body::Offer(ob), Body::Use(ub)) = (&po.body, &pu.body) else {
            return None;
        };
        if !po.target.contains(&pu.promiser)
            || !po.in_scope(&pu.promiser)
            || !pu.target.contains(&po.promiser)
            || !self.no_opaque_wall(&po.promiser, &pu.promiser)
        {
            return None;
        }
        self.algebra.overlap(ob, ub)
    }

    pub(crate) fn cond_deps(&self, neg: bool, cond: &Cond<P>, out: &mut Vec<(P, bool)>) {
        match cond {
            Cond::SelfPromise(q) | Cond::Interior(q) => out.push((q.clone(), neg)),
            Cond::Assisted { use_id, .. } => {
                out.push((use_id.clone(), neg));
                if let Some(pu) = self.promises.get(use_id) {
                    for po in self.promises.values() {
                        if self.static_overlap(po, pu).is_some() {
                            out.push((po.id.clone(), neg));
                        }
                    }
                }
            }
            Cond::Accepted { offer_id, .. } => {
                out.push((offer_id.clone(), neg));
                if let Some(po) = self.promises.get(offer_id) {
                    for pu in self.promises.values() {
                        if self.static_overlap(po, pu).is_some() && pu.in_scope(&po.promiser) {
                            out.push((pu.id.clone(), neg));
                        }
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

    /// Computes a minimal valid stratification rank per promise via Kosaraju SCC decomposition.
    ///
    /// Positive dependencies satisfy `rank(dep) <= rank(p)`; negated dependencies satisfy
    /// `rank(dep) < rank(p)`.
    ///
    /// # Errors
    /// Returns [`EvalError::UnstratifiableNegativeCycle`] if any strongly connected component
    /// contains a negated dependency edge.
    pub fn stratify(&self) -> Result<BTreeMap<P, usize>, EvalError<P>> {
        let mut deps: BTreeMap<P, Vec<(P, bool)>> = BTreeMap::new();
        for (pid, pr) in &self.promises {
            let mut d = Vec::new();
            self.cond_deps(false, &pr.cond, &mut d);
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

    fn eval_cond<F>(&self, alpha: &F, qset: &BTreeSet<P>, me: &A, cond: &Cond<P>) -> bool
    where
        F: Fn(&A, &P) -> bool,
    {
        match cond {
            Cond::SelfPromise(q) => self
                .promises
                .get(q)
                .is_some_and(|pq| &pq.promiser == me && qset.contains(q) && alpha(me, q)),
            Cond::Interior(q) => self.promises.get(q).is_some_and(|pq| {
                self.is_strict_ancestor(me, &pq.promiser) && qset.contains(q) && alpha(me, q)
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
                let n = self
                    .promises
                    .values()
                    .filter(|po| {
                        self.static_overlap(po, pu).is_some()
                            && qset.contains(&po.id)
                            && alpha(me, &po.id)
                    })
                    .count();
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
                let n = self
                    .promises
                    .values()
                    .filter(|pu| {
                        self.static_overlap(po, pu).is_some()
                            && pu.in_scope(me)
                            && qset.contains(&pu.id)
                            && alpha(me, &pu.id)
                    })
                    .count();
                n >= *min_acceptors
            }
            Cond::AtLeast(k, cs) => {
                cs.iter()
                    .filter(|c| self.eval_cond(alpha, qset, me, c))
                    .count()
                    >= *k
            }
            Cond::Not(c) => !self.eval_cond(alpha, qset, me, c),
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
        let strata = self.stratify()?;
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
                        if self.eval_cond(&alpha, &quenched, &pr.promiser, &pr.cond) {
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
            if !po.is_offer() || !quenched.contains(&po.id) {
                continue;
            }
            for pu in self.promises.values() {
                if !pu.is_use() || !quenched.contains(&pu.id) {
                    continue;
                }
                if let Some(ov) = self.static_overlap(po, pu)
                    && alpha(&pu.promiser, &po.id)
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
                    for a in &self.agents {
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

fn dfs_postorder<P: Ord + Clone>(
    start: &P,
    adj: &BTreeMap<P, BTreeSet<P>>,
    visited: &mut BTreeSet<P>,
    order: &mut Vec<P>,
) {
    if !visited.insert(start.clone()) {
        return;
    }
    // Iterative DFS to avoid stack overflow on deep dependency chains.
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
