//! Pure Promise Theory algebra: offers, acceptances, mutual-information overlap,
//! boolean and value-dependent conditional quenching (`+f(obs) | C`), observer-local
//! assessments, and dressed superagents.
//!
//! Derived directly from Bergstra & Burgess (`arXiv:0810.3294v5`, `1401.3381v1`,
//! `1411.5563`, `1505.01716v1`, `1608.02193`, `2606.08552v1`) and mirrored 1:1
//! by `lean/Baugr/Promise.lean`.

mod cond;
mod hierarchy;
mod resolve;
mod system;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::convert::Infallible;
use core::fmt;
use core::marker::PhantomData;

pub use cond::{Cond, Obs};
pub use hierarchy::HierarchyError;
pub use system::PromiseSystem;

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

/// Optional extension of [`BodyAlgebra`] for value-dependent conditional promises
/// (`+f(obs) | C` and `-f(obs) | C`, `arXiv:1505.01716v1` §4.1).
///
/// Automatically implemented for `R = Infallible` on every [`BodyAlgebra`], so
/// purely static systems need zero extra trait implementations.
pub trait DeriveAlgebra<A, P, R>: BodyAlgebra {
    /// Derives a concrete offer body from frozen local observations, returning
    /// `None` to leave the promise unquenched.
    fn derive_offer(&self, _rule: &R, _obs: &LocalView<'_, A, P, Self>) -> Option<Self::Offer> {
        None
    }

    /// Derives a concrete acceptance/use body from frozen local observations,
    /// returning `None` to leave the promise unquenched.
    fn derive_use(&self, _rule: &R, _obs: &LocalView<'_, A, P, Self>) -> Option<Self::Use> {
        None
    }
}

impl<A, P, D: BodyAlgebra> DeriveAlgebra<A, P, Infallible> for D {}

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

/// Polarity-preserving promise body specification: either a static constant body
/// or a value-derived body computed from declared local [`Obs`] observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodySpec<P, O, U, R = Infallible> {
    /// Static constant offer or acceptance body (`+b` / `-b`).
    Fixed(Body<O, U>),
    /// Value-derived offer body (`+f(obs) | C`).
    DerivedOffer {
        /// Autonomy-grounded local observations read by `rule`.
        obs: Vec<Obs<P>>,
        /// Domain-defined derivation rule value.
        rule: R,
    },
    /// Value-derived acceptance/use body (`-f(obs) | C`).
    DerivedUse {
        /// Autonomy-grounded local observations read by `rule`.
        obs: Vec<Obs<P>>,
        /// Domain-defined derivation rule value.
        rule: R,
    },
}

/// A kept upstream offer observed via [`Obs::Assisted`] inside a [`LocalView`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedOffer<'a, A, P, O, M> {
    /// Identifier of the promiser's `Use` promise that matched this offer.
    pub use_id: &'a P,
    /// Identifier of the matched upstream `Offer` promise.
    pub offer_id: &'a P,
    /// Upstream promiser agent.
    pub promiser: &'a A,
    /// Resolved body of the upstream offer.
    pub offer: &'a O,
    /// Effective mutual-information overlap `offer ∩ use`.
    pub overlap: M,
}

/// A visible kept acceptance observed via [`Obs::Accepted`] inside a [`LocalView`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedUse<'a, A, P, U, M> {
    /// Identifier of the promiser's `Offer` promise that was accepted.
    pub offer_id: &'a P,
    /// Identifier of the accepting `Use` promise.
    pub use_id: &'a P,
    /// Accepting consumer agent.
    pub consumer: &'a A,
    /// Resolved body of the accepting use promise.
    pub use_body: &'a U,
    /// Effective mutual-information overlap `offer ∩ use`.
    pub overlap: M,
}

/// Shorthand for a [`Body`] parameterized by a [`BodyAlgebra`].
pub type AlgebraBody<D> = Body<<D as BodyAlgebra>::Offer, <D as BodyAlgebra>::Use>;

/// Shorthand for a [`Promise`] parameterized by a [`BodyAlgebra`] and derivation rule `R`.
pub type AlgebraPromise<A, P, D, R = Infallible> =
    Promise<A, P, <D as BodyAlgebra>::Offer, <D as BodyAlgebra>::Use, R>;

/// Restricted autonomy-grounded observation snapshot handed to [`DeriveAlgebra`].
///
/// Mirrors `Lean`'s `LocalObs` 1:1: only values explicitly declared in the
/// promise's `obs` list and passing ownership, opaque-wall, scope, and local
/// assessment `α(promiser, _)` checks appear here.
pub struct LocalView<'a, A, P, D: BodyAlgebra + ?Sized> {
    pub(crate) self_bodies: Vec<(&'a P, &'a AlgebraBody<D>)>,
    pub(crate) assisted_offers: Vec<ObservedOffer<'a, A, P, D::Offer, D::Overlap>>,
    pub(crate) accepted_uses: Vec<ObservedUse<'a, A, P, D::Use, D::Overlap>>,
    pub(crate) interior_bodies: Vec<(&'a P, &'a A, &'a AlgebraBody<D>)>,
}

impl<A, P, D> fmt::Debug for LocalView<'_, A, P, D>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra + ?Sized,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
    D::Overlap: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LocalView")
            .field("self_bodies", &self.self_bodies)
            .field("assisted_offers", &self.assisted_offers)
            .field("accepted_uses", &self.accepted_uses)
            .field("interior_bodies", &self.interior_bodies)
            .finish()
    }
}

impl<'a, A, P, D: BodyAlgebra + ?Sized> LocalView<'a, A, P, D> {
    /// All observed self-promise `(id, body)` pairs in declared observation order.
    #[must_use]
    pub fn self_entries(&self) -> &[(&'a P, &'a AlgebraBody<D>)] {
        &self.self_bodies
    }

    /// All observed assisted upstream offers in declared observation order.
    #[must_use]
    pub fn assisted_entries(&self) -> &[ObservedOffer<'a, A, P, D::Offer, D::Overlap>] {
        &self.assisted_offers
    }

    /// All observed visible acceptances in declared observation order.
    #[must_use]
    pub fn accepted_entries(&self) -> &[ObservedUse<'a, A, P, D::Use, D::Overlap>] {
        &self.accepted_uses
    }

    /// All observed interior sub-agent `(promise_id, promiser, body)` triples.
    #[must_use]
    pub fn interior_entries(&self) -> &[(&'a P, &'a A, &'a AlgebraBody<D>)] {
        &self.interior_bodies
    }

    /// Looks up an observed self-promise body by identifier.
    #[must_use]
    pub fn self_body<Q: ?Sized + Eq>(&self, id: &Q) -> Option<&'a AlgebraBody<D>>
    where
        P: Borrow<Q>,
    {
        self.self_bodies
            .iter()
            .find(|(p, _)| (*p).borrow() == id)
            .map(|(_, b)| *b)
    }

    /// Looks up an observed self-offer body by identifier.
    #[must_use]
    pub fn self_offer<Q: ?Sized + Eq>(&self, id: &Q) -> Option<&'a D::Offer>
    where
        P: Borrow<Q>,
    {
        match self.self_body(id) {
            Some(Body::Offer(o)) => Some(o),
            _ => None,
        }
    }

    /// Looks up an observed self-use body by identifier.
    #[must_use]
    pub fn self_use<Q: ?Sized + Eq>(&self, id: &Q) -> Option<&'a D::Use>
    where
        P: Borrow<Q>,
    {
        match self.self_body(id) {
            Some(Body::Use(u)) => Some(u),
            _ => None,
        }
    }

    /// Iterates over kept upstream offers bound to the promiser's `Use` promise `use_id`.
    pub fn assisted<'s, Q: ?Sized + Eq>(
        &'s self,
        use_id: &'s Q,
    ) -> impl Iterator<Item = &'s ObservedOffer<'a, A, P, D::Offer, D::Overlap>> + 's
    where
        P: Borrow<Q>,
    {
        self.assisted_offers
            .iter()
            .filter(move |entry| entry.use_id.borrow() == use_id)
    }

    /// Iterates over visible kept acceptances bound to the promiser's `Offer` promise `offer_id`.
    pub fn accepted<'s, Q: ?Sized + Eq>(
        &'s self,
        offer_id: &'s Q,
    ) -> impl Iterator<Item = &'s ObservedUse<'a, A, P, D::Use, D::Overlap>> + 's
    where
        P: Borrow<Q>,
    {
        self.accepted_uses
            .iter()
            .filter(move |entry| entry.offer_id.borrow() == offer_id)
    }

    /// Looks up an observed interior sub-agent promise `(promiser, body)` by identifier.
    #[must_use]
    pub fn interior_body<Q: ?Sized + Eq>(&self, id: &Q) -> Option<(&'a A, &'a AlgebraBody<D>)>
    where
        P: Borrow<Q>,
    {
        self.interior_bodies
            .iter()
            .find(|(p, _, _)| (*p).borrow() == id)
            .map(|(_, a, b)| (*a, *b))
    }

    /// Looks up an observed interior sub-agent offer `(promiser, offer)` by identifier.
    #[must_use]
    pub fn interior_offer<Q: ?Sized + Eq>(&self, id: &Q) -> Option<(&'a A, &'a D::Offer)>
    where
        P: Borrow<Q>,
    {
        match self.interior_body(id) {
            Some((a, Body::Offer(o))) => Some((a, o)),
            _ => None,
        }
    }
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

/// A directed conditional promise with static or value-derived body.
///
/// Separates promisee `target` from witness observability `scope` (`arXiv:0810.3294v5`
/// L722, `arXiv:1401.3381v1` L663) and supports both constant bodies (`+b | C`) and
/// value-derived bodies (`+f(obs) | C`, `arXiv:1505.01716v1` §4.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Promise<A, P, O, U, R = Infallible> {
    /// Unique identifier of this promise.
    pub id: P,
    /// Autonomous promiser agent.
    pub promiser: A,
    /// Intended promisee(s).
    pub target: AgentSet<A>,
    /// Observability scope `σ` (effective scope always includes `promiser`).
    pub scope: AgentSet<A>,
    /// Polarity and static or value-derived body specification.
    pub spec: BodySpec<P, O, U, R>,
    /// Boolean quenching condition (`Cond::always()` for unconditional promises).
    pub cond: Cond<P>,
}

impl<A: Ord + Clone, P, O, U, R> Promise<A, P, O, U, R> {
    /// Creates a static offer promise (`+b`) whose default scope covers `promiser ∪ target`.
    #[must_use]
    pub fn offer(id: P, promiser: A, target: AgentSet<A>, body: O) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            spec: BodySpec::Fixed(Body::Offer(body)),
            cond: Cond::always(),
        }
    }

    /// Creates a static acceptance/use promise (`-b`) whose default scope covers `promiser ∪ target`.
    #[must_use]
    pub fn accept(id: P, promiser: A, target: AgentSet<A>, body: U) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            spec: BodySpec::Fixed(Body::Use(body)),
            cond: Cond::always(),
        }
    }

    /// Creates a value-derived offer promise (`+f(obs)`) whose effective body is computed
    /// strictly from declared local observations `obs` via `rule`.
    #[must_use]
    pub fn derive_offer(
        id: P,
        promiser: A,
        target: AgentSet<A>,
        obs: Vec<Obs<P>>,
        rule: R,
    ) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            spec: BodySpec::DerivedOffer { obs, rule },
            cond: Cond::always(),
        }
    }

    /// Creates a value-derived acceptance/use promise (`-f(obs)`) whose effective body is
    /// computed strictly from declared local observations `obs` via `rule`.
    #[must_use]
    pub fn derive_use(id: P, promiser: A, target: AgentSet<A>, obs: Vec<Obs<P>>, rule: R) -> Self {
        let scope = default_scope(&promiser, &target);
        Self {
            id,
            promiser,
            target,
            scope,
            spec: BodySpec::DerivedUse { obs, rule },
            cond: Cond::always(),
        }
    }

    /// Attaches a boolean quenching condition (`+b | cond`, `-b | cond`, or `+f(obs) | cond`).
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

    /// Returns `true` if this promise is a positive offer (`+b` or `+f(obs)`).
    #[must_use]
    pub const fn is_offer(&self) -> bool {
        matches!(
            self.spec,
            BodySpec::Fixed(Body::Offer(_)) | BodySpec::DerivedOffer { .. }
        )
    }

    /// Returns `true` if this promise is a negative acceptance/use (`-b` or `-f(obs)`).
    #[must_use]
    pub const fn is_use(&self) -> bool {
        matches!(
            self.spec,
            BodySpec::Fixed(Body::Use(_)) | BodySpec::DerivedUse { .. }
        )
    }

    /// Returns the declared [`Obs`] slice for derived promises (empty for static promises).
    #[must_use]
    pub fn obs(&self) -> &[Obs<P>] {
        match &self.spec {
            BodySpec::Fixed(_) => &[],
            BodySpec::DerivedOffer { obs, .. } | BodySpec::DerivedUse { obs, .. } => obs,
        }
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

/// Error returned when a system's dependency graph contains an unstratifiable cycle
/// (any strongly connected component containing a negated condition edge or value-derivation `Obs` edge).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError<P> {
    /// The strongly connected component contains at least one strict stratum barrier
    /// (`Not` or `Obs`) and therefore admits no canonical stratified fixed point.
    UnstratifiableCycle(BTreeSet<P>),
}

impl<P: fmt::Debug> fmt::Display for EvalError<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnstratifiableCycle(scc) => {
                write!(f, "unstratifiable dependency cycle over {scc:?}")
            }
        }
    }
}

impl<P: fmt::Debug> core::error::Error for EvalError<P> {}

/// Diagnostic warning for incomplete promise information.
///
/// Flagged when a target of a conditional or derived promise lies outside the
/// observability scope of a surface dependency (`SelfPromise`, `Assisted`, or
/// `Accepted`) (`arXiv:1505.01716v1` Def. L475, `arXiv:2606.08552v1` L671).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IncompleteInfoWarning<A, P> {
    /// Conditional or derived promise with incomplete information.
    pub conditional_promise: P,
    /// Surface dependency (`SelfPromise`, `Assisted` use, or `Accepted` offer)
    /// whose observability scope omits `blind_target`.
    pub dependency: P,
    /// Target agent unable to observe `dependency`.
    pub blind_target: A,
}

/// Static diagnostic warning emitted by [`PromiseSystem::lint`] for conditions
/// or observations that are syntactically well-typed yet structurally vacuous,
/// unsatisfiable, or scope-incomplete.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionWarning<A, P> {
    /// Condition or observation references a promise identifier not registered in the system.
    DanglingRef {
        /// Promise containing the reference.
        promise: P,
        /// Missing referenced promise identifier.
        referenced: P,
    },
    /// Local condition/observation (`SelfPromise`, `Assisted`, `Accepted`) references
    /// a promise owned by a different agent (always empty/false by autonomy).
    WrongPromiser {
        /// Promise containing the reference.
        promise: P,
        /// Referenced promise identifier.
        referenced: P,
        /// Promiser of `promise`.
        expected: A,
        /// Actual promiser of `referenced`.
        actual: A,
    },
    /// `Assisted` references an `Offer` (expected `Use`), or `Accepted` references
    /// a `Use` (expected `Offer`).
    WrongPolarity {
        /// Promise containing the reference.
        promise: P,
        /// Referenced promise identifier.
        referenced: P,
        /// `true` if an `Offer` was expected (`Accepted`); `false` if a `Use` was expected (`Assisted`).
        expected_offer: bool,
    },
    /// `Interior` references a promise whose promiser is not strictly contained
    /// inside this superagent.
    NonInteriorRef {
        /// Superagent promise containing the `Interior` reference.
        promise: P,
        /// Referenced promise identifier.
        referenced: P,
        /// Superagent promiser.
        superagent: A,
        /// Actual promiser of `referenced`.
        actual_promiser: A,
    },
    /// `Assisted` or `Accepted` requires more partners than can statically bind
    /// (permanently null-potent in Bergstra–Burgess Promise Theory).
    UnsatisfiableMinCount {
        /// Promise containing the unsatisfiable bound.
        promise: P,
        /// Referenced `Use` (for `Assisted`) or `Offer` (for `Accepted`).
        referenced: P,
        /// Minimum number of providers/acceptors required.
        required: usize,
        /// Maximum number of statically bindable partners in the system.
        max_possible: usize,
    },
    /// Incomplete promise information: a target cannot observe a surface dependency.
    IncompleteInformation(IncompleteInfoWarning<A, P>),
}

/// Result of resolving a [`PromiseSystem`] under an observer-local assessment `α(a, π)`.
pub struct Resolved<A, P, D: BodyAlgebra> {
    /// Effective resolved body of every quenched promise (`State : P -> Option<Body<O, U>>`).
    pub bodies: BTreeMap<P, Body<D::Offer, D::Use>>,
    /// Active bindings between quenched offers and quenched uses assessed kept by consumers.
    pub bindings: Vec<Binding<A, P, D::Overlap>>,
    /// Assigned stratification rank per promise.
    pub strata: BTreeMap<P, usize>,
}

impl<A, P, D> Clone for Resolved<A, P, D>
where
    A: Clone,
    P: Clone,
    D: BodyAlgebra,
    D::Offer: Clone,
    D::Use: Clone,
    D::Overlap: Clone,
{
    fn clone(&self) -> Self {
        Self {
            bodies: self.bodies.clone(),
            bindings: self.bindings.clone(),
            strata: self.strata.clone(),
        }
    }
}

impl<A, P, D> fmt::Debug for Resolved<A, P, D>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
    D::Overlap: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Resolved")
            .field("bodies", &self.bodies)
            .field("bindings", &self.bindings)
            .field("strata", &self.strata)
            .finish()
    }
}

impl<A, P, D> PartialEq for Resolved<A, P, D>
where
    A: PartialEq,
    P: PartialEq,
    D: BodyAlgebra,
    D::Offer: PartialEq,
    D::Use: PartialEq,
    D::Overlap: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.bodies == other.bodies
            && self.bindings == other.bindings
            && self.strata == other.strata
    }
}

impl<A, P, D> Eq for Resolved<A, P, D>
where
    A: Eq,
    P: Eq,
    D: BodyAlgebra,
    D::Offer: Eq,
    D::Use: Eq,
    D::Overlap: Eq,
{
}

impl<A, P: Ord, D: BodyAlgebra> Resolved<A, P, D> {
    /// Returns `true` if promise `id` quenched (is active with a resolved body).
    #[must_use]
    pub fn is_quenched<Q: ?Sized + Ord>(&self, id: &Q) -> bool
    where
        P: Borrow<Q>,
    {
        self.bodies.contains_key(id)
    }

    /// Returns the number of quenched promises.
    #[must_use]
    pub fn quenched_count(&self) -> usize {
        self.bodies.len()
    }

    /// Iterates over the identifiers of all quenched promises in ascending order.
    pub fn quenched_ids(&self) -> impl Iterator<Item = &P> {
        self.bodies.keys()
    }

    /// Returns the resolved offer body of quenched offer `id`, if active.
    #[must_use]
    pub fn offer<Q: ?Sized + Ord>(&self, id: &Q) -> Option<&D::Offer>
    where
        P: Borrow<Q>,
    {
        match self.bodies.get(id) {
            Some(Body::Offer(o)) => Some(o),
            _ => None,
        }
    }

    /// Returns the resolved acceptance/use body of quenched use `id`, if active.
    #[must_use]
    pub fn use_body<Q: ?Sized + Ord>(&self, id: &Q) -> Option<&D::Use>
    where
        P: Borrow<Q>,
    {
        match self.bodies.get(id) {
            Some(Body::Use(u)) => Some(u),
            _ => None,
        }
    }
}

/// Indexed collection of typed promises parameterized by a [`BodyAlgebra`] and derivation rule `R`.
pub type PromiseMap<A, P, D, R = Infallible> =
    BTreeMap<P, Promise<A, P, <D as BodyAlgebra>::Offer, <D as BodyAlgebra>::Use, R>>;
