//! Pure Promise Theory algebra: offers, acceptances, mutual-information overlap,
//! conditional quenching, observer-local assessments, and dressed superagents.
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
use core::fmt;
use core::marker::PhantomData;

pub use cond::Cond;
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
    /// The strongly connected component contains at least one negated dependency edge
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

impl<P: fmt::Debug> core::error::Error for EvalError<P> {}

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

/// Static diagnostic warning emitted by [`PromiseSystem::lint`] for conditions
/// that are syntactically well-typed yet structurally vacuous or scope-incomplete.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionWarning<A, P> {
    /// Condition references a promise identifier not registered in the system.
    DanglingRef {
        /// Promise containing the condition.
        promise: P,
        /// Missing referenced promise identifier.
        referenced: P,
    },
    /// Local condition (`SelfPromise`, `Assisted`, `Accepted`) references a promise
    /// owned by a different agent (always evaluates `false` by autonomy).
    WrongPromiser {
        /// Promise containing the condition.
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
        /// Promise containing the condition.
        promise: P,
        /// Referenced promise identifier.
        referenced: P,
        /// `true` if an `Offer` was expected (`Accepted`); `false` if a `Use` was expected (`Assisted`).
        expected_offer: bool,
    },
    /// `Interior` references a promise whose promiser is not strictly contained
    /// inside this superagent.
    NonInteriorRef {
        /// Superagent promise containing the `Interior` condition.
        promise: P,
        /// Referenced promise identifier.
        referenced: P,
        /// Superagent promiser.
        superagent: A,
        /// Actual promiser of `referenced`.
        actual_promiser: A,
    },
    /// Incomplete promise information: a target cannot observe an assisting `Use`.
    IncompleteInformation(IncompleteInfoWarning<A, P>),
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
