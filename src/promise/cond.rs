//! Autonomy-grounded conditional promise formulas (`+b | C`, `-b | C`) and
//! value-derivation observation selectors (`+f(obs) | C`, `-f(obs) | C`).

use alloc::boxed::Box;
use alloc::vec::Vec;

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
    /// Assisted quenching: promiser's own `Use` promise `use_id` is quenched, locally kept,
    /// and bound to at least `min_providers` quenched offers assessed kept by this promiser.
    Assisted {
        /// Identifier of the promiser's own `Use` (`-c`) promise.
        use_id: P,
        /// Minimum number of kept upstream offers required.
        min_providers: usize,
    },
    /// Tenancy / acceptance trigger: promiser's own `Offer` promise `offer_id` is quenched,
    /// locally kept, and accepted by at least `min_acceptors` quenched `Use` promises visible
    /// in scope and assessed kept by this promiser.
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

    /// Assisted quenching requiring at least `1` kept upstream offer matching `use_id`.
    #[must_use]
    pub const fn assisted(use_id: P) -> Self {
        Self::Assisted {
            use_id,
            min_providers: 1,
        }
    }

    /// Assisted quenching requiring at least `min_providers` kept upstream offers matching `use_id`.
    #[must_use]
    pub const fn assisted_quorum(use_id: P, min_providers: usize) -> Self {
        Self::Assisted {
            use_id,
            min_providers,
        }
    }

    /// Tenancy / acceptance trigger requiring at least `1` accepting consumer on `offer_id`.
    #[must_use]
    pub const fn accepted(offer_id: P) -> Self {
        Self::Accepted {
            offer_id,
            min_acceptors: 1,
        }
    }

    /// Tenancy / acceptance trigger requiring at least `min_acceptors` accepting consumers on `offer_id`.
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

/// Autonomy-grounded local observation selector for value-derived promises
/// (`+f(obs) | C` and `-f(obs) | C`, `arXiv:1505.01716v1` §4.1).
///
/// Mirrors the exact four autonomy-grounded atoms of [`Cond`]. Every declared
/// `Obs` entry establishes a strict stratum barrier (`rank(dep) < rank(p)`) and
/// emits a causal `+LeadsTo` edge in Semantic Spacetime γ(3,4), guaranteeing
/// all four universal Lean 4 laws hold for value-computed promise bodies.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Obs<P> {
    /// Observe the resolved body of another promise `q` by the *same* promiser.
    SelfPromise(P),
    /// Observe all kept offers and overlaps bound to promiser's own `Use` promise `use_id`.
    Assisted(P),
    /// Observe all visible kept acceptances and overlaps bound to promiser's own `Offer` promise `offer_id`.
    Accepted(P),
    /// Observe the resolved body of promise `q` made by a strict interior sub-agent.
    Interior(P),
}

impl<P> Obs<P> {
    /// Observes the resolved body of another promise `q` by the same promiser.
    #[must_use]
    pub const fn self_promise(q: P) -> Self {
        Self::SelfPromise(q)
    }

    /// Observes kept upstream offers and overlaps bound to promiser's own `Use` promise.
    #[must_use]
    pub const fn assisted(use_id: P) -> Self {
        Self::Assisted(use_id)
    }

    /// Observes visible kept acceptances and overlaps bound to promiser's own `Offer` promise.
    #[must_use]
    pub const fn accepted(offer_id: P) -> Self {
        Self::Accepted(offer_id)
    }

    /// Observes the resolved body of strict interior sub-agent promise `q`.
    #[must_use]
    pub const fn interior(q: P) -> Self {
        Self::Interior(q)
    }
}
