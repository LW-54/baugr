//! Generalized monoidal Promise Valency (`+b#n`), grouped cross-offer budgets,
//! and open composable [`ScopeLaw`] algebra.
//!
//! Directly derived from `arXiv:1505.01716v1` §2.7 (`Valency`) and `arXiv:1411.5563`
//! L2575 (coordination `C(b)`).
//!
//! # Example
//! ```
//! use baugr::{AgentSet, Promise, PromiseSystem, ResolutionView, SymmetricMeet};
//!
//! let mut sys = PromiseSystem::new(SymmetricMeet::new(|o: &u32, u: &u32| (*u <= *o).then_some(*u)));
//! sys.add_promise(Promise::offer("psu", "mains", AgentSet::All, 100));
//! sys.add_promise(Promise::accept("load1", "a", AgentSet::single("mains"), 60));
//! sys.add_promise(Promise::accept("load2", "b", AgentSet::single("mains"), 50));
//!
//! let resolved = sys.resolve_optimistic().unwrap();
//! let view = ResolutionView::new(&sys, &resolved);
//!
//! // 60 + 50 = 110 > 100 triggers a typed ValencyDeficit (zero type annotations needed!).
//! let deficit = view.check_valency("psu", 100_u32, |b| b.overlap).unwrap_err();
//! assert_eq!(deficit.used, 110);
//!
//! // Grouped per-agent budget, pairwise disjointness & agreement infer closure types directly:
//! let bdef = view.check_budget(|_, b| Some((b.promiser, b.overlap)), |_| 100_u32).unwrap_err();
//! assert_eq!(bdef.used, 110);
//! assert!(view.check_disjoint(|_, b| Some(b.consumer)).is_ok());
//! assert!(view.check_agreement(|_, b| Some(((), b.promiser))).is_ok());
//! ```

mod monoid;
mod standard;

use core::convert::Infallible;
use core::fmt;

use crate::promise::{Binding, BodyAlgebra, PromiseSystem, Resolved};

pub use monoid::{MaxOne, ResourceMonoid, Unbounded};
pub use standard::{
    AgreementBy, AgreementConflict, BudgetBy, BudgetDeficit, DisjointBy, DisjointViolation,
    ProviderCardinalityError, QuorumLaw, QuorumShortfall, UniqueProviderLaw, ValencyDeficit,
    ValencyLaw,
};

/// Read-only view combining a [`PromiseSystem`] with its [`Resolved`] fixed point.
pub struct ResolutionView<'a, A, P, D: BodyAlgebra, Rule = Infallible> {
    /// Underlying promise system (agents, superagent hierarchy, promises).
    pub system: &'a PromiseSystem<A, P, D, Rule>,
    /// Resolved fixed-point output (resolved bodies, active bindings, strata).
    pub resolved: &'a Resolved<A, P, D>,
}

impl<A, P, D, Rule> fmt::Debug for ResolutionView<'_, A, P, D, Rule>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra + fmt::Debug,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
    D::Overlap: fmt::Debug,
    Rule: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ResolutionView")
            .field("system", &self.system)
            .field("resolved", &self.resolved)
            .finish()
    }
}

impl<'a, A, P, D: BodyAlgebra, Rule> ResolutionView<'a, A, P, D, Rule> {
    /// Constructs a [`ResolutionView`].
    #[must_use]
    pub const fn new(
        system: &'a PromiseSystem<A, P, D, Rule>,
        resolved: &'a Resolved<A, P, D>,
    ) -> Self {
        Self { system, resolved }
    }

    /// Evaluates any [`ScopeLaw`] against this resolved view.
    ///
    /// # Errors
    /// Propagates the typed law violation `L::Error`.
    pub fn check<L: ScopeLaw<A, P, D, Rule>>(&self, law: &L) -> Result<(), L::Error> {
        law.check(self)
    }

    /// Ergonomic zero-annotation shorthand for [`ValencyLaw`].
    ///
    /// # Errors
    /// Returns [`ValencyDeficit`] if aggregate demand on `offer_id` exceeds `capacity`.
    pub fn check_valency<R, F>(
        &self,
        offer_id: P,
        capacity: R,
        weight: F,
    ) -> Result<(), ValencyDeficit<P, R>>
    where
        P: Eq + Clone,
        R: ResourceMonoid,
        F: Fn(&Binding<A, P, D::Overlap>) -> R,
    {
        self.check(&ValencyLaw {
            offer_id,
            capacity,
            weight,
        })
    }

    /// Ergonomic zero-annotation shorthand for grouped cross-offer [`BudgetBy`].
    ///
    /// # Errors
    /// Returns [`BudgetDeficit`] if aggregate demand for any group exceeds `capacity(&group)`.
    pub fn check_budget<G, R, F, C>(
        &self,
        extract: F,
        capacity: C,
    ) -> Result<(), BudgetDeficit<G, R>>
    where
        G: Ord + Clone,
        R: ResourceMonoid,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, R)>,
        C: Fn(&G) -> R,
    {
        self.check(&BudgetBy::new(extract, capacity))
    }

    /// Ergonomic zero-annotation shorthand for [`DisjointBy`].
    ///
    /// # Errors
    /// Returns [`DisjointViolation`] if two bindings extract the same key.
    pub fn check_disjoint<K, F>(&self, key: F) -> Result<(), DisjointViolation<K, P>>
    where
        P: Clone,
        K: Ord + Clone,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<K>,
    {
        self.check(&DisjointBy::new(key))
    }

    /// Ergonomic zero-annotation shorthand for [`AgreementBy`] (`C(b)`).
    ///
    /// # Errors
    /// Returns [`AgreementConflict`] if two bindings in the same group disagree on a value.
    pub fn check_agreement<G, V, F>(&self, extract: F) -> Result<(), AgreementConflict<G, V, P>>
    where
        P: Clone,
        G: Ord + Clone,
        V: Eq + Clone,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, V)>,
    {
        self.check(&AgreementBy::new(extract))
    }
}

/// Open composable verification law over a resolved [`PromiseSystem`] (`ADR-0018`).
///
/// Users can implement arbitrary collective constraints (quorums, disjointness,
/// consensus agreement, multi-dimensional budgets, latency bounds) without
/// modifying `baugr`'s kernel.
pub trait ScopeLaw<A, P, D: BodyAlgebra, Rule = Infallible> {
    /// Typed violation returned when this law fails.
    type Error;

    /// Verifies this law against `view`.
    ///
    /// # Errors
    /// Returns `Self::Error` describing the exact violation.
    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error>;
}
