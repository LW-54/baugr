//! Generalized monoidal Promise Valency (`+b#n`) and open composable [`ScopeLaw`] algebra.
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
//! // Pairwise disjointness & grouped agreement infer closure types directly:
//! assert!(view.check_disjoint(|_, b| Some(b.consumer)).is_ok());
//! assert!(view.check_agreement(|_, b| Some(((), b.promiser))).is_ok());
//! ```

mod monoid;
mod standard;

use core::fmt;

use crate::promise::{Binding, BodyAlgebra, PromiseSystem, Resolved};

pub use monoid::{MaxOne, ResourceMonoid, Unbounded};
pub use standard::{
    AgreementBy, AgreementConflict, DisjointBy, DisjointViolation, ProviderCardinalityError,
    QuorumLaw, QuorumShortfall, UniqueProviderLaw, ValencyDeficit, ValencyLaw,
};

/// Read-only view combining a [`PromiseSystem`] with its [`Resolved`] fixed point.
pub struct ResolutionView<'a, A, P, D: BodyAlgebra> {
    /// Underlying promise system (agents, superagent hierarchy, promises).
    pub system: &'a PromiseSystem<A, P, D>,
    /// Resolved fixed-point output (quenched promises, active bindings, strata).
    pub resolved: &'a Resolved<A, P, D::Overlap>,
}

impl<A, P, D> fmt::Debug for ResolutionView<'_, A, P, D>
where
    A: fmt::Debug,
    P: fmt::Debug,
    D: BodyAlgebra + fmt::Debug,
    D::Offer: fmt::Debug,
    D::Use: fmt::Debug,
    D::Overlap: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ResolutionView")
            .field("system", &self.system)
            .field("resolved", &self.resolved)
            .finish()
    }
}

impl<'a, A, P, D: BodyAlgebra> ResolutionView<'a, A, P, D> {
    /// Constructs a [`ResolutionView`].
    #[must_use]
    pub const fn new(
        system: &'a PromiseSystem<A, P, D>,
        resolved: &'a Resolved<A, P, D::Overlap>,
    ) -> Self {
        Self { system, resolved }
    }

    /// Evaluates any [`ScopeLaw`] against this resolved view.
    ///
    /// # Errors
    /// Propagates the typed law violation `L::Error`.
    pub fn check<L: ScopeLaw<A, P, D>>(&self, law: &L) -> Result<(), L::Error> {
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

    /// Ergonomic zero-annotation shorthand for [`DisjointBy`].
    ///
    /// # Errors
    /// Returns [`DisjointViolation`] if two bindings extract the same key.
    pub fn check_disjoint<K, F>(&self, key: F) -> Result<(), DisjointViolation<K, P>>
    where
        P: Clone,
        K: Ord + Clone,
        F: Fn(&PromiseSystem<A, P, D>, &Binding<A, P, D::Overlap>) -> Option<K>,
    {
        self.check(&DisjointBy::new(key))
    }

    /// Ergonomic zero-annotation shorthand for [`AgreementBy`] (`C(b)`).
    ///
    /// # Errors
    /// Returns [`AgreementConflict`] if two bindings in the same group disagree.
    pub fn check_agreement<G, V, F>(&self, extract: F) -> Result<(), AgreementConflict<G, V, P>>
    where
        P: Clone,
        G: Ord + Clone,
        V: Eq + Clone,
        F: Fn(&PromiseSystem<A, P, D>, &Binding<A, P, D::Overlap>) -> Option<(G, V)>,
    {
        self.check(&AgreementBy::new(extract))
    }
}

/// Open composable verification law over a [`ResolutionView`].
pub trait ScopeLaw<A, P, D: BodyAlgebra> {
    /// Typed violation error returned when the law fails.
    type Error;

    /// Verifies that `view` satisfies this law.
    ///
    /// # Errors
    /// Returns `Err(Self::Error)` describing the counterexample when violated.
    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error>;
}
