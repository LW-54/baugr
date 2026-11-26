//! Generalized monoidal Promise Valency (`+b#n`) and open composable [`ScopeLaw`] algebra.
//!
//! Directly derived from `arXiv:1505.01716v1` §2.7 (`Valency`) and `arXiv:1411.5563`
//! L2575 (coordination `C(b)`).
//!
//! # Example
//! ```
//! use baugr::{
//!     AgentSet, Binding, DisjointBy, Promise, PromiseSystem, ResolutionView, SymmetricMeet,
//!     ValencyLaw,
//! };
//!
//! let mut sys = PromiseSystem::new(SymmetricMeet::new(|o: &u32, u: &u32| (*u <= *o).then_some(*u)));
//! sys.add_promise(Promise::offer("psu", "mains", AgentSet::All, 100));
//! sys.add_promise(Promise::accept("load1", "a", AgentSet::single("mains"), 60));
//! sys.add_promise(Promise::accept("load2", "b", AgentSet::single("mains"), 50));
//!
//! let resolved = sys.resolve_optimistic().unwrap();
//! let view = ResolutionView::new(&sys, &resolved);
//!
//! // 60 + 50 = 110 > 100 triggers a typed ValencyDeficit.
//! let deficit = view.check(&ValencyLaw {
//!     offer_id: "psu",
//!     capacity: 100_u32,
//!     weight: |b: &Binding<_, _, u32>| b.overlap,
//! }).unwrap_err();
//! assert_eq!(deficit.used, 110);
//!
//! // DisjointBy checks pairwise uniqueness across arbitrary extracted keys.
//! assert!(
//!     view.check(&DisjointBy::new(
//!         |_: &PromiseSystem<_, _, _>, b: &Binding<_, _, _>| Some(b.consumer)
//!     ))
//!     .is_ok()
//! );
//! ```

mod monoid;
mod standard;

use core::fmt;

use crate::promise::{BodyAlgebra, PromiseSystem, Resolved};

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
