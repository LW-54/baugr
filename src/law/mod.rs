//! Generalized monoidal Promise Valency (`Cap<R>`), four orthogonal composable
//! [`ScopeLaw`]s (`BudgetBy`, `DisjointBy`, `AgreementBy`, `CardinalityBy`),
//! and compile-time-enforced [`StaticUpperBound`] universal discharge.
//!
//! Directly derived from `arXiv:1505.01716v1` §2.7 (`Valency`) and `arXiv:1411.5563`
//! L2575 (coordination `C(b)`).
//!
//! # Example
//! ```
//! use baugr::{AgentSet, Cap, Promise, PromiseSystem, ResolutionView, SymmetricMeet};
//!
//! let mut sys = PromiseSystem::new(SymmetricMeet::new(|o: &u32, u: &u32| (*u <= *o).then_some(*u)));
//! sys.add_promise(Promise::offer("psu", "mains", AgentSet::All, 100));
//! sys.add_promise(Promise::accept("load1", "a", AgentSet::single("mains"), 60));
//! sys.add_promise(Promise::accept("load2", "b", AgentSet::single("mains"), 50));
//!
//! let resolved = sys.resolve_optimistic().unwrap();
//! let view = ResolutionView::new(&sys, &resolved);
//!
//! // 60 + 50 = 110 > 100 triggers a typed BudgetDeficit (zero type annotations needed!).
//! let deficit = view.check_valency("psu", 100_u32, |b| b.overlap).unwrap_err();
//! assert_eq!(deficit.used, 110);
//!
//! // Heterogeneous #1 / #n / #∞ budgets unify cleanly via `Cap<R>`:
//! assert!(view.check_budget(|_, b| Some((b.promiser, Cap::Bounded(b.overlap))), |_| Cap::Unbounded).is_ok());
//!
//! // Type-safe static upper-bound discharge proves downward-closed laws for ALL α:
//! let upper = sys.static_upper_bound();
//! assert!(upper.discharge_disjoint(|_, b| Some(b.consumer)).is_ok());
//! assert!(upper.discharge_agreement(|_, b| Some(((), b.promiser))).is_ok());
//! ```

mod monoid;
mod standard;

use core::convert::Infallible;
use core::fmt;

use crate::promise::{Binding, BodyAlgebra, PromiseSystem, Resolved};

pub use monoid::{Cap, ResourceMonoid};
pub use standard::{
    AgreementBy, AgreementConflict, BudgetBy, BudgetDeficit, CardinalityBy, CardinalityViolation,
    DisjointBy, DisjointViolation,
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

    /// Ergonomic single-offer Promise Valency (`+b#C`) shorthand (special case of [`BudgetBy`]).
    ///
    /// # Errors
    /// Returns [`BudgetDeficit`] if aggregate demand on `offer_id` exceeds `capacity`.
    pub fn check_valency<R, F>(
        &self,
        offer_id: P,
        capacity: R,
        weight: F,
    ) -> Result<(), BudgetDeficit<P, R>>
    where
        P: Eq,
        R: ResourceMonoid,
        F: Fn(&Binding<A, P, D::Overlap>) -> R,
    {
        let mut used = R::zero();
        for b in &self.resolved.bindings {
            if b.offer_id == offer_id {
                used = used.add(&weight(b));
            }
        }
        if used.le(&capacity) {
            Ok(())
        } else {
            Err(BudgetDeficit {
                group: offer_id,
                used,
                capacity,
            })
        }
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

    /// Ergonomic zero-annotation shorthand for fleet-wide [`CardinalityBy`].
    ///
    /// # Errors
    /// Returns [`CardinalityViolation`] if any declared group's count falls outside `[min, max]`.
    pub fn check_cardinality<G, F>(
        &self,
        bounds: impl IntoIterator<Item = (G, usize, Option<usize>)>,
        group: F,
    ) -> Result<(), CardinalityViolation<G>>
    where
        G: Ord + Clone,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<G>,
    {
        self.check(&CardinalityBy::new(bounds, group))
    }

    /// Ergonomic consumer quorum shorthand (`actual >= min_providers`) delegating to [`CardinalityBy`].
    ///
    /// # Errors
    /// Returns [`CardinalityViolation`] if `use_id` has fewer than `min_providers` active bindings.
    pub fn check_quorum(
        &self,
        use_id: P,
        min_providers: usize,
    ) -> Result<(), CardinalityViolation<P>>
    where
        P: Ord + Clone,
    {
        self.check_cardinality([(use_id, min_providers, None)], |_, b| {
            Some(b.use_id.clone())
        })
    }

    /// Ergonomic unique-provider shorthand (`actual == 1`) delegating to [`CardinalityBy`].
    ///
    /// # Errors
    /// Returns [`CardinalityViolation`] if `use_id` has `0` or `> 1` active bindings.
    pub fn check_unique_provider(&self, use_id: P) -> Result<(), CardinalityViolation<P>>
    where
        P: Ord + Clone,
    {
        self.check_cardinality([(use_id, 1, Some(1))], |_, b| Some(b.use_id.clone()))
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

/// Marker trait for [`ScopeLaw`]s that are **downward-closed** (anti-monotone) over
/// the active binding list: if the law holds on a superlist `B₂`, it holds on every
/// sublist `B₁ ⊆ B₂`.
///
/// Verified in Lean 4 (`static_discharge_universal`, `budget_downward_closed`,
/// `disjoint_downward_closed`, `agreement_downward_closed`): only `DownwardClosedLaw`s
/// may be universally discharged on [`StaticUpperBound`] across all runtime assessments `α`.
pub trait DownwardClosedLaw<A, P, D: BodyAlgebra, Rule = Infallible>:
    ScopeLaw<A, P, D, Rule>
{
}

/// Type-safe maximal static upper-bound binding view `B_max(S)` for universal static
/// discharge across **all** observer-local assessments `α` (Lean 4 `static_discharge_universal`).
///
/// By restricting `.discharge(&law)` exclusively to [`DownwardClosedLaw`]s, attempting
/// to unsoundly discharge upward-closed laws (such as [`CardinalityBy`] quorums) on
/// `B_max(S)` is rejected at **compile time**.
pub struct StaticUpperBound<'a, A, P, D: BodyAlgebra, Rule = Infallible> {
    system: &'a PromiseSystem<A, P, D, Rule>,
    resolved: Resolved<A, P, D>,
}

impl<A, P, D, Rule> fmt::Debug for StaticUpperBound<'_, A, P, D, Rule>
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
        f.debug_struct("StaticUpperBound")
            .field("bindings", &self.resolved.bindings)
            .finish()
    }
}

impl<'a, A, P, D: BodyAlgebra, Rule> StaticUpperBound<'a, A, P, D, Rule> {
    pub(crate) const fn new(
        system: &'a PromiseSystem<A, P, D, Rule>,
        resolved: Resolved<A, P, D>,
    ) -> Self {
        Self { system, resolved }
    }

    /// Returns all statically compatible offer–use bindings in `B_max(S)`.
    #[must_use]
    pub fn bindings(&self) -> &[Binding<A, P, D::Overlap>] {
        &self.resolved.bindings
    }

    /// Universally discharges any [`DownwardClosedLaw`] over `B_max(S)`: if this returns
    /// `Ok(())`, the law is guaranteed by Lean 4 (`static_discharge_universal`) to hold
    /// for **every** possible runtime observer-local assessment `α`.
    ///
    /// # Errors
    /// Propagates `L::Error` if `B_max(S)` violates `law`.
    pub fn discharge<L: DownwardClosedLaw<A, P, D, Rule>>(&self, law: &L) -> Result<(), L::Error> {
        let view = ResolutionView::new(self.system, &self.resolved);
        law.check(&view)
    }

    /// Universally discharges single-offer Promise Valency (`+b#C`) for all `α`.
    ///
    /// # Errors
    /// Returns [`BudgetDeficit`] if worst-case static demand on `offer_id` exceeds `capacity`.
    pub fn discharge_valency<R, F>(
        &self,
        offer_id: P,
        capacity: R,
        weight: F,
    ) -> Result<(), BudgetDeficit<P, R>>
    where
        P: Eq,
        R: ResourceMonoid,
        F: Fn(&Binding<A, P, D::Overlap>) -> R,
    {
        ResolutionView::new(self.system, &self.resolved).check_valency(offer_id, capacity, weight)
    }

    /// Universally discharges grouped cross-offer [`BudgetBy`] for all `α`.
    ///
    /// # Errors
    /// Returns [`BudgetDeficit`] if worst-case static demand in any group exceeds `capacity(&group)`.
    pub fn discharge_budget<G, R, F, C>(
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
        self.discharge(&BudgetBy::new(extract, capacity))
    }

    /// Universally discharges pairwise key disjointness [`DisjointBy`] for all `α`.
    ///
    /// # Errors
    /// Returns [`DisjointViolation`] if two statically bindable pairs can collide on a key.
    pub fn discharge_disjoint<K, F>(&self, key: F) -> Result<(), DisjointViolation<K, P>>
    where
        P: Clone,
        K: Ord + Clone,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<K>,
    {
        self.discharge(&DisjointBy::new(key))
    }

    /// Universally discharges Burgess coordination agreement [`AgreementBy`] (`C(b)`) for all `α`.
    ///
    /// # Errors
    /// Returns [`AgreementConflict`] if two statically bindable pairs in a group can disagree.
    pub fn discharge_agreement<G, V, F>(&self, extract: F) -> Result<(), AgreementConflict<G, V, P>>
    where
        P: Clone,
        G: Ord + Clone,
        V: Eq + Clone,
        F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, V)>,
    {
        self.discharge(&AgreementBy::new(extract))
    }
}
