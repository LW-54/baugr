//! Generalized monoidal Promise Valency (`+b#n`) and open composable [`ScopeLaw`] algebra.
//!
//! Replaces the closed 4-variant binding discipline enum of v0.1 (`Exclusive`,
//! `Broadcast`, `Partitioned`, `Budgeted`) with two open mathematical abstractions
//! directly derived from `arXiv:1505.01716v1` §2.7 (`Valency`) and `arXiv:1411.5563`
//! L2575 (coordination `C(b)`).

use alloc::collections::BTreeMap;
use core::fmt;
use core::marker::PhantomData;

use crate::promise::{AgentSet, Binding, BodyAlgebra, PromiseSystem, Resolved};

/// Ordered Commutative Monoid for generalized Promise Valency (`+b#n`, capacities,
/// multi-dimensional budgets).
///
/// Laws verified in `lean/Baugr/Law.lean` & `lean/Baugr/Theorems.lean`
/// (`valency_withdrawal_safe`):
/// - `(zero, add)` is a commutative monoid
/// - `le` is a reflexive, transitive order with `le(zero, x)` for all `x`
/// - `add` is monotone in both arguments (`le(a, b) ∧ le(c, d) → le(add(a, c), add(b, d))`).
pub trait ResourceMonoid: Clone {
    /// Additive identity (zero demand).
    fn zero() -> Self;
    /// Commutative, associative demand aggregation.
    #[must_use]
    fn add(&self, other: &Self) -> Self;
    /// Partial order comparing aggregate demand against capacity.
    fn le(&self, other: &Self) -> bool;
}

macro_rules! impl_uint_monoid {
    ($($t:ty),+ $(,)?) => {
        $(
            impl ResourceMonoid for $t {
                fn zero() -> Self {
                    0
                }
                fn add(&self, other: &Self) -> Self {
                    self.saturating_add(*other)
                }
                fn le(&self, other: &Self) -> bool {
                    self <= other
                }
            }
        )+
    };
}

impl_uint_monoid!(u32, u64, u128, usize);

/// Exclusive / fermionic resource monoid (`+b#1` — at most 1 consumer slot,
/// `arXiv:1505.01716v1` L3008).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MaxOne {
    /// Zero consumers bound.
    Zero,
    /// Exactly one consumer bound.
    One,
    /// Over-committed (two or more consumers bound).
    Overflow,
}

impl ResourceMonoid for MaxOne {
    fn zero() -> Self {
        Self::Zero
    }

    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Zero, x) | (x, Self::Zero) => *x,
            _ => Self::Overflow,
        }
    }

    fn le(&self, other: &Self) -> bool {
        self <= other
    }
}

/// Broadcast / bosonic resource monoid (`+b#∞` — unbounded concurrent consumers,
/// `arXiv:1505.01716v1` L3008).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Unbounded;

impl ResourceMonoid for Unbounded {
    fn zero() -> Self {
        Self
    }

    fn add(&self, _other: &Self) -> Self {
        Self
    }

    fn le(&self, _other: &Self) -> bool {
        true
    }
}

/// Cartesian product of any two [`ResourceMonoid`]s (multi-dimensional budgets,
/// e.g. `(CpuMillis, RamMiB)`).
impl<R1: ResourceMonoid, R2: ResourceMonoid> ResourceMonoid for (R1, R2) {
    fn zero() -> Self {
        (R1::zero(), R2::zero())
    }

    fn add(&self, other: &Self) -> Self {
        (self.0.add(&other.0), self.1.add(&other.1))
    }

    fn le(&self, other: &Self) -> bool {
        self.0.le(&other.0) && self.1.le(&other.1)
    }
}

/// Read-only view combining a [`PromiseSystem`] (structure & hierarchy) with its
/// [`Resolved`] fixed point (quenched promises & active bindings).
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
///
/// Any domain-specific invariant can implement [`ScopeLaw`] directly with typed
/// diagnostics; the standard laws in this module are simply reusable instances.
pub trait ScopeLaw<A, P, D: BodyAlgebra> {
    /// Typed violation error returned when the law fails.
    type Error;

    /// Verifies that `view` satisfies this law.
    ///
    /// # Errors
    /// Returns `Err(Self::Error)` describing the exact counterexample when violated.
    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error>;
}

// ----------------------------------------------------------------------------
// Standard Law 1: Generalized Promise Valency (`+b#C`)
// ----------------------------------------------------------------------------

/// Violation returned when aggregate bound demand exceeds an offer's valency capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValencyDeficit<P, R> {
    /// Over-committed offer identifier.
    pub offer_id: P,
    /// Aggregate demand across all active bindings.
    pub used: R,
    /// Declared offer capacity.
    pub capacity: R,
}

impl<P: fmt::Debug, R: fmt::Debug> fmt::Display for ValencyDeficit<P, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "valency deficit on offer {:?}: used {:?} exceeds capacity {:?}",
            self.offer_id, self.used, self.capacity
        )
    }
}

/// Generalized Promise Valency Law (`+b#C`, `arXiv:1505.01716v1` §2.7):
/// verifies that the monoidal sum of demands on `offer_id` does not exceed `capacity`.
#[derive(Clone, Debug)]
pub struct ValencyLaw<P, R, F> {
    /// Offer promise identifier whose capacity is bounded.
    pub offer_id: P,
    /// Maximum capacity in `R`.
    pub capacity: R,
    /// Extractor mapping each active binding on `offer_id` to its demand in `R`.
    pub weight: F,
}

impl<A, P, D, R, F> ScopeLaw<A, P, D> for ValencyLaw<P, R, F>
where
    P: Eq + Clone,
    D: BodyAlgebra,
    R: ResourceMonoid,
    F: Fn(&Binding<A, P, D::Overlap>) -> R,
{
    type Error = ValencyDeficit<P, R>;

    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error> {
        let mut used = R::zero();
        for b in &view.resolved.bindings {
            if b.offer_id == self.offer_id {
                used = used.add(&(self.weight)(b));
            }
        }
        if used.le(&self.capacity) {
            Ok(())
        } else {
            Err(ValencyDeficit {
                offer_id: self.offer_id.clone(),
                used,
                capacity: self.capacity.clone(),
            })
        }
    }
}

// ----------------------------------------------------------------------------
// Standard Law 2: Consumer Quorum (`k`-of-`n`)
// ----------------------------------------------------------------------------

/// Violation returned when a `Use` promise has fewer active bindings than required.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumShortfall<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
    /// Minimum required active providers.
    pub required: usize,
    /// Actual active providers bound.
    pub actual: usize,
}

impl<P: fmt::Debug> fmt::Display for QuorumShortfall<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "quorum shortfall on use {:?}: bound {} < required {}",
            self.use_id, self.actual, self.required
        )
    }
}

/// Requires at least `min_providers` active bindings for `use_id`.
#[derive(Clone, Debug)]
pub struct QuorumLaw<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
    /// Minimum required active bindings.
    pub min_providers: usize,
}

impl<A, P: Eq + Clone, D: BodyAlgebra> ScopeLaw<A, P, D> for QuorumLaw<P> {
    type Error = QuorumShortfall<P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error> {
        let actual = view
            .resolved
            .bindings
            .iter()
            .filter(|b| b.use_id == self.use_id)
            .count();
        if actual >= self.min_providers {
            Ok(())
        } else {
            Err(QuorumShortfall {
                use_id: self.use_id.clone(),
                required: self.min_providers,
                actual,
            })
        }
    }
}

// ----------------------------------------------------------------------------
// Standard Law 3: Unique Provider (`Exact(1)`)
// ----------------------------------------------------------------------------

/// Violation returned when a consumer `Use` promise is bound to 0 or >1 offers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProviderCardinalityError<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
    /// Actual number of bound offers (expected exactly `1`).
    pub actual: usize,
}

impl<P: fmt::Debug> fmt::Display for ProviderCardinalityError<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "unique provider violation on use {:?}: expected 1, found {}",
            self.use_id, self.actual
        )
    }
}

/// Requires exactly one unambiguous active offer binding for `use_id`.
#[derive(Clone, Debug)]
pub struct UniqueProviderLaw<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
}

impl<A, P: Eq + Clone, D: BodyAlgebra> ScopeLaw<A, P, D> for UniqueProviderLaw<P> {
    type Error = ProviderCardinalityError<P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error> {
        let actual = view
            .resolved
            .bindings
            .iter()
            .filter(|b| b.use_id == self.use_id)
            .count();
        if actual == 1 {
            Ok(())
        } else {
            Err(ProviderCardinalityError {
                use_id: self.use_id.clone(),
                actual,
            })
        }
    }
}

// ----------------------------------------------------------------------------
// Standard Law 4: Scoped Pairwise Disjointness (Partitioned / Unique Ports / CIDRs)
// ----------------------------------------------------------------------------

/// Violation returned when two active bindings inside the same scope collide on a partition key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisjointViolation<K, P> {
    /// Colliding partition key (e.g., TCP port, IP address, shard ID).
    pub key: K,
    /// First binding's `(offer_id, use_id)`.
    pub first: (P, P),
    /// Conflicting second binding's `(offer_id, use_id)`.
    pub second: (P, P),
}

impl<K: fmt::Debug, P: fmt::Debug> fmt::Display for DisjointViolation<K, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "disjointness collision on key {:?} between {:?} and {:?}",
            self.key, self.first, self.second
        )
    }
}

/// Enforces pairwise disjoint keys across all active bindings whose promiser and consumer
/// fall within `scope` (e.g., unique TCP ports per host superagent, non-overlapping shards).
#[derive(Clone, Debug)]
pub struct DisjointInScope<A, K, F> {
    /// Agent scope over which keys must be unique (e.g., `AgentSet::Set(sys.members_of(&host))`).
    pub scope: AgentSet<A>,
    /// Key extractor returning `Some(key)` for bindings subject to uniqueness.
    pub key: F,
    _marker: PhantomData<K>,
}

impl<A, K, F> DisjointInScope<A, K, F> {
    /// Constructs a new [`DisjointInScope`] law.
    #[must_use]
    pub const fn new(scope: AgentSet<A>, key: F) -> Self {
        Self {
            scope,
            key,
            _marker: PhantomData,
        }
    }
}

impl<A, P, D, K, F> ScopeLaw<A, P, D> for DisjointInScope<A, K, F>
where
    A: Ord,
    P: Clone,
    D: BodyAlgebra,
    K: Ord + Clone,
    F: Fn(&Binding<A, P, D::Overlap>) -> Option<K>,
{
    type Error = DisjointViolation<K, P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error> {
        let mut seen: BTreeMap<K, (P, P)> = BTreeMap::new();
        for b in &view.resolved.bindings {
            if !self.scope.contains(&b.promiser) && !self.scope.contains(&b.consumer) {
                continue;
            }
            if let Some(k) = (self.key)(b) {
                let pair = (b.offer_id.clone(), b.use_id.clone());
                if let Some(first) = seen.insert(k.clone(), pair.clone()) {
                    return Err(DisjointViolation {
                        key: k,
                        first,
                        second: pair,
                    });
                }
            }
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------------
// Standard Law 5: Burgess Coordination / Agreement C(b) (arXiv:1411.5563 L2575)
// ----------------------------------------------------------------------------

/// Violation returned when two active bindings inside the same scope disagree on a coordinated value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreementConflict<V, P> {
    /// First observed coordinated value.
    pub first_value: V,
    /// Binding `(offer_id, use_id)` carrying `first_value`.
    pub first_binding: (P, P),
    /// Conflicting value.
    pub conflicting_value: V,
    /// Binding `(offer_id, use_id)` carrying `conflicting_value`.
    pub conflicting_binding: (P, P),
}

impl<V: fmt::Debug, P: fmt::Debug> fmt::Display for AgreementConflict<V, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "agreement C(b) conflict: {:?} ({:?}) != {:?} ({:?})",
            self.first_value, self.first_binding, self.conflicting_value, self.conflicting_binding
        )
    }
}

/// Burgess Coordination / Agreement Law `C(b)` (`arXiv:1411.5563` L2575):
/// all selected bindings within `scope` must agree on a single value.
#[derive(Clone, Debug)]
pub struct AgreementInScope<A, V, F> {
    /// Agent scope over which agreement is required.
    pub scope: AgentSet<A>,
    /// Value extractor returning `Some(v)` for bindings participating in coordination.
    pub value: F,
    _marker: PhantomData<V>,
}

impl<A, V, F> AgreementInScope<A, V, F> {
    /// Constructs a new [`AgreementInScope`] law.
    #[must_use]
    pub const fn new(scope: AgentSet<A>, value: F) -> Self {
        Self {
            scope,
            value,
            _marker: PhantomData,
        }
    }
}

impl<A, P, D, V, F> ScopeLaw<A, P, D> for AgreementInScope<A, V, F>
where
    A: Ord,
    P: Clone,
    D: BodyAlgebra,
    V: Eq + Clone,
    F: Fn(&Binding<A, P, D::Overlap>) -> Option<V>,
{
    type Error = AgreementConflict<V, P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D>) -> Result<(), Self::Error> {
        let mut first: Option<(V, (P, P))> = None;
        for b in &view.resolved.bindings {
            if !self.scope.contains(&b.promiser) && !self.scope.contains(&b.consumer) {
                continue;
            }
            if let Some(v) = (self.value)(b) {
                let pair = (b.offer_id.clone(), b.use_id.clone());
                match &first {
                    None => first = Some((v, pair)),
                    Some((fv, _)) if fv == &v => {}
                    Some((fv, fp)) => {
                        return Err(AgreementConflict {
                            first_value: fv.clone(),
                            first_binding: fp.clone(),
                            conflicting_value: v,
                            conflicting_binding: pair,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}
