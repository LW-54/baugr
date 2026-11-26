//! Ordered Commutative Monoids for generalized Promise Valency (`+b#n`,
//! capacities, and multi-dimensional budgets) (`arXiv:1505.01716v1` §2.7).

/// Ordered Commutative Monoid for generalized Promise Valency (`+b#n`, capacities,
/// multi-dimensional budgets).
///
/// Laws verified in `lean/Baugr/Law.lean` & `lean/Baugr/Thm/Law.lean`
/// (`valency_withdrawal_safe`):
/// - `(zero, add)` is a commutative monoid
/// - `le` is a reflexive, transitive order with `le(zero, x)` for all `x`
/// - `add` is monotone in both arguments.
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
                fn zero() -> Self { 0 }
                fn add(&self, other: &Self) -> Self { self.saturating_add(*other) }
                fn le(&self, other: &Self) -> bool { self <= other }
            }
        )+
    };
}

impl_uint_monoid!(u32, u64, u128, usize);

/// Exclusive / fermionic resource monoid (`+b#1`, `arXiv:1505.01716v1` L3008).
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

/// Broadcast / bosonic resource monoid (`+b#∞`, `arXiv:1505.01716v1` L3008).
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

/// Cartesian product of any two [`ResourceMonoid`]s (multi-dimensional budgets).
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
