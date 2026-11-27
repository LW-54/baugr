//! Ordered Commutative Monoids and top-completion [`Cap`] (`R⊤`) for generalized
//! Promise Valency (`+b#1`, `+b#n`, `+b#∞`, and multi-dimensional budgets)
//! (`arXiv:1505.01716v1` §2.7).

/// Ordered Commutative Monoid for generalized Promise Valency (`+b#n`, capacities,
/// multi-dimensional budgets).
///
/// Laws verified in `lean/Baugr/Law.lean` & `lean/Baugr/Thm/Law.lean`
/// (`valency_withdrawal_safe`, `budget_downward_closed`):
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

/// Top-completion `R⊤` adjoining an unbounded ceiling `∞` to any [`ResourceMonoid`] `R`.
///
/// Unifies Burgess's fermionic exclusive (`Cap::Bounded(1)`), bounded finite
/// (`Cap::Bounded(1500)`), and bosonic broadcast (`Cap::Unbounded`) valencies
/// (`arXiv:1505.01716v1` L3008) inside a single homogeneous type usable in one
/// [`crate::BudgetBy`] pass or multi-dimensional `(Cap<R1>, Cap<R2>)` product.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Cap<R> {
    /// Finite resource value or capacity ceiling (`+b#1`, `+b#n`).
    Bounded(R),
    /// Unbounded / broadcast ceiling (`+b#∞`).
    Unbounded,
}

impl<R: ResourceMonoid> ResourceMonoid for Cap<R> {
    fn zero() -> Self {
        Self::Bounded(R::zero())
    }

    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bounded(a), Self::Bounded(b)) => Self::Bounded(a.add(b)),
            _ => Self::Unbounded,
        }
    }

    fn le(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Unbounded) => true,
            (Self::Unbounded, Self::Bounded(_)) => false,
            (Self::Bounded(a), Self::Bounded(b)) => a.le(b),
        }
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
