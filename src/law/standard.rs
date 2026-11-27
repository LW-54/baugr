//! Reusable standard [`ScopeLaw`] instances: single-offer valency, grouped
//! cross-offer/scope monoidal budgets, consumer quorum, unique provider,
//! pairwise disjointness, and grouped coordination `C(b)`.

use alloc::collections::BTreeMap;
use core::fmt;
use core::marker::PhantomData;

use crate::promise::{Binding, BodyAlgebra, PromiseSystem};

use super::monoid::ResourceMonoid;
use super::{ResolutionView, ScopeLaw};

// ----------------------------------------------------------------------------
// Standard Law 1a: Single-Offer Promise Valency (`+b#C`)
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

impl<P: fmt::Debug, R: fmt::Debug> core::error::Error for ValencyDeficit<P, R> {}

/// Single-offer Promise Valency Law (`+b#C`, `arXiv:1505.01716v1` §2.7).
#[derive(Clone, Debug)]
pub struct ValencyLaw<P, R, F> {
    /// Offer promise identifier whose capacity is bounded.
    pub offer_id: P,
    /// Maximum capacity in `R`.
    pub capacity: R,
    /// Extractor mapping each active binding on `offer_id` to its demand in `R`.
    pub weight: F,
}

impl<A, P, D, Rule, R, F> ScopeLaw<A, P, D, Rule> for ValencyLaw<P, R, F>
where
    P: Eq + Clone,
    D: BodyAlgebra,
    R: ResourceMonoid,
    F: Fn(&Binding<A, P, D::Overlap>) -> R,
{
    type Error = ValencyDeficit<P, R>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
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
// Standard Law 1b: Generalized Grouped Monoidal Budget (`BudgetBy`)
// ----------------------------------------------------------------------------

/// Violation returned when aggregate bound demand across a resource group
/// (e.g., an agent's shared RAM pool, a battery bank's total grants, or a host's CPU)
/// exceeds that group's capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetDeficit<G, R> {
    /// Over-committed resource group identifier.
    pub group: G,
    /// Aggregate demand across all bindings mapped to `group`.
    pub used: R,
    /// Declared capacity of `group`.
    pub capacity: R,
}

impl<G: fmt::Debug, R: fmt::Debug> fmt::Display for BudgetDeficit<G, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "budget deficit on group {:?}: used {:?} exceeds capacity {:?}",
            self.group, self.used, self.capacity
        )
    }
}

impl<G: fmt::Debug, R: fmt::Debug> core::error::Error for BudgetDeficit<G, R> {}

/// Generalized grouped monoidal budget law: maps each binding to `Option<(group, demand)>`,
/// sums demands per group in any [`ResourceMonoid`] `R`, and checks each group against
/// `capacity(&group)` in a single pass.
///
/// Unifies single-offer valency (`group = b.offer_id`), cross-offer per-agent shared pools
/// (`group = b.promiser`), and per-host / per-superagent multi-dimensional budgets.
pub struct BudgetBy<G, R, F, C> {
    /// Extractor returning `Some((group, demand))` for bindings charged to a budget.
    pub extract: F,
    /// Capacity oracle returning the maximum allowed total in `R` for `group`.
    pub capacity: C,
    _marker: PhantomData<fn() -> (G, R)>,
}

impl<G, R, F, C> BudgetBy<G, R, F, C> {
    /// Constructs a new [`BudgetBy`] law.
    #[must_use]
    pub const fn new(extract: F, capacity: C) -> Self {
        Self {
            extract,
            capacity,
            _marker: PhantomData,
        }
    }
}

impl<G, R, F: Clone, C: Clone> Clone for BudgetBy<G, R, F, C> {
    fn clone(&self) -> Self {
        Self {
            extract: self.extract.clone(),
            capacity: self.capacity.clone(),
            _marker: PhantomData,
        }
    }
}

impl<G, R, F: fmt::Debug, C: fmt::Debug> fmt::Debug for BudgetBy<G, R, F, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BudgetBy")
            .field("extract", &self.extract)
            .field("capacity", &self.capacity)
            .finish()
    }
}

impl<A, P, D, Rule, G, R, F, C> ScopeLaw<A, P, D, Rule> for BudgetBy<G, R, F, C>
where
    D: BodyAlgebra,
    G: Ord + Clone,
    R: ResourceMonoid,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, R)>,
    C: Fn(&G) -> R,
{
    type Error = BudgetDeficit<G, R>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
        let mut totals: BTreeMap<G, R> = BTreeMap::new();
        for b in &view.resolved.bindings {
            if let Some((group, demand)) = (self.extract)(view.system, b) {
                let next = totals
                    .get(&group)
                    .map_or_else(|| demand.clone(), |prev| prev.add(&demand));
                totals.insert(group, next);
            }
        }
        for (group, used) in totals {
            let cap = (self.capacity)(&group);
            if !used.le(&cap) {
                return Err(BudgetDeficit {
                    group,
                    used,
                    capacity: cap,
                });
            }
        }
        Ok(())
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

impl<P: fmt::Debug> core::error::Error for QuorumShortfall<P> {}

/// Requires at least `min_providers` active bindings for `use_id`.
#[derive(Clone, Debug)]
pub struct QuorumLaw<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
    /// Minimum required active bindings.
    pub min_providers: usize,
}

impl<A, P: Eq + Clone, D: BodyAlgebra, Rule> ScopeLaw<A, P, D, Rule> for QuorumLaw<P> {
    type Error = QuorumShortfall<P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
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

impl<P: fmt::Debug> core::error::Error for ProviderCardinalityError<P> {}

/// Requires exactly one unambiguous active offer binding for `use_id`.
#[derive(Clone, Debug)]
pub struct UniqueProviderLaw<P> {
    /// Consumer `Use` promise identifier.
    pub use_id: P,
}

impl<A, P: Eq + Clone, D: BodyAlgebra, Rule> ScopeLaw<A, P, D, Rule> for UniqueProviderLaw<P> {
    type Error = ProviderCardinalityError<P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
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
// Standard Law 4: Pairwise Disjointness (`DisjointBy`)
// ----------------------------------------------------------------------------

/// Violation returned when two active bindings collide on a partition key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisjointViolation<K, P> {
    /// Colliding partition key (e.g., `(host, tcp_port)`, shard ID, CIDR).
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

impl<K: fmt::Debug, P: fmt::Debug> core::error::Error for DisjointViolation<K, P> {}

/// Enforces pairwise distinct keys extracted via `key(system, binding) -> Option<K>`.
///
/// Returning a composite key such as `Some((host, port))` checks per-scope
/// disjointness across *all* superagents simultaneously in a single pass.
pub struct DisjointBy<K, F> {
    /// Key extractor returning `Some(key)` for bindings subject to uniqueness.
    pub key: F,
    _key: PhantomData<fn() -> K>,
}

impl<K, F> DisjointBy<K, F> {
    /// Constructs a new [`DisjointBy`] law.
    #[must_use]
    pub const fn new(key: F) -> Self {
        Self {
            key,
            _key: PhantomData,
        }
    }
}

impl<K, F: Clone> Clone for DisjointBy<K, F> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            _key: PhantomData,
        }
    }
}

impl<K, F: fmt::Debug> fmt::Debug for DisjointBy<K, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DisjointBy")
            .field("key", &self.key)
            .finish()
    }
}

impl<A, P, D, Rule, K, F> ScopeLaw<A, P, D, Rule> for DisjointBy<K, F>
where
    P: Clone,
    D: BodyAlgebra,
    K: Ord + Clone,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<K>,
{
    type Error = DisjointViolation<K, P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
        let mut seen: BTreeMap<K, (P, P)> = BTreeMap::new();
        for b in &view.resolved.bindings {
            if let Some(k) = (self.key)(view.system, b) {
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
// Standard Law 5: Burgess Grouped Coordination / Agreement `C(b)`
// ----------------------------------------------------------------------------

/// Violation returned when two bindings in the same coordination group disagree on a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreementConflict<G, V, P> {
    /// Coordination group where the disagreement occurred (use `()` for global agreement).
    pub group: G,
    /// First observed coordinated value.
    pub first_value: V,
    /// Binding `(offer_id, use_id)` carrying `first_value`.
    pub first_binding: (P, P),
    /// Conflicting value.
    pub conflicting_value: V,
    /// Binding `(offer_id, use_id)` carrying `conflicting_value`.
    pub conflicting_binding: (P, P),
}

impl<G: fmt::Debug, V: fmt::Debug, P: fmt::Debug> fmt::Display for AgreementConflict<G, V, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "agreement C(b) conflict in group {:?}: {:?} ({:?}) != {:?} ({:?})",
            self.group,
            self.first_value,
            self.first_binding,
            self.conflicting_value,
            self.conflicting_binding
        )
    }
}

impl<G: fmt::Debug, V: fmt::Debug, P: fmt::Debug> core::error::Error
    for AgreementConflict<G, V, P>
{
}

/// Burgess Coordination / Agreement Law `C(b)` (`arXiv:1411.5563` L2575):
/// all bindings mapped to the same coordination group `G` must agree on value `V`.
///
/// Use `G = ()` for global agreement, or a superagent/cluster ID to verify
/// per-cluster coordination across the entire system in one pass.
pub struct AgreementBy<G, V, F> {
    /// Extractor returning `Some((group, value))` for participating bindings.
    pub extract: F,
    _marker: PhantomData<fn() -> (G, V)>,
}

impl<G, V, F> AgreementBy<G, V, F> {
    /// Constructs a new [`AgreementBy`] law.
    #[must_use]
    pub const fn new(extract: F) -> Self {
        Self {
            extract,
            _marker: PhantomData,
        }
    }
}

impl<G, V, F: Clone> Clone for AgreementBy<G, V, F> {
    fn clone(&self) -> Self {
        Self {
            extract: self.extract.clone(),
            _marker: PhantomData,
        }
    }
}

impl<G, V, F: fmt::Debug> fmt::Debug for AgreementBy<G, V, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AgreementBy")
            .field("extract", &self.extract)
            .finish()
    }
}

impl<A, P, D, Rule, G, V, F> ScopeLaw<A, P, D, Rule> for AgreementBy<G, V, F>
where
    P: Clone,
    D: BodyAlgebra,
    G: Ord + Clone,
    V: Eq + Clone,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, V)>,
{
    type Error = AgreementConflict<G, V, P>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
        let mut expected: BTreeMap<G, (V, (P, P))> = BTreeMap::new();
        for b in &view.resolved.bindings {
            if let Some((group, value)) = (self.extract)(view.system, b) {
                let pair = (b.offer_id.clone(), b.use_id.clone());
                if let Some((first_value, first_binding)) = expected.get(&group) {
                    if *first_value != value {
                        return Err(AgreementConflict {
                            group,
                            first_value: first_value.clone(),
                            first_binding: first_binding.clone(),
                            conflicting_value: value,
                            conflicting_binding: pair,
                        });
                    }
                } else {
                    expected.insert(group, (value, pair));
                }
            }
        }
        Ok(())
    }
}
