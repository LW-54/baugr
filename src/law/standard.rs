//! Four orthogonal standard [`ScopeLaw`] instances:
//! 1. [`BudgetBy`] — monoidal resource upper bounds (`DownwardClosedLaw`, subsumes single-offer valency & `Cap<R>`)
//! 2. [`DisjointBy`] — pairwise key uniqueness (`DownwardClosedLaw`)
//! 3. [`AgreementBy`] — Burgess grouped coordination `C(b)` (`DownwardClosedLaw`)
//! 4. [`CardinalityBy`] — group binding count intervals `[min, max]` (quorums, unique providers, replica ranges)

use alloc::collections::BTreeMap;
use core::fmt;
use core::marker::PhantomData;

use crate::promise::{Binding, BodyAlgebra, PromiseSystem};

use super::monoid::ResourceMonoid;
use super::{DownwardClosedLaw, ResolutionView, ScopeLaw};

// ----------------------------------------------------------------------------
// Standard Law 1: Grouped Monoidal Budget (`BudgetBy` — subsumes Valency `+b#C`)
// ----------------------------------------------------------------------------

/// Violation returned when aggregate bound demand across a resource group
/// (a single offer, an agent's shared pool, or a host's multi-dimensional CPU/RAM)
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

/// Generalized grouped monoidal budget law across arbitrary binding groups.
///
/// Maps each binding to `Option<(group, demand)>`, sums demands per group in any
/// [`ResourceMonoid`] `R` (including [`crate::Cap`] and multi-dimensional tuples
/// `(R1, R2)`), and checks each group against `capacity(&group)` in one pass.
///
/// Unifies single-offer Promise Valency (`+b#C`, `group = b.offer_id`), cross-offer
/// per-agent shared pools (`group = b.promiser`), and heterogeneous `#1` / `#n` / `#∞`
/// fleet budgets via [`crate::Cap`]. Verified downward-closed in Lean 4
/// (`budget_downward_closed`).
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

impl<A, P, D, Rule, G, R, F, C> DownwardClosedLaw<A, P, D, Rule> for BudgetBy<G, R, F, C>
where
    D: BodyAlgebra,
    G: Ord + Clone,
    R: ResourceMonoid,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, R)>,
    C: Fn(&G) -> R,
{
}

// ----------------------------------------------------------------------------
// Standard Law 2: Pairwise Disjointness (`DisjointBy`)
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
/// Verified downward-closed in Lean 4 (`disjoint_downward_closed`).
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

impl<A, P, D, Rule, K, F> DownwardClosedLaw<A, P, D, Rule> for DisjointBy<K, F>
where
    P: Clone,
    D: BodyAlgebra,
    K: Ord + Clone,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<K>,
{
}

// ----------------------------------------------------------------------------
// Standard Law 3: Burgess Grouped Coordination / Agreement `C(b)`
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
/// Verified downward-closed in Lean 4 (`agreement_downward_closed`).
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

impl<A, P, D, Rule, G, V, F> DownwardClosedLaw<A, P, D, Rule> for AgreementBy<G, V, F>
where
    P: Clone,
    D: BodyAlgebra,
    G: Ord + Clone,
    V: Eq + Clone,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<(G, V)>,
{
}

// ----------------------------------------------------------------------------
// Standard Law 4: Grouped Cardinality Intervals (`CardinalityBy` — quorums, unique, ranges)
// ----------------------------------------------------------------------------

/// Violation returned when a group's active binding count falls outside `[min, max]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CardinalityViolation<G> {
    /// Group whose active binding count violated its bounds.
    pub group: G,
    /// Observed active binding count for `group`.
    pub actual: usize,
    /// Inclusive lower bound required.
    pub min: usize,
    /// Optional inclusive upper bound (`None` means unbounded above).
    pub max: Option<usize>,
}

impl<G: fmt::Debug> fmt::Display for CardinalityViolation<G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.max {
            Some(hi) => write!(
                f,
                "cardinality violation on group {:?}: actual {} outside [{}..={}]",
                self.group, self.actual, self.min, hi
            ),
            None => write!(
                f,
                "cardinality violation on group {:?}: actual {} < min {}",
                self.group, self.actual, self.min
            ),
        }
    }
}

impl<G: fmt::Debug> core::error::Error for CardinalityViolation<G> {}

/// Fleet-wide grouped binding-count interval law `[min, max]` per declared group.
///
/// Unifies consumer quorums (`min = k, max = None`), unique provider checks
/// (`min = 1, max = Some(1)`), and multi-service replica bounds (`[2, 5]`) in a
/// single pass—explicitly checking declared groups even when they have `0` bindings.
///
/// Intentionally does **not** implement [`DownwardClosedLaw`]: lower bounds (`min >= 1`)
/// are upward-closed and therefore cannot be soundly discharged on `B_max(S)`.
pub struct CardinalityBy<G, F> {
    /// Declared groups and their inclusive `(min, max)` binding-count bounds.
    pub bounds: BTreeMap<G, (usize, Option<usize>)>,
    /// Extractor mapping each active binding to the group it counts toward.
    pub group: F,
}

impl<G, F> CardinalityBy<G, F> {
    /// Constructs a new [`CardinalityBy`] law from an explicit map of `(group -> (min, max))`
    /// and a binding-to-group extractor.
    #[must_use]
    pub fn new(bounds: impl IntoIterator<Item = (G, usize, Option<usize>)>, group: F) -> Self
    where
        G: Ord,
    {
        let map = bounds
            .into_iter()
            .map(|(g, min, max)| (g, (min, max)))
            .collect();
        Self { bounds: map, group }
    }
}

impl<G: Clone, F: Clone> Clone for CardinalityBy<G, F> {
    fn clone(&self) -> Self {
        Self {
            bounds: self.bounds.clone(),
            group: self.group.clone(),
        }
    }
}

impl<G: fmt::Debug, F: fmt::Debug> fmt::Debug for CardinalityBy<G, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CardinalityBy")
            .field("bounds", &self.bounds)
            .field("group", &self.group)
            .finish()
    }
}

impl<A, P, D, Rule, G, F> ScopeLaw<A, P, D, Rule> for CardinalityBy<G, F>
where
    D: BodyAlgebra,
    G: Ord + Clone,
    F: Fn(&PromiseSystem<A, P, D, Rule>, &Binding<A, P, D::Overlap>) -> Option<G>,
{
    type Error = CardinalityViolation<G>;

    fn check(&self, view: &ResolutionView<'_, A, P, D, Rule>) -> Result<(), Self::Error> {
        let mut counts: BTreeMap<G, usize> = BTreeMap::new();
        for b in &view.resolved.bindings {
            if let Some(g) = (self.group)(view.system, b) {
                let entry = counts.entry(g).or_insert(0);
                *entry = entry.saturating_add(1);
            }
        }
        for (group, &(min, max)) in &self.bounds {
            let actual = counts.get(group).copied().unwrap_or(0);
            if actual < min || max.is_some_and(|hi| actual > hi) {
                return Err(CardinalityViolation {
                    group: group.clone(),
                    actual,
                    min,
                    max,
                });
            }
        }
        Ok(())
    }
}
