//! Strict Semantic Spacetime γ(3,4) typed graph algebra.
//!
//! Derived directly from Mark Burgess (2025, `arXiv:2506.07756v2` §§3–5) and
//! Mark Burgess (2015, `arXiv:1505.01716v1` §3.5).
//!
//! Every node has one of three meta-types ([`NodeKind`]):
//! - [`NodeKind::Event`] (`e`): ephemeral, realized, timelike process agent
//! - [`NodeKind::Thing`] (`t`): invariant, realized, spacelike persistent agent
//! - [`NodeKind::Concept`] (`c`): persistent, unrealized, virtual attribute / intent
//!
//! Every edge carries one of four signed link meta-types ([`LinkKind`]):
//! - `0` [`LinkKind::Near`] (`N`): symmetric proximity / similarity
//! - `±1` [`LinkKind::LeadsTo`] / [`LinkKind::Follows`] (`±L`): causal / temporal order
//! - `±2` [`LinkKind::Contains`] / [`LinkKind::ContainedBy`] (`±C`): spatial containment
//! - `±3` [`LinkKind::Expresses`] / [`LinkKind::ExpressedBy`] (`±E`): attribute / promise expression
//!
//! # Example
//! ```
//! use baugr::{LinkKind, NodeKind, SstGraph};
//!
//! let mut g = SstGraph::new();
//! g.add_node("flight", NodeKind::Event).unwrap();
//! g.add_node("landing", NodeKind::Event).unwrap();
//! g.add_node("butterfly", NodeKind::Thing).unwrap();
//! g.add_node("blue", NodeKind::Concept).unwrap();
//!
//! // Inverse links normalize automatically (`landing -L flight` == `flight +L landing`).
//! g.add_edge("landing", LinkKind::Follows, "flight").unwrap();
//! assert!(g.forward_causal_cone(&"flight").contains("landing"));
//!
//! // Disallowed transitions (`Thing +L Event`) are rejected structurally.
//! assert!(g.add_edge("butterfly", LinkKind::LeadsTo, "flight").is_err());
//! ```

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::vec::Vec;
use core::fmt;

/// The 3 node meta-types of Semantic Spacetime γ(3,4) (`arXiv:2506.07756v2` §3.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeKind {
    /// `e` — Event: ephemeral, realized, timelike process agent.
    Event,
    /// `t` — Thing: invariant, realized, spacelike persistent agent.
    Thing,
    /// `c` — Concept: persistent, unrealized, virtual attribute, property, or intent.
    Concept,
}

/// The 4 signed link meta-types of Semantic Spacetime γ(3,4) (`arXiv:2506.07756v2` Table 1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LinkKind {
    /// `0` (`N`): symmetric proximity or similarity.
    Near,
    /// `+1` (`+L`): causal or temporal precedence (`enables`, `causes`, `precedes`).
    LeadsTo,
    /// `-1` (`-L`): causal or temporal dependence (`depends on`, `follows`).
    Follows,
    /// `+2` (`+C`): spatial containment or membership (`contains`, `surrounds`).
    Contains,
    /// `-2` (`-C`): interiority or participation (`is part of`, `inside`).
    ContainedBy,
    /// `+3` (`+E`): qualitative property or promise expression (`expresses`, `promises`).
    Expresses,
    /// `-3` (`-E`): converse expression (`is expressed by`, `is property of`).
    ExpressedBy,
}

impl LinkKind {
    /// Returns the exact algebraic inverse `r⁻¹` satisfying `(r⁻¹)⁻¹ = r`.
    #[must_use]
    pub const fn inv(self) -> Self {
        match self {
            Self::Near => Self::Near,
            Self::LeadsTo => Self::Follows,
            Self::Follows => Self::LeadsTo,
            Self::Contains => Self::ContainedBy,
            Self::ContainedBy => Self::Contains,
            Self::Expresses => Self::ExpressedBy,
            Self::ExpressedBy => Self::Expresses,
        }
    }

    /// Evaluates the strict γ(3,4) transition predicate (`arXiv:2506.07756v2` Rules 1–2,
    /// L614–624 & L1234–1245; ratified in `ADR-0018` A2):
    ///
    /// - `Near`: strictly homogeneous (`e-e`, `t-t`, `c-c`).
    /// - `LeadsTo`: strictly `Event -> Event`.
    /// - `Contains`: realized non-ascending (`e->e`, `e->t`, `t->t`).
    /// - `Expresses`: target is strictly `Concept` (`e->c`, `t->c`, `c->c`).
    /// - Negative links: exact antisymmetric converse of their positive duals.
    #[must_use]
    pub const fn allowed(src: NodeKind, link: Self, dst: NodeKind) -> bool {
        match link {
            Self::Near => matches!(
                (src, dst),
                (NodeKind::Event, NodeKind::Event)
                    | (NodeKind::Thing, NodeKind::Thing)
                    | (NodeKind::Concept, NodeKind::Concept)
            ),
            Self::LeadsTo => matches!((src, dst), (NodeKind::Event, NodeKind::Event)),
            Self::Contains => matches!(
                (src, dst),
                (NodeKind::Event, NodeKind::Event | NodeKind::Thing)
                    | (NodeKind::Thing, NodeKind::Thing)
            ),
            Self::Expresses => matches!(dst, NodeKind::Concept),
            Self::Follows | Self::ContainedBy | Self::ExpressedBy => {
                Self::allowed(dst, link.inv(), src)
            }
        }
    }
}

/// A directed typed edge in a Semantic Spacetime γ(3,4) graph.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SstEdge<N> {
    /// Source node identifier.
    pub src: N,
    /// Signed γ(3,4) link meta-type.
    pub kind: LinkKind,
    /// Destination node identifier.
    pub dst: N,
}

/// Errors produced when mutating an [`SstGraph`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SstError<N> {
    /// Re-registering an existing node with an incompatible [`NodeKind`].
    KindConflict {
        /// Conflicting node identifier.
        node: N,
        /// Existing meta-type already registered.
        existing: NodeKind,
        /// Attempted conflicting meta-type.
        attempted: NodeKind,
    },
    /// Either source or destination node has not been registered in the graph.
    UnknownNode(N),
    /// The transition `(src_kind, link, dst_kind)` violates the strict γ(3,4) rules.
    DisallowedTransition {
        /// Source node identifier.
        src: N,
        /// Source node meta-type.
        src_kind: NodeKind,
        /// Attempted link meta-type.
        link: LinkKind,
        /// Destination node identifier.
        dst: N,
        /// Destination node meta-type.
        dst_kind: NodeKind,
    },
}

impl<N: fmt::Debug> fmt::Display for SstError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::KindConflict {
                node,
                existing,
                attempted,
            } => write!(
                f,
                "node {node:?} already registered as {existing:?}, cannot retype as {attempted:?}"
            ),
            Self::UnknownNode(n) => write!(f, "unknown SST node: {n:?}"),
            Self::DisallowedTransition {
                src,
                src_kind,
                link,
                dst,
                dst_kind,
            } => write!(
                f,
                "disallowed γ(3,4) transition: {src:?} ({src_kind:?}) --{link:?}--> {dst:?} ({dst_kind:?})"
            ),
        }
    }
}

impl<N: fmt::Debug> core::error::Error for SstError<N> {}

/// Error produced when quotient coarse-graining merges nodes of incompatible [`NodeKind`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarseGrainError<N, M> {
    /// Quotient supernode where the kind mismatch occurred.
    pub grain: M,
    /// First node's meta-type assigned to `grain`.
    pub existing_kind: NodeKind,
    /// Conflicting node mapped to the same `grain`.
    pub conflicting_node: N,
    /// Meta-type of the conflicting node.
    pub conflicting_kind: NodeKind,
}

impl<N: fmt::Debug, M: fmt::Debug> fmt::Display for CoarseGrainError<N, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "inhomogeneous coarse grain {:?}: {:?} conflicts with node {:?} ({:?})",
            self.grain, self.existing_kind, self.conflicting_node, self.conflicting_kind
        )
    }
}

impl<N: fmt::Debug, M: fmt::Debug> core::error::Error for CoarseGrainError<N, M> {}

/// A well-formed typed Semantic Spacetime γ(3,4) graph.
///
/// Both [`SstGraph::add_node`] (rejecting conflicting re-typing) and
/// [`SstGraph::add_edge`] (enforcing [`LinkKind::allowed`]) maintain γ(3,4)
/// well-formedness as an unbreakable structural invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SstGraph<N> {
    nodes: BTreeMap<N, NodeKind>,
    edges: BTreeSet<SstEdge<N>>,
}

impl<N: Ord + Clone> Default for SstGraph<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Ord + Clone> SstGraph<N> {
    /// Creates an empty γ(3,4) Semantic Spacetime graph.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            nodes: BTreeMap::new(),
            edges: BTreeSet::new(),
        }
    }

    /// Registers a node with its γ(3,4) meta-type (idempotent if the kind matches).
    ///
    /// # Errors
    /// Returns [`SstError::KindConflict`] if `id` is already registered with a different [`NodeKind`].
    pub fn add_node(&mut self, id: N, kind: NodeKind) -> Result<(), SstError<N>> {
        if let Some(&existing) = self.nodes.get(&id) {
            if existing != kind {
                return Err(SstError::KindConflict {
                    node: id,
                    existing,
                    attempted: kind,
                });
            }
            return Ok(());
        }
        self.nodes.insert(id, kind);
        Ok(())
    }

    /// Returns the map of registered nodes and their meta-types.
    #[must_use]
    pub const fn nodes(&self) -> &BTreeMap<N, NodeKind> {
        &self.nodes
    }

    /// Returns the set of raw stored well-formed edges.
    #[must_use]
    pub const fn edges(&self) -> &BTreeSet<SstEdge<N>> {
        &self.edges
    }

    /// Looks up the [`NodeKind`] of `id`, if present.
    #[must_use]
    pub fn kind_of(&self, id: &N) -> Option<NodeKind> {
        self.nodes.get(id).copied()
    }

    /// Inserts a typed edge after checking node existence and strict γ(3,4) admissibility.
    ///
    /// # Errors
    /// Returns [`SstError::UnknownNode`] if `src` or `dst` is not registered, or
    /// [`SstError::DisallowedTransition`] if `(kind(src), link, kind(dst))` violates
    /// [`LinkKind::allowed`].
    pub fn add_edge(&mut self, src: N, kind: LinkKind, dst: N) -> Result<(), SstError<N>> {
        let Some(&src_kind) = self.nodes.get(&src) else {
            return Err(SstError::UnknownNode(src));
        };
        let Some(&dst_kind) = self.nodes.get(&dst) else {
            return Err(SstError::UnknownNode(dst));
        };
        if !LinkKind::allowed(src_kind, kind, dst_kind) {
            return Err(SstError::DisallowedTransition {
                src,
                src_kind,
                link: kind,
                dst,
                dst_kind,
            });
        }
        self.edges.insert(SstEdge { src, kind, dst });
        Ok(())
    }

    /// Deduplicated directed adjacency pairs along `axis`, automatically normalizing
    /// dual inverse links (`u --r⁻¹--> v` contributes `(v, u)` to `r`, and `Near` is
    /// symmetric) (`arXiv:2506.07756v2` §§3.1 & 5.2).
    #[must_use]
    pub fn axis_edges(&self, axis: LinkKind) -> BTreeSet<(&N, &N)> {
        let inv = axis.inv();
        let mut out = BTreeSet::new();
        for e in &self.edges {
            if e.kind == axis {
                out.insert((&e.src, &e.dst));
            }
            if e.kind == inv {
                out.insert((&e.dst, &e.src));
            }
        }
        out
    }

    /// Forward causal light cone `J⁺(origin)` along [`LinkKind::LeadsTo`] (and dual [`LinkKind::Follows`]).
    #[must_use]
    pub fn forward_causal_cone(&self, origin: &N) -> BTreeSet<N> {
        self.reachable_along(origin, LinkKind::LeadsTo, false)
    }

    /// Reverse causal light cone `J⁻(target)` along [`LinkKind::LeadsTo`] backwards (and dual [`LinkKind::Follows`]).
    #[must_use]
    pub fn reverse_causal_cone(&self, target: &N) -> BTreeSet<N> {
        self.reachable_along(target, LinkKind::LeadsTo, true)
    }

    /// Computes reflexive reachability from `start` along `axis` in `O(V + E)` time,
    /// honoring dual inverse links.
    #[must_use]
    pub fn reachable_along(&self, start: &N, axis: LinkKind, reverse: bool) -> BTreeSet<N> {
        let mut adj: BTreeMap<&N, Vec<&N>> = BTreeMap::new();
        for (u, v) in self.axis_edges(axis) {
            if reverse {
                adj.entry(v).or_default().push(u);
            } else {
                adj.entry(u).or_default().push(v);
            }
        }

        let mut visited = BTreeSet::new();
        let mut queue = VecDeque::new();
        visited.insert(start.clone());
        queue.push_back(start.clone());

        while let Some(cur) = queue.pop_front() {
            if let Some(neighbors) = adj.get(&cur) {
                for &next in neighbors {
                    if visited.insert(next.clone()) {
                        queue.push_back(next.clone());
                    }
                }
            }
        }
        visited
    }

    /// Source nodes on a directed axis (in-degree `0`, `arXiv:2506.07756v2` §4.2 & §5.3).
    #[must_use]
    pub fn sources(&self, axis: LinkKind) -> BTreeSet<N> {
        let has_in: BTreeSet<&N> = self
            .axis_edges(axis)
            .into_iter()
            .map(|(_, dst)| dst)
            .collect();
        self.nodes
            .keys()
            .filter(|n| !has_in.contains(n))
            .cloned()
            .collect()
    }

    /// Absorbing sink nodes on a directed axis (out-degree `0`, `arXiv:2506.07756v2` §4.2 & §5.3).
    #[must_use]
    pub fn sinks(&self, axis: LinkKind) -> BTreeSet<N> {
        let has_out: BTreeSet<&N> = self
            .axis_edges(axis)
            .into_iter()
            .map(|(src, _)| src)
            .collect();
        self.nodes
            .keys()
            .filter(|n| !has_out.contains(n))
            .cloned()
            .collect()
    }

    /// Appointed hub nodes on a directed axis (in-degree `>= 2`, `arXiv:2506.07756v2` §4.2).
    #[must_use]
    pub fn appointed_hubs(&self, axis: LinkKind) -> BTreeSet<N> {
        let mut in_deg: BTreeMap<&N, usize> = BTreeMap::new();
        for (_, dst) in self.axis_edges(axis) {
            let entry = in_deg.entry(dst).or_insert(0);
            *entry = entry.saturating_add(1);
        }
        in_deg
            .into_iter()
            .filter(|(_, d)| *d >= 2)
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Branching nodes on a directed axis (out-degree `>= 2`, `arXiv:2506.07756v2` §5.3).
    #[must_use]
    pub fn branching_points(&self, axis: LinkKind) -> BTreeSet<N> {
        let mut out_deg: BTreeMap<&N, usize> = BTreeMap::new();
        for (src, _) in self.axis_edges(axis) {
            let entry = out_deg.entry(src).or_insert(0);
            *entry = entry.saturating_add(1);
        }
        out_deg
            .into_iter()
            .filter(|(_, d)| *d >= 2)
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Quotient coarse-graining functor `G` (`arXiv:1505.01716v1` §3.5,
    /// `arXiv:2506.07756v2` §4.4, verified by Lean 4 `coarseGrain_wellFormed`).
    ///
    /// Maps every node `n` to supernode `partition(n)`, drops interior self-loops
    /// (`partition(src) == partition(dst)`), and preserves all exterior edges.
    ///
    /// # Errors
    /// Returns [`CoarseGrainError`] if `partition` maps two nodes of different
    /// [`NodeKind`] to the same supernode (violating kind-homogeneity).
    pub fn coarse_grain<M, F>(&self, partition: F) -> Result<SstGraph<M>, CoarseGrainError<N, M>>
    where
        M: Ord + Clone,
        F: Fn(&N) -> M,
    {
        let mut quotient = SstGraph::new();
        for (n, &kind) in &self.nodes {
            let grain = partition(n);
            if let Some(&existing_kind) = quotient.nodes.get(&grain) {
                if existing_kind != kind {
                    return Err(CoarseGrainError {
                        grain,
                        existing_kind,
                        conflicting_node: n.clone(),
                        conflicting_kind: kind,
                    });
                }
            } else {
                quotient.nodes.insert(grain, kind);
            }
        }

        for e in &self.edges {
            let src = partition(&e.src);
            let dst = partition(&e.dst);
            if src != dst {
                quotient.edges.insert(SstEdge {
                    src,
                    kind: e.kind,
                    dst,
                });
            }
        }
        Ok(quotient)
    }
}
