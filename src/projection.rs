//! Canonical functor `Φ : PromiseSystem -> γ(3,4)` and Superagent
//! Coarse-Graining Directories.
//!
//! Derived directly from `arXiv:2506.07756v2` Appendix A (*"Only events can lead to events"*)
//! and `arXiv:1505.01716v1` §3.5–3.7 (`Coarse-graining directory`, Def. L1736).
//!
//! Mirrored 1:1 by `lean/Baugr/Projection.lean` (verified by `projectSst_wellFormed`).
//!
//! # Example
//! ```
//! use baugr::{AgentSet, Cond, Promise, PromiseSystem, SstNode, SymmetricMeet, project_sst};
//!
//! let mut sys = PromiseSystem::new(SymmetricMeet::new(|a: &u8, b: &u8| (a == b).then_some(*a)));
//! sys.add_promise(Promise::offer("p1", "a", AgentSet::single("b"), 1));
//! sys.add_promise(Promise::accept("u1", "b", AgentSet::single("a"), 1));
//! sys.add_promise(Promise::offer("p2", "b", AgentSet::All, 2).when(Cond::assisted("u1")));
//!
//! let sst = project_sst(&sys);
//! assert!(sst.reverse_causal_cone(&SstNode::Promise("p2")).contains(&SstNode::Promise("p1")));
//! ```

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use crate::promise::{BodyAlgebra, PromiseSystem};
use crate::spacetime::{LinkKind, NodeKind, SstGraph};

/// Typed node in the canonical γ(3,4) projection of a [`PromiseSystem`]:
/// - [`SstNode::Agent`] maps to [`NodeKind::Thing`] (`t`)
/// - [`SstNode::Promise`] maps to [`NodeKind::Event`] (`e`)
/// - [`SstNode::Intent`] maps to [`NodeKind::Concept`] (`c`)
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SstNode<A, P> {
    /// Autonomous agent or superagent (`Thing`).
    Agent(A),
    /// Promise activation / keeping event (`Event`).
    Promise(P),
    /// Unrealized promise body / intent concept (`Concept`).
    Intent(P),
}

/// Coarse-graining directory for a superagent `S` (`arXiv:1505.01716v1` Def. L1736).
///
/// Captures the fine-grained interior structure lost when coarse-graining `S` to
/// a single black-box node so transparency can be restored on demand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarseGrainingDirectory<A, P> {
    /// The superagent whose boundary this directory describes.
    pub superagent: A,
    /// Whether this superagent's boundary is opaque (hard non-piercing wall).
    pub is_opaque: bool,
    /// Strict descendant sub-agents contained inside `superagent`.
    pub interior_agents: BTreeSet<A>,
    /// Promises made by strict sub-agents inside `superagent`.
    pub interior_promises: BTreeSet<P>,
    /// Promises made directly on `superagent`'s own surface (reducible gateways or
    /// irreducible emergent promises).
    pub surface_promises: BTreeSet<P>,
}

/// Canonical functor `Φ : PromiseSystem -> γ(3,4)`.
///
/// Emits strictly well-formed γ(3,4) edges:
/// - `Agent(superagent) --(+Contains)--> Agent(child)` (`t +C t`)
/// - `Promise(p) --(+Contains)--> Agent(promiser)` (`e +C t`)
/// - `Agent(promiser) --(+Expresses)--> Intent(p)` (`t +E c`)
/// - `Promise(p) --(+Expresses)--> Intent(p)` (`e +E c`)
/// - `Promise(dep) --(+LeadsTo)--> Promise(p)` (`e +L e`)
#[must_use]
pub fn project_sst<A, P, D>(sys: &PromiseSystem<A, P, D>) -> SstGraph<SstNode<A, P>>
where
    A: Ord + Clone,
    P: Ord + Clone,
    D: BodyAlgebra,
{
    let compat = sys.build_compat_index();
    let mut graph = SstGraph::new();

    for a in sys.agents() {
        let _ = graph.add_node(SstNode::Agent(a.clone()), NodeKind::Thing);
    }
    for pr in sys.promises().values() {
        let _ = graph.add_node(SstNode::Promise(pr.id.clone()), NodeKind::Event);
        let _ = graph.add_node(SstNode::Intent(pr.id.clone()), NodeKind::Concept);
    }

    for (child, par) in sys.parents() {
        let _ = graph.add_edge(
            SstNode::Agent(par.clone()),
            LinkKind::Contains,
            SstNode::Agent(child.clone()),
        );
    }

    for pr in sys.promises().values() {
        let _ = graph.add_edge(
            SstNode::Promise(pr.id.clone()),
            LinkKind::Contains,
            SstNode::Agent(pr.promiser.clone()),
        );
        let _ = graph.add_edge(
            SstNode::Agent(pr.promiser.clone()),
            LinkKind::Expresses,
            SstNode::Intent(pr.id.clone()),
        );
        let _ = graph.add_edge(
            SstNode::Promise(pr.id.clone()),
            LinkKind::Expresses,
            SstNode::Intent(pr.id.clone()),
        );

        let mut deps = Vec::new();
        compat.cond_deps(false, &pr.cond, &mut deps);
        for (dep, _) in deps {
            if sys.promises().contains_key(&dep) {
                let _ = graph.add_edge(
                    SstNode::Promise(dep),
                    LinkKind::LeadsTo,
                    SstNode::Promise(pr.id.clone()),
                );
            }
        }
    }

    graph
}

/// Extracts the [`CoarseGrainingDirectory`] of `superagent`.
#[must_use]
pub fn directory_of<A, P, D>(
    sys: &PromiseSystem<A, P, D>,
    superagent: &A,
) -> CoarseGrainingDirectory<A, P>
where
    A: Ord + Clone,
    P: Ord + Clone,
    D: BodyAlgebra,
{
    let mut interior_agents = BTreeSet::new();
    for a in sys.agents() {
        if sys.is_strict_ancestor(superagent, a) {
            interior_agents.insert(a.clone());
        }
    }

    let mut interior_promises = BTreeSet::new();
    let mut surface_promises = BTreeSet::new();
    for pr in sys.promises().values() {
        if &pr.promiser == superagent {
            surface_promises.insert(pr.id.clone());
        } else if interior_agents.contains(&pr.promiser) {
            interior_promises.insert(pr.id.clone());
        }
    }

    CoarseGrainingDirectory {
        superagent: superagent.clone(),
        is_opaque: sys.opaque_superagents().contains(superagent),
        interior_agents,
        interior_promises,
        surface_promises,
    }
}
