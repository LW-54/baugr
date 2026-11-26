//! Strictly acyclic dressed superagent containment forest & opaque wall checks
//! (`arXiv:1505.01716v1` §§3.3–3.7).

use alloc::collections::{BTreeMap, BTreeSet};
use core::fmt;

/// Error returned when a superagent containment operation would introduce a cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HierarchyError<A> {
    /// An agent cannot contain itself.
    SelfContainment(A),
    /// Placing `child` inside `superagent` would create a containment cycle because
    /// `child` is already an ancestor of `superagent`.
    Cycle {
        /// Intended containing superagent.
        superagent: A,
        /// Intended child that already contains `superagent`.
        child: A,
    },
}

impl<A: fmt::Debug> fmt::Display for HierarchyError<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SelfContainment(a) => write!(f, "agent {a:?} cannot contain itself"),
            Self::Cycle { superagent, child } => write!(
                f,
                "containment cycle: placing {child:?} inside {superagent:?} closes a cycle"
            ),
        }
    }
}

impl<A: fmt::Debug> core::error::Error for HierarchyError<A> {}

/// Acyclic superagent containment forest with explicit opaque/transparent boundaries.
#[derive(Clone, Debug)]
pub struct Hierarchy<A> {
    pub agents: BTreeSet<A>,
    pub parent: BTreeMap<A, A>,
    pub opaque_superagents: BTreeSet<A>,
}

impl<A: Ord + Clone> Hierarchy<A> {
    pub const fn new() -> Self {
        Self {
            agents: BTreeSet::new(),
            parent: BTreeMap::new(),
            opaque_superagents: BTreeSet::new(),
        }
    }

    pub fn add_agent(&mut self, agent: A) {
        self.agents.insert(agent);
    }

    pub fn add_superagent(&mut self, superagent: A, opaque: bool) {
        self.agents.insert(superagent.clone());
        if opaque {
            self.opaque_superagents.insert(superagent);
        } else {
            self.opaque_superagents.remove(&superagent);
        }
    }

    pub fn contain(&mut self, superagent: A, child: A) -> Result<(), HierarchyError<A>> {
        if superagent == child {
            return Err(HierarchyError::SelfContainment(child));
        }
        if self.is_strict_ancestor(&child, &superagent) {
            return Err(HierarchyError::Cycle { superagent, child });
        }
        self.agents.insert(superagent.clone());
        self.agents.insert(child.clone());
        self.parent.insert(child, superagent);
        Ok(())
    }

    pub fn parent_of(&self, agent: &A) -> Option<&A> {
        self.parent.get(agent)
    }

    pub fn is_strict_ancestor(&self, ancestor: &A, node: &A) -> bool {
        let mut cur = node;
        while let Some(p) = self.parent.get(cur) {
            if p == ancestor {
                return true;
            }
            cur = p;
        }
        false
    }

    pub fn members_of(&self, superagent: &A) -> BTreeSet<A> {
        let mut out = BTreeSet::new();
        if self.agents.contains(superagent) {
            out.insert(superagent.clone());
        }
        for a in &self.agents {
            if self.is_strict_ancestor(superagent, a) {
                out.insert(a.clone());
            }
        }
        out
    }

    pub fn no_opaque_wall(&self, a: &A, b: &A) -> bool {
        for s in &self.opaque_superagents {
            let a_strict = self.is_strict_ancestor(s, a);
            let b_strict = self.is_strict_ancestor(s, b);
            let a_in = a == s || a_strict;
            let b_in = b == s || b_strict;
            if (a_strict && !b_in) || (b_strict && !a_in) {
                return false;
            }
        }
        true
    }
}
