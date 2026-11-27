//! # Baugr
//!
//! A minimal, `#![no_std]` (`alloc`), zero-dependency, formally verified Rust
//! library for **Promise Theory** and **Semantic Spacetime γ(3,4)**, derived
//! directly from the primary mathematical literature of Jan Bergstra and
//! Mark Burgess (`arXiv:0810.3294v5`, `1401.3381v1`, `1411.5563`,
//! `1505.01716v1`, `1608.02193`, `2506.07756v2`, `2606.08552v1`) and
//! machine-checked in Lean 4 (`lean/Baugr/Thm/`).
//!
//! ## Quick Start
//! ```
//! use baugr::{AgentSet, Cond, Promise, PromiseSystem, SymmetricMeet};
//!
//! let mut sys = PromiseSystem::new(SymmetricMeet::new(|a: &u16, b: &u16| (a == b).then_some(*a)));
//! sys.add_promise(Promise::offer("grid:mains", "grid", AgentSet::All, 230));
//! sys.add_promise(Promise::accept("bat:sense", "battery", AgentSet::single("grid"), 230));
//! sys.add_promise(
//!     Promise::offer("bat:backup", "battery", AgentSet::All, 230)
//!         .when(!Cond::assisted("bat:sense")),
//! );
//!
//! // Mains healthy -> backup stays inactive.
//! let normal = sys.resolve_optimistic().unwrap();
//! assert!(!normal.quenched.contains("bat:backup"));
//!
//! // Mains broken -> backup quenches via stratified negation.
//! let outage = sys.resolve(|_, p| *p != "grid:mains").unwrap();
//! assert!(outage.quenched.contains("bat:backup"));
//! ```
//!
//! ## Modules
//! - [`promise`]: Autonomous agents, 2-polarity offers/acceptances (`+b`/`-b`),
//!   mutual-information overlap (`b₁ ∩ b₂`), exact conditional quenching
//!   (`+b | C`) with stratified negation, observer-local assessments
//!   `α(a, π)`, and acyclic opaque/transparent dressed superagents.
//! - [`spacetime`]: Strict typed Semantic Spacetime γ(3,4) with 3 node
//!   meta-types (`Event`, `Thing`, `Concept`), 4 signed link meta-types
//!   (`Near`, `±LeadsTo`, `±Contains`, `±Expresses`), dual-link normalized
//!   causal light cones, sources/sinks/appointed hubs, and quotient
//!   coarse-graining `G`.
//! - [`projection`]: Canonical well-formed functor `Φ : PromiseSystem -> γ(3,4)`
//!   and superagent coarse-graining directories.
//! - [`law`]: Generalized ordered-commutative-monoid Promise Valency (`+b#n`)
//!   and open composable [`law::ScopeLaw`] verification (`ValencyLaw`,
//!   `QuorumLaw`, `UniqueProviderLaw`, `DisjointBy`, `AgreementBy`).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod law;
pub mod projection;
pub mod promise;
pub mod spacetime;

pub use law::{
    AgreementBy, AgreementConflict, DisjointBy, DisjointViolation, MaxOne,
    ProviderCardinalityError, QuorumLaw, QuorumShortfall, ResolutionView, ResourceMonoid, ScopeLaw,
    Unbounded, UniqueProviderLaw, ValencyDeficit, ValencyLaw,
};
pub use projection::{CoarseGrainingDirectory, SstNode, directory_of, project_sst};
pub use promise::{
    AgentSet, Binding, Body, BodyAlgebra, Cond, ConditionWarning, EvalError, HierarchyError,
    IncompleteInfoWarning, Promise, PromiseMap, PromiseSystem, Resolved, SymmetricMeet,
};
pub use spacetime::{CoarseGrainError, LinkKind, NodeKind, SstEdge, SstError, SstGraph};
