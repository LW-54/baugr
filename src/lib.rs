//! # Baugr
//!
//! A minimal, `#![no_std]` (`alloc`), zero-dependency, formally verified Rust
//! library for **Promise Theory** and **Semantic Spacetime γ(3,4)**, derived
//! directly from the primary mathematical literature of Jan Bergstra and
//! Mark Burgess (`arXiv:0810.3294v5`, `1401.3381v1`, `1411.5563`,
//! `1505.01716v1`, `1608.02193`, `2506.07756v2`, `2606.08552v1`) and
//! machine-checked in Lean 4 (`lean/Baugr/Theorems.lean`).
//!
//! ## Modules
//! - [`promise`]: Autonomous agents, 2-polarity offers/acceptances (`+b`/`-b`),
//!   mutual-information overlap (`b₁ ∩ b₂`), exact conditional quenching
//!   (`+b | C`) with stratified negation, observer-local assessments
//!   `α(a, π)`, and opaque/transparent dressed superagents.
//! - [`spacetime`]: Strict typed Semantic Spacetime γ(3,4) with 3 node
//!   meta-types (`Event`, `Thing`, `Concept`), 4 signed link meta-types
//!   (`Near`, `±LeadsTo`, `±Contains`, `±Expresses`), causal light cones,
//!   sources/sinks/appointed hubs, and quotient coarse-graining `G`.
//! - [`projection`]: Canonical well-formed functor `Φ : PromiseSystem -> γ(3,4)`
//!   and superagent coarse-graining directories.
//! - [`law`]: Generalized ordered-commutative-monoid Promise Valency (`+b#n`)
//!   and open composable [`law::ScopeLaw`] verification (`ValencyLaw`,
//!   `QuorumLaw`, `UniqueProviderLaw`, `DisjointInScope`, `AgreementInScope`).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod law;
pub mod projection;
pub mod promise;
pub mod spacetime;

pub use law::{
    AgreementConflict, AgreementInScope, DisjointInScope, DisjointViolation, MaxOne,
    ProviderCardinalityError, QuorumLaw, QuorumShortfall, ResolutionView, ResourceMonoid, ScopeLaw,
    Unbounded, UniqueProviderLaw, ValencyDeficit, ValencyLaw,
};
pub use projection::{CoarseGrainingDirectory, SstNode, directory_of, project_sst};
pub use promise::{
    AgentSet, Binding, Body, BodyAlgebra, Cond, EvalError, IncompleteInfoWarning, Promise,
    PromiseMap, PromiseSystem, Resolved, SymmetricMeet,
};
pub use spacetime::{CoarseGrainError, LinkKind, NodeKind, SstEdge, SstError, SstGraph};
