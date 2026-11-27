# Baugr

A minimal, formally verified `#![no_std]` Rust + Lean 4 library for **Promise Theory** and **Semantic Spacetime $\gamma(3,4)$**.

[Paper (PDF)](https://lw-54.github.io/baugr/baugr.pdf) · [Examples](examples/) · [Lean 4 Proofs](lean/Baugr/) · [License](LICENSE)

Baugr models voluntary coordination between autonomous agents—including value-derived conditional promises (`+f(obs) | C`), observer-local assessments, strict $\gamma(3,4)$ causal geometry, and compile-time-checked static law discharge. Zero runtime dependencies, `#![forbid(unsafe_code)]`, and 37 zero-`sorryAx` Lean 4 theorems guarantee **Non-Coercion**, **Event-Horizon Boundary Integrity**, **Reverse Light-Cone Locality**, and **Stratification Independence** for every expressible system.

## Try It

```bash
cargo run --example microgrid  # opaque 2-of-3 battery bank, Request->Grant allocation, failover & residual split
cargo run --example raft       # opaque Raft superagent quorum, blocked piercing & light cone
cargo run --example tenancy    # Burgess tenancy, type-safe static discharge, per-host disjointness & agreement
```

## Verify & Docs

```bash
cargo test                     # unit, domain, purity, property tests & doctests
cargo doc --no-deps --open     # local API reference
just lean                      # Lean 4 build + 0-sorryAx audit (37 theorems)
just drt                       # 500-case value-derived Rust ↔ Lean oracle DRT
nix flake check -L             # full hermetic verification suite (7 checks)
```
