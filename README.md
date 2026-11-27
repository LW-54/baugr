# Baugr

A minimal, formally verified `#![no_std]` Rust + Lean 4 library for **Promise Theory** and **Semantic Spacetime $\gamma(3,4)$**.

[Paper (PDF)](https://lw-54.github.io/baugr/baugr.pdf) · [Examples](examples/) · [Lean 4 Proofs](lean/Baugr/) · [License](LICENSE)

Baugr models voluntary coordination between autonomous agents under observer-local assessments and strict $\gamma(3,4)$ causal geometry. Zero runtime dependencies, `#![forbid(unsafe_code)]`, and 29 zero-`sorryAx` Lean 4 theorems guarantee **Non-Coercion**, **Opaque Encapsulation**, **Reverse Light-Cone Locality**, and **Stratification Independence** for every expressible system.

## Try It

```bash
cargo run --example microgrid  # opaque 2-of-3 battery bank, failover, overdraw & load shedding
cargo run --example raft       # opaque Raft superagent quorum, blocked piercing & light cone
cargo run --example tenancy    # Burgess tenancy, fleet-wide per-host disjointness & agreement
```

## Verify & Docs

```bash
cargo test                     # unit, domain, purity, property tests & doctests
cargo doc --no-deps --open     # local API reference
just lean                      # Lean 4 build + 0-sorryAx audit (29 theorems)
just drt                       # 500-case nested-negation Rust ↔ Lean oracle DRT
nix flake check -L             # full hermetic verification suite (7 checks)
```
