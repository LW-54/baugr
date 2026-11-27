# Baugr

A minimal, formally verified `#![no_std]` Rust + Lean 4 library for **Promise Theory** and **Semantic Spacetime $\gamma(3,4)$**.

[Paper (PDF)](https://lw-54.github.io/baugr/baugr.pdf) · [Examples](examples/) · [Lean 4 Proofs](lean/Baugr/) · [License](LICENSE)

Baugr models voluntary coordination between autonomous agents—including static and value-derived conditional promises (`±b | C`, `±f(obs) | C`), observer-local assessments, recursive opaque superagents, and strict $\gamma(3,4)$ causal geometry. Zero runtime dependencies, `#![forbid(unsafe_code)]`, and 30 zero-`sorryAx` Lean 4 theorems guarantee **Non-Coercion**, **Event-Horizon Boundary Integrity**, **Reverse Light-Cone Locality**, and **Stratification Independence** for every expressible system.

## Try It

```bash
cargo run --example microgrid  # opaque 2-of-3 battery bank, +f(obs) priority grants, -f(obs) residual draw & failover
cargo run --example raft       # opaque Raft superagent quorum, blocked piercing & light cone
cargo run --example tenancy    # Burgess tenancy & exclusive port leasing via pure ±f(obs) | C conditions
```

## Verify & Docs

```bash
cargo test                     # unit, domain, purity, property tests & doctests
cargo doc --no-deps --open     # local API reference
just lean                      # Lean 4 build + 0-sorryAx audit (30 theorems)
just drt                       # 500-case value-derived Rust ↔ Lean oracle DRT
nix flake check -L             # full hermetic verification suite (7 checks)
```
