# Baugr

**A formally verified `#![no_std]` Rust + Lean 4 library for Promise Theory and Semantic Spacetime $\gamma(3,4)$.**

[Read the Paper (PDF)](https://lw-54.github.io/baugr/baugr.pdf) · [Examples](examples/) · [Lean 4 Proofs](lean/Baugr/) · [License](LICENSE)

Baugr models decentralized systems as autonomous agents making voluntary offers (`+o`) and acceptances (`-u`) under observer-local assessments $\alpha_a(\pi)$, projected canonically into strict Semantic Spacetime $\gamma(3,4)$ (3 node kinds: _Event_, _Thing_, _Concept_; 4 link axes: _Near_, _LeadsTo_, _Contains_, _Expresses_). Zero runtime dependencies, `#![forbid(unsafe_code)]`, and 29 zero-`sorryAx` Lean 4 theorems guarantee **Non-Coercion**, **Opaque Encapsulation**, **Reverse Light-Cone Locality**, and **Stratification Independence** for every expressible system.

## Quick Start

```rust
use baugr::{
    AgentSet, BodyAlgebra, Cond, Promise, PromiseSystem, ResolutionView, SstNode, project_sst,
};

struct PowerOffer { voltage: u16, max_watts: u32 }
struct PowerUse   { voltage: u16, watts: u32 }
struct Grid;

impl BodyAlgebra for Grid {
    type Offer = PowerOffer;
    type Use = PowerUse;
    type Overlap = u32;

    fn overlap(&self, o: &PowerOffer, u: &PowerUse) -> Option<Self::Overlap> {
        (o.voltage == u.voltage && u.watts <= o.max_watts).then_some(u.watts)
    }
}

let mut sys = PromiseSystem::new(Grid);
sys.add_promise(Promise::offer(
    "mains", "grid", AgentSet::All, PowerOffer { voltage: 230, max_watts: 5000 },
));
sys.add_promise(
    Promise::accept("sense", "bat", AgentSet::single("grid"), PowerUse { voltage: 230, watts: 0 })
        .with_scope(AgentSet::All),
);
sys.add_promise(
    Promise::offer("backup", "bat", AgentSet::All, PowerOffer { voltage: 230, max_watts: 1500 })
        .when(!Cond::assisted("sense")), // stratified failover negation
);
sys.add_promise(Promise::accept(
    "draw", "hosp", AgentSet::of(["grid", "bat"]), PowerUse { voltage: 230, watts: 1000 },
));

assert!(sys.lint().is_empty());                                           // 1. static diagnostics
let outage = sys.resolve(|obs, p| !(*obs == "bat" && *p == "mains"))?;    // 2. observer-local blackout
ResolutionView::new(&sys, &outage).check_valency("backup", 1500_u32, |b| b.overlap)?; // 3. capacity law
let cone = project_sst(&sys).reverse_causal_cone(&SstNode::Promise("backup"));        // 4. causal ancestry J^-
```

## Workflow

1. **Define compatibility (`BodyAlgebra`):** Implement `overlap(&self, o, u) -> Option<Self::Overlap>` (or use `SymmetricMeet` when offers and uses share a single type $\pm b$).
2. **Model agents & walls (`PromiseSystem`):** Register opaque or transparent superagents (`add_superagent`, `contain`) and add voluntary promises (`Promise::offer`, `Promise::accept`, `.when(...)`, `.with_scope(...)`).
3. **Lint statically (`sys.lint()`):** Flag dangling promise IDs, wrong promisers, polarity mismatches, non-interior refs, and incomplete-information scopes before evaluation.
4. **Simulate & query (`resolve`, `project_sst`, `directory_of`):** Sweep observer-local assessments $\alpha$, inspect forward/reverse light cones ($J^+$ blast radius, $J^-$ causal ancestry), and extract superagent directories.
5. **Enforce collective laws (`ResolutionView`):** Check `check_valency`, `check_disjoint`, `check_agreement`, `QuorumLaw`, `UniqueProviderLaw`, or custom `ScopeLaw`s.

## Examples

```bash
cargo run --example microgrid  # opaque 2-of-3 battery bank, failover negation, valency & agreement
cargo run --example raft       # opaque Raft superagent quorum, blocked piercing & light cone
cargo run --example tenancy    # Burgess tenancy, fleet-wide per-host disjointness & C(b) agreement
```

## Verification & Development

Read the full theory, proofs, and comparative analysis in the [paper](https://lw-54.github.io/baugr/baugr.pdf) ([`paper/baugr.typ`](paper/baugr.typ)).

```bash
cargo test                     # unit, domain, purity, property tests & doctests
cargo doc --no-deps --open     # local API reference
just lean                      # Lean 4 build + 0-sorryAx audit (29 theorems, zero Mathlib)
just drt                       # 500-case nested-negation Rust ↔ Lean oracle DRT
just paper                     # compile paper/baugr.typ -> paper/baugr.pdf offline
nix flake check -L             # full hermetic verification suite (7 checks)
```
