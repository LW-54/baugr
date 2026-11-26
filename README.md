# Baugr (`baugr`)

> **Old Norse: *baugr* (Oath Ring)** — A universal, formally verified **Promise Theory** & **Semantic Spacetime $\gamma(3,4)$** compiler, policy verifier, and graph projection toolkit.

Baugr is completely **domain-agnostic** (zero OS, container, cloud, or Nix assumptions). Use it to verify autonomous multi-agent topologies, distributed microservices, electrical microgrids, Kubernetes/Terraform overlays, AI agent capability boundaries, or infrastructure fleets.

---

## Core Design

1. **Fractal Uniform Agency & Non-Piercing Superagents**: Every node is an autonomous agent exposing an explicit exterior surface ($\Pi_{\mathrm{ext}}$). Dressed Superagents compose children into sealed scopes whose interior bindings can never be pierced from the outside.
2. **Cardinality-Checked Scoped Binding (`B3`)**: Four orthogonal promise cardinalities — `exclusive` (unique 1:1), `broadcast` (tag-selected fanout), `partitioned` (strictly disjoint handler ownership), and `budgeted` (priority-tiered resource supply/demand).
3. **Cedar `L3+` `Forbid`-Dominant Authorization**: Boolean set-algebra authorization (`AttrExpr`) over both Superagent and Atomic principals, with sound-and-complete blast-radius and policy-matrix projections.
4. **Data-Driven `ERG-L2` Schemas**: Optional user-defined `schemas/*.toml` registries drive concise `[offer.*]` / `[use.*]` / `[internal.offer.*]` shorthand, static payload type checking, Draft 2020-12 JSON Schema export (`baugr schema-json`), and automatic Promise Type Catalogs in `baugr-doc` — while desugaring **100% totally** into pure Layer-0 IR verified by Lean 4.
5. **Semantic Spacetime $\gamma(3,4)$ Spine**: Projects every verified system onto the four orthogonal link types (`CONTAINS`, `FOLLOWS`, `EXPRESSES`, `NEAR`) with reverse causal impact cones and Unix-piped documentation (`baugr graph --json | baugr-doc`).

---

## Formal Guarantees (AWS Cedar VGD)

| Artifact | Location | Guarantee |
| :--- | :--- | :--- |
| **Pure Promise Theory + SST** | [`lean/Baugr/Theory/`](lean/Baugr/Theory/) | Pure Burgess/Bergstra semantics (`imposition_never_cooperates`, `projectAgentSST`, `siblingFollowsEdges_non_piercing`) |
| **Engine & Type Soundness** | [`lean/Baugr/Engine/`](lean/Baugr/Engine/) | **54 machine-checked Lean 4 theorems (`0 sorryAx`)**, incl. `Resolve` **Progress & Preservation** (`valid_agent_tree_resolves_safely`, `resolve_parent_scope_non_piercing`) and `checkAgentTree_atomic_sound` |
| **Pure Wasm-Ready Kernel** | [`crates/baugr-core/`](crates/baugr-core/) | `unsafe_code = "forbid"`, `clippy::pedantic --deny warnings`, zero `std::fs`/OS I/O, zero domain strings (guarded by unit tests) |
| **Differential Testing (DRT)** | `baugr drt --oracle baugr-oracle` | Bit-for-bit Rust $\leftrightarrow$ Lean 4 oracle equivalence across checker, `Resolve`, SST $\gamma(3,4)$, and Cedar |

---

## Quickstart (`examples/smart-grid`)

```sh
# 1. Verify the autonomous microgrid (schemas, B3 scopes, power budget, invariants, Cedar auth)
baugr --root examples/smart-grid check

# 2. Compute reverse operational impact cone if battery-bank fails
baugr --root examples/smart-grid graph --impact battery-bank

# 3. Explain a Cedar authorization verdict
baugr --root examples/smart-grid explain auditor trip-breaker trip-critical

# 4. Inspect canonical Layer-0 desugared IR or export IDE JSON Schema (Draft 2020-12)
baugr --root examples/smart-grid desugar --agent hospital-load
baugr --root examples/smart-grid schema-json --kind agent > agent.schema.json

# 5. Pipe Semantic Spacetime JSON into mdBook Markdown + Mermaid docs
baugr --root examples/smart-grid graph --json \
  | baugr-doc --out /tmp/smart-grid-docs --title "Smart Grid Architecture"
```

Multiple `--root <dir>` overlays compose fractally in order (`agents/**`, `schemas/**`, `profiles/**`, `policies/**` are discovered recursively with zero artificial barriers).

---

## Repository Layout

```text
├── crates/
│   ├── baugr-core/    # Pure, std::fs-free Wasm-ready Promise Theory & ERG-L2 kernel
│   ├── baugr-cli/     # `baugr` compiler CLI + golden conformance integration tests
│   └── baugr-doc/     # `baugr-doc` pure Unix SST -> mdBook Markdown/Mermaid filter
├── lean/              # Lean 4 specification (`Baugr.{Theory,Engine,Oracle}`) & Audit (54 theorems)
├── examples/          # Domain-agnostic `smart-grid` end-to-end tutorial
├── fixtures/          # Golden valid & invalid conformance fixtures
├── flake.nix          # Hermetic Nix build, Lean 4 audit, DRT, and test checks
└── justfile           # Thin developer workflow shortcuts
```

## License

MIT — see [`LICENSE`](LICENSE).
