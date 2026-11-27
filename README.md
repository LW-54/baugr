# Baugr

A minimal, `#![no_std]` (`alloc`), `#![forbid(unsafe_code)]`, **zero-runtime-dependency**, formally verified Rust + Lean 4 library for **Promise Theory** and **Semantic Spacetime $\gamma(3,4)$**.

Derived directly from the primary mathematical papers of Jan Bergstra and Mark Burgess:
- `arXiv:0810.3294v5` — *A Static Theory of Promises* (scope vs. promisee, relative/absolute keeping, subjective assessment)
- `arXiv:1401.3381v1` — *Promises, Impositions, and other Directionals* (2 polarities, compliance as conditional promise)
- `arXiv:1411.5563` — *Spacetimes with Semantics (I)* (mutual-information overlap $b_1 \cap b_2$, assisted quenching, coordination $C(b)$)
- `arXiv:1505.01716v1` — *Spacetimes with Semantics (II)* (Promise Valency `#n`, opaque/transparent dressed superagents, coarse-graining directories, irreducible emergent promises, tenancy)
- `arXiv:1608.02193` — *Spacetimes with Semantics (III)* (four irreducible link axes, multi-condition aggregation)
- `arXiv:2506.07756v2` — *Agent Semantics, Semantic Spacetime, and Graphical Reasoning* (strict $\gamma(3,4)$ `(Event, Thing, Concept)` $\times$ `(Near, ±LeadsTo, ±Contains, ±Expresses)`)
- `arXiv:2606.08552v1` — *Quantitative Promise Theory* (observer-local assessment $\alpha_a(\pi)$, self & assisted quenching)

## Architecture (4 Modules)

| Module | Rust | Lean 4 | Mathematical Primitives |
| :--- | :--- | :--- | :--- |
| **Promise Algebra** | [`src/promise/`](src/promise/mod.rs) | [`Baugr/Promise.lean`](lean/Baugr/Promise.lean) | `Body<O, U>` (`Offer`/`Use`), `BodyAlgebra` ($b_1 \cap b_2$), `AgentSet`, `Cond` (`SelfPromise`, `Assisted`, `Accepted`, `Interior`, monotone `AtLeast`, native `!` stratified negation), acyclic opaque/transparent `Hierarchy`, Kosaraju SCC stratification, observer-local `resolve`, static `lint()` & complete-information checks |
| **Semantic Spacetime** | [`src/spacetime.rs`](src/spacetime.rs) | [`Baugr/Spacetime.lean`](lean/Baugr/Spacetime.lean) | Strict $\gamma(3,4)$ `NodeKind` (`Event`, `Thing`, `Concept`), `LinkKind` (`0, ±1, ±2, ±3`), invariant-enforcing `SstGraph`, dual-link normalized $O(V+E)$ causal light cones, sources/sinks/hubs, quotient `coarse_grain` $\mathbf{G}$ |
| **Projection & Directories** | [`src/projection.rs`](src/projection.rs) | [`Baugr/Projection.lean`](lean/Baugr/Projection.lean) | Canonical well-formed functor $\Phi : \text{PromiseSystem} \to \gamma(3,4)$ (`Agent ↦ Thing`, `Promise ↦ Event`, `Intent ↦ Concept`) and `CoarseGrainingDirectory` $\pi_{\text{directory}}$ |
| **Valency & Open Laws** | [`src/law/`](src/law/mod.rs) | [`Baugr/Law.lean`](lean/Baugr/Law.lean) | Ordered Commutative Monoid `ResourceMonoid` (`u32`..`usize`, `MaxOne`, `Unbounded`, Cartesian products), `ResolutionView` (with zero-annotation `check_valency`/`check_disjoint`/`check_agreement`), open composable `ScopeLaw`, standard laws (`ValencyLaw`, `QuorumLaw`, `UniqueProviderLaw`, `DisjointBy`, `AgreementBy`) |

## Formal Verification (`lean/Baugr/Thm/` — Cedar VGD)

**Zero `Mathlib`, `0` warnings, `0 sorryAx`** across **29 audited theorems** ([`Baugr/Audit.lean`](lean/Baugr/Audit.lean)):

| Family | Proof Module | Audited Theorems | Guarantee |
| :---: | :--- | :--- | :--- |
| **T1–T2** | [`Thm/Quenching.lean`](lean/Baugr/Thm/Quenching.lean) | `evalCond_mono`, `evalCond_mono_pol`, `quenchStep_mono`, `quenchIter_le_any_prefixed`, `quenchIter_chain`, `cyclic_conditional_never_quenches`, `stratified_agrees_with_positive` | Knaster-Tarski least fixed point, polarity-indexed monotonicity under arbitrary nested `Not`, circular cycle rejection |
| **T3** | [`Thm/Stratification.lean`](lean/Baugr/Thm/Stratification.lean) | `checkValidStratification_sound`, `stratumStep_mono`, `stratumIter_fixed_point`, `evalStratified_fixed_point`, **`stratification_independent`** | Sound stratification validation, finite convergence ($\le |P|+1$ steps) to a global fixed point & **Apt–Blair–Walker Stratification Independence** |
| **T4** | [`Thm/Autonomy.lean`](lean/Baugr/Thm/Autonomy.lean) | `autonomy_unaccepted_offer_inert` | **Axiom of Autonomy**: unaccepted offers/impositions cannot alter any existing condition |
| **T5** | [`Thm/Spacetime.lean`](lean/Baugr/Thm/Spacetime.lean) | `LinkKind.inv_inv`, `allowed_antisym`, `hasEdge_inv`, `hasEdge_wellFormed`, `allowed_pos_trans`, `inference_contains_expresses`, `inference_near_expresses`, `coarseGrain_wellFormed` | Exact $\gamma(3,4)$ involution, dual-link symmetry, antisymmetry, transitivity, Couch/Burgess inference closure, quotient coarse-graining |
| **T5d–T6** | [`Thm/LightCone.lean`](lean/Baugr/Thm/LightCone.lean) | `projectSst_wellFormed`, **`perturbation_in_reverse_cone`** | Canonical $\Phi$ well-formedness & **Crown-Jewel SST Reverse Light Cone Perturbation Containment** |
| **T7** | [`Thm/Superagent.lean`](lean/Baugr/Thm/Superagent.lean) | `noOpaqueWall_symm`, `opaque_non_piercing`, `opaque_non_piercing_inward`, `opaque_interior_perturbation_contained` | Opaque superagent non-piercing encapsulation (outward & inward) & interior isolation |
| **T8** | [`Thm/Law.lean`](lean/Baugr/Thm/Law.lean) | `valency_withdrawal_safe`, `allLaws_cons` | Monoidal valency withdrawal safety & composable `ScopeLaw` conjunction |

- **Mechanical Rust ↔ Lean Lock**: [`tests/drt.rs`](tests/drt.rs) runs **500 randomized Promise Systems** (including arbitrarily nested negations) against the compiled Lean 4 `baugr-oracle`. Lean mechanically validates Rust's Kosaraju stratification via `checkValidStratification` on every case before asserting `0` divergences across quenched promises, active bindings (+ exact overlap $b_1 \cap b_2$), and $\gamma(3,4)$ edges.

## Documentation, Paper & Examples

- **Conceptual & Mathematical Paper**: [`paper/baugr.typ`](paper/baugr.typ) — compiles hermetically offline via `nix build .#paper` (or `just paper`) to an 11-page PDF presenting the problem of voluntary coordination, running microgrid and consensus examples, the Promise Theory + $\gamma(3,4)$ algebra, the Four Universal Laws, comparative landscape, and verified realization.
- **API Reference & Executable Doctests**: `cargo doc --no-deps --open` and `cargo test --doc`.
- **Standalone Runnable Examples**:
  - `cargo run --example microgrid` — stratified failover, split blackout, and wattage valency
  - `cargo run --example raft` — opaque superagent 2-of-3 quorum emergence & reverse light cone
  - `cargo run --example tenancy` — Burgess tenancy, simultaneous per-host `DisjointBy`, and `AgreementBy` $C(b)$

## Running Checks

```bash
just test   # cargo fmt, clippy::pedantic, rustdoc, unit + domain + 500 property tests + doctests
just lean   # Lean 4 build + 0-sorryAx audit across all 29 theorems
just drt    # 500-case Rust ↔ Lean 4 differential randomized testing
just paper  # Compile paper/baugr.typ -> paper/baugr.pdf
just check  # Full hermetic `nix flake check -L` (7 checks)
```
