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

| Module | Mathematical Primitives |
| :--- | :--- |
| [`src/promise.rs`](src/promise.rs) | `Body<O, U>` (`Offer` / `Use`), `BodyAlgebra` ($b_1 \cap b_2$), `AgentSet`, `Cond` (`SelfPromise`, `Assisted`, `Accepted`, `Interior`, monotone `AtLeast`, stratified `Not`), `PromiseSystem`, Kosaraju SCC stratification, observer-local `resolve`, complete-information check |
| [`src/spacetime.rs`](src/spacetime.rs) | Strict $\gamma(3,4)$ `NodeKind` (`Event`, `Thing`, `Concept`), `LinkKind` (`0, ±1, ±2, ±3`), `SstGraph`, forward/reverse causal light cones, sources/sinks/appointed hubs, quotient `coarse_grain` $\mathbf{G}$ |
| [`src/projection.rs`](src/projection.rs) | Canonical well-formed functor $\Phi : \text{PromiseSystem} \to \gamma(3,4)$ (`Agent ↦ Thing`, `Promise ↦ Event`, `Intent ↦ Concept`) and `CoarseGrainingDirectory` $\pi_{\text{directory}}$ |
| [`src/law.rs`](src/law.rs) | Ordered Commutative Monoid `ResourceMonoid` (`u32`..`usize`, `MaxOne`, `Unbounded`, Cartesian products), `ResolutionView`, open composable `ScopeLaw`, standard laws (`ValencyLaw`, `QuorumLaw`, `UniqueProviderLaw`, `DisjointInScope`, `AgreementInScope`) |

## Formal Verification (`lean/Baugr/` — Cedar VGD)

- **Zero `Mathlib`, `0` warnings, `0 sorryAx`** across **20 audited theorems** in [`lean/Baugr/Theorems.lean`](lean/Baugr/Theorems.lean):
  - Knaster-Tarski least fixed point & cycle rejection (`quenchIter_le_any_prefixed`, `cyclic_conditional_never_quenches`)
  - Stratified negation equivalence on positive systems (`stratified_agrees_with_positive`)
  - Promise Theory Axiom of Autonomy (`autonomy_unaccepted_offer_inert`)
  - Exact $\gamma(3,4)$ involution, antisymmetry, transitive closure, Couch/Burgess inference closure, quotient `coarseGrain_wellFormed`, and canonical `projectSst_wellFormed`
  - **Crown-Jewel Unification Theorem**: `perturbation_in_reverse_cone` — observer-local assessment perturbations are strictly bounded by the $\gamma(3,4)$ reverse causal light cone $J^-_\Phi(\pi)$
  - Opaque superagent non-piercing encapsulation (`opaque_non_piercing`, `opaque_non_piercing_inward`, `opaque_interior_perturbation_contained`)
  - Generalized monoidal valency withdrawal safety (`valency_withdrawal_safe`) & composable `ScopeLaw` conjunction (`allLaws_cons`)
- **Mechanical Rust ↔ Lean Lock**: [`tests/drt.rs`](tests/drt.rs) runs **500 randomized Promise Systems** against the compiled Lean 4 `baugr-oracle` verifying `0` divergences across quenched promises, active bindings (+ exact overlap $b_1 \cap b_2$), and $\gamma(3,4)$ edges.

## Running Checks

```bash
just test   # cargo fmt, clippy::pedantic, rustdoc, unit + 3-domain + 500 randomized property tests
just lean   # Lean 4 build + 0-sorryAx axiom audit
just drt    # 500-case Rust ↔ Lean 4 differential randomized testing
just check  # Full hermetic `nix flake check -L` (6 checks)
```
