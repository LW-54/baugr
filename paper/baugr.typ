// Baugr v0.2 — Formal Technical Specification & Verification Paper
// Build offline with: `typst compile paper/baugr.typ paper/baugr.pdf` or `nix build .#paper`

#set document(
  title: "Baugr: A Minimal, Formally Verified Library for Promise Theory and Semantic Spacetime γ(3,4)",
  author: "LW-54",
)

#set page(
  paper: "a4",
  margin: (x: 2.1cm, y: 2.2cm),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 8.5pt, fill: luma(100))
      _Baugr v0.2 — Formally Verified Promise Theory & Semantic Spacetime $gamma(3,4)$_
      #h(1fr)
      #counter(page).display()
    ]
  },
  footer: [],
)

#set text(font: "Libertinus Serif", size: 10pt, lang: "en")
#set par(justify: true, leading: 0.60em)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => {
  v(0.8em, weak: true)
  set text(size: 12.5pt, weight: "bold")
  it
  v(0.35em, weak: true)
}
#show heading.where(level: 2): it => {
  v(0.6em, weak: true)
  set text(size: 10.6pt, weight: "bold")
  it
  v(0.25em, weak: true)
}
#show raw.where(block: true): it => block(
  width: 100%,
  fill: luma(248),
  stroke: (left: 2pt + luma(160)),
  inset: (x: 8pt, y: 6pt),
  radius: (right: 2pt),
  text(size: 8.3pt, it),
)
#show raw.where(block: false): text.with(size: 8.6pt)

// Clean left-aligned cells inside all tables (prevents stretched spaces or overflows)
#show table.cell: it => {
  set par(justify: false, leading: 0.52em)
  it
}

#let accent = rgb("#1f4e79")
#let softbg = rgb("#f4f7fa")
#let splus = $attach(prec, tr: +)$

#let thmbox(kind, label, body) = block(
  width: 100%,
  fill: softbg,
  stroke: (left: 2.5pt + accent, rest: 0.4pt + luma(210)),
  inset: (x: 9pt, y: 7pt),
  radius: 2pt,
  breakable: false,
  [
    #text(weight: "bold", fill: accent)[#kind (#label).] #body
  ],
)

// ============================================================================
// Title & Abstract
// ============================================================================

#align(center)[
  #text(size: 16.5pt, weight: "bold")[
    Baugr: A Minimal, Formally Verified Library for \
    Promise Theory and Semantic Spacetime $gamma(3,4)$
  ]
  #v(0.55em)
  #text(size: 9.8pt, fill: luma(70))[
    Technical Specification & Formal Verification Report — `baugr` v0.2.0 \
    Repository: `https://github.com/LW-54/baugr`
  ]
]

#v(0.7em)

#block(
  width: 100%,
  fill: luma(247),
  stroke: 0.5pt + luma(200),
  inset: 10.5pt,
  radius: 3pt,
)[
  #align(center)[#text(weight: "bold", size: 9.5pt)[Abstract]]
  #v(0.3em)
  #set text(size: 9.2pt)
  *Baugr* is a minimal, `#![no_std]` (`alloc`), `#![forbid(unsafe_code)]`, zero-runtime-dependency Rust library paired with a zero-`Mathlib` Lean 4 formal kernel for *Promise Theory* and *Semantic Spacetime* $gamma(3,4)$. Rather than embedding ad-hoc configuration schemas, custom boolean DSLs, or domain-specific authorization policies, Baugr derives four orthogonal algebraic primitives directly from the primary mathematical literature of Jan Bergstra and Mark Burgess: (1) two-polarity offers and acceptances paired via mutual-information body overlap $b_1 inter b_2$ with autonomy-grounded conditional quenching and observer-local boolean assessments $alpha_a (pi)$, (2) strict typed Semantic Spacetime $gamma(3,4)$ graphs with dual-link normalization and kind-homogeneous quotient coarse-graining $bold(G)$, (3) a canonical well-formed functor $Phi : "PromiseSystem" -> gamma(3,4)$ mapping agents to _Things_, promises to _Events_, and intents to _Concepts_, and (4) generalized ordered-commutative-monoid Promise Valency (`+b#n`) with open composable `ScopeLaw` verification.

  We machine-check *26 theorems* in pure Lean 4 (`0` warnings, `0 sorryAx`), including two flagship unification results: *Perturbation Containment in the Reverse Causal Light Cone* (observer-local assessment changes outside $J^-_Phi (pi)$ cannot alter $pi$, even under stratified negation) and *Apt–Blair–Walker Stratification Independence* (any two valid stratifications converge in at most $|P|+1$ steps to the exact same fixed point, proved directly via SST light cones). Following AWS Cedar Verification-Guided Development, a 500-case randomized differential test harness locks the Rust implementation bit-for-bit against the compiled Lean 4 oracle with zero divergences in `0.25 s`.
]

#v(0.5em)

= Introduction & Architectural Boundaries

Autonomous distributed systems—from electrical microgrids and consensus clusters to multi-tenant cloud fabrics—consist of independent agents whose cooperation arises from voluntary promises rather than top-down coercion @bergstra2008static @bergstra2014impositions. While Promise Theory and Semantic Spacetime @burgess2025sst offer an unusually clean mathematical vocabulary for modeling autonomy, conditional dependencies, superagent encapsulation, and causal structure, existing software tools either hard-code a single domain (e.g., configuration management) or collapse formal promise semantics into unverified heuristics.

Baugr is designed around Ousterhout's principle of *module depth* @ousterhout2018philosophy: maximize expressive power while minimizing interface surface. Every component is strictly domain-agnostic and formally justified:

- *What Baugr IS*: A standalone `#![no_std]` (`alloc`) Rust crate (10 focused modules, \~2.5k LOC, *zero* runtime dependencies) paired 1:1 with a zero-`Mathlib` Lean 4 formal specification and proof suite (13 modules, \~2.0k LOC, *26 audited theorems*, `0 sorryAx`).
- *What Baugr intentionally EXCLUDES*: No command-line interface, no documentation generator, no file or TOML loader, no syntactic sugar or schema desugarer, no custom boolean predicate DSL, and no access-control or authority engine (e.g., Cedar or Biscuit). Higher-level systems compose Baugr as their verified mathematical foundation without inheriting domain assumptions.

#figure(
  kind: image,
  supplement: [Figure],
  block(
    width: 100%,
    inset: 8pt,
    stroke: 0.5pt + luma(190),
    radius: 3pt,
    fill: white,
  )[
    #set par(justify: false)
    #set text(size: 8.5pt)
    #grid(
      columns: (1fr, auto, 1fr),
      align: center + horizon,
      gutter: 8pt,
      block(width: 100%, fill: softbg, stroke: 0.6pt + accent, inset: 7pt, radius: 2pt)[
        *1. Promise Algebra* (`promise/`) \
        `Body<O, U>`, `BodyAlgebra` ($b_1 inter b_2$) \
        `Cond<P>` (`Self`, `Assisted`, `Accepted`, `Interior`, `AtLeast`, `!`) \
        Acyclic `Hierarchy` & Kosaraju `resolve`
      ],
      text(size: 11pt, weight: "bold", fill: accent)[$arrow.r^Phi$],
      block(width: 100%, fill: softbg, stroke: 0.6pt + accent, inset: 7pt, radius: 2pt)[
        *2. Semantic Spacetime $gamma(3,4)$* (`spacetime.rs`) \
        `NodeKind`: `Event`, `Thing`, `Concept` \
        `LinkKind`: `Near`, $plus.minus L$, $plus.minus C$, $plus.minus E$ \
        Dual-link cones $J^plus.minus$ & quotient $bold(G)$
      ],
    )
    #v(6pt)
    #grid(
      columns: (1fr, 1fr),
      align: center + horizon,
      gutter: 12pt,
      block(width: 100%, fill: luma(248), stroke: 0.6pt + luma(150), inset: 7pt, radius: 2pt)[
        *3. Projection & Directories* (`projection.rs`) \
        Canonical functor `project_sst` ($Phi$) \
        `CoarseGrainingDirectory` ($pi_"directory"$)
      ],
      block(width: 100%, fill: luma(248), stroke: 0.6pt + luma(150), inset: 7pt, radius: 2pt)[
        *4. Monoidal Valency & Open Laws* (`law/`) \
        `ResourceMonoid` (`+b#n`, `MaxOne`, `Unbounded`, products) \
        `ScopeLaw`: `Valency`, `Quorum`, `Unique`, `DisjointBy`, `AgreementBy`
      ],
    )
    #v(6pt)
    #block(width: 100%, fill: rgb("#f3f8f3"), stroke: 0.6pt + rgb("#2e6b3e"), inset: 6pt, radius: 2pt)[
      #align(center)[
        *Cedar VGD Lock*: 26 Lean 4 Theorems (`0 sorryAx`, zero `Mathlib`) $arrow.l.r$ 500-case Rust/Lean DRT (`0` divergences)
      ]
    ]
  ],
  caption: [Four-module architecture of `baugr` v0.2 and its mechanical Verification-Guided Development lock.],
)

= Direct Derivation from the Primary Literature

Every primitive in Baugr maps directly to definitions in seven primary arXiv papers by Jan Bergstra and Mark Burgess. @tab-derivation summarizes the exact mathematical lineage.

#figure(
  {
    set text(size: 8.5pt)
    show raw: text.with(size: 7.7pt)
    table(
      columns: (auto, 1.35fr, 1.05fr, 1.25fr),
      inset: 5pt,
      align: left,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*Source*], [*Mathematical Concept*], [*Lean 4 Definition*], [*Rust Type / API*],
      [@bergstra2008static], [Distinct promisee target vs. witness scope $sigma$; subjective assessment], [`Promise.target`, \ `Promise.scope`, \ `Assessment`], [`Promise`, `AgentSet`, \ `resolve(alpha)`],
      [@bergstra2014impositions], [Two polarities (`+b`, `-b`); impositions as offers + voluntary compliance; $a in sigma$], [`Body.offer`, `Body.use`, \ `inScope`], [`Body<O, U>`, \ `Promise::in_scope`],
      [@burgess2014spacetimes1], [Mutual-information body overlap $b_1 inter b_2$; assisted quenching; coordination $C(b)$], [`BodyAlgebra.overlap`, \ `Cond.assisted`], [`BodyAlgebra`, \ `SymmetricMeet`, \ `AgreementBy`],
      [@burgess2015spacetimes2], [Promise Valency `+b#n`; opaque vs. transparent superagents; directories $pi_"directory"$; irreducible emergence; tenancy; incomplete info], [`Hierarchy`, \ `noOpaqueWall`, \ `Cond.interior`, \ `Cond.accepted`, \ `ResourceMonoid`], [`Hierarchy`, \ `CoarseGrainingDirectory`, \ `ResourceMonoid`, \ `check_complete_information`],
      [@burgess2016spacetimes3], [Four irreducible spacetime link axes; multi-condition aggregation], [`LinkKind`, \ `Cond.atLeast`], [`LinkKind`, \ `Cond::at_least`],
      [@burgess2025sst], [Strict $gamma(3,4)$ `(e, t, c)` transition rules 1–2; antisymmetry; Couch/Burgess inference; quotient coarse-graining $bold(G)$], [`NodeKind`, `allowed`, \ `SstGraph.coarseGrain`], [`SstGraph`, \ `LinkKind::allowed`, \ `coarse_grain`],
      [@burgess2026quantitative], [Observer-local assessment $alpha_a (pi)$; self-quenching and assisted quenching], [`Assessment`, \ `Cond.selfPromise`, \ `evalCond`], [`Cond::SelfPromise`, \ `PromiseSystem::resolve`],
    )
  },
  caption: [Exact correspondence between primary Promise Theory / SST literature, Lean 4 formal specification, and Rust implementation.],
) <tab-derivation>

Three deliberate design commitments (`ADR-0018`) keep the mathematical core sharp and free of accidental complexity:

+ *Two Polarities Only (A1)*: `Body<O, U>` admits strictly `Offer(O)` ($+b$) and `Use(U)` ($-b$), making illegal polarity/body combinations structurally unrepresentable. Following @bergstra2014impositions (§1.5), impositions require no third polarity: an unaccepted imposition is an `Offer` whose voluntary compliance is modeled by the target's conditional acceptance; our Autonomy theorem (T4) proves an unaccepted offer is inert.
+ *Strict $gamma(3,4)$ Rules 1–2 (A2)*: `Expresses` ($+E$) strictly targets `Concept` nodes (`e -> c`, `t -> c`, `c -> c`). This guarantees exact antisymmetry of the transition matrix $hat(A)$, transitive closure of all four positive axes, and algebraic closure of Couch/Burgess inference rules (`Contains ; Expresses` $subset.eq$ `Expresses` and `Near ; Expresses` $subset.eq$ `Expresses`) @burgess2025sst.
+ *Exact Observer-Local Boolean Assessment (A3)*: The verified core fixes $alpha : A times P -> "Bool"$ @burgess2026quantitative, yielding sharp Knaster–Tarski least fixed points and exact Kosaraju SCC stratification. Three-valued or probabilistic assessment layers can compose cleanly above this kernel without weakening its soundness theorems.

= Promise Algebra & Conditional Quenching

Let $A$ be a finite type of autonomous agents and $P$ a finite type of promise identifiers.

== Agents, Acyclic Superagents, and Opaque Encapsulation

A dressed superagent hierarchy @burgess2015spacetimes2 (§3.3–3.7) is a pair $cal(H) = ("parent" : A -> "Option" A, "isOpaque" : A -> "Bool")$. In Rust, `PromiseSystem::contain(superagent, child)` rejects self-containment and cycles at construction (`HierarchyError`), maintaining a strict containment forest. Write $s #splus a$ (`isStrictAncAux`) if $s$ is a strict ancestor of $a$, and $s prec.eq a$ if $a = s or s #splus a$.

#thmbox("Definition", [Non-Piercing Opaque Wall])[
  Two agents $a, b in A$ respect every opaque superagent boundary, written `noOpaqueWall`$(cal(H), a, b)$, iff for every $s in A$ with $"isOpaque"(s) = "true"$:
  $ (s #splus a => s prec.eq b) quad and quad (s #splus b => s prec.eq a). $
  Strict interior members of an opaque superagent $s$ may bind freely with one another and with $s$'s own surface, but never directly across $s$'s wall to an exterior agent.
]

== Mutual-Information Overlap and Static Compatibility

A `BodyAlgebra` supplies an overlap partial operation $"overlap" : O times U -> "Option" M$ modeling Burgess's mutual-information intersection $b_1 inter b_2$ @burgess2014spacetimes1 @burgess2026quantitative. No custom attribute-matching DSL exists: callers express compatibility directly in native Rust or Lean types (e.g., voltage and wattage bounds, protocol versions, or symmetric meet-semilattices via `SymmetricMeet`).

A directed promise is a tuple $pi = ("id", a, "target", sigma, "body", C)$ where `target` and observability scope $sigma$ are agent sets and effective observability always includes the promiser: $"inScope"(pi, x) <=> (x = a) or (x in sigma)$ @bergstra2014impositions. An offer $pi_o = ("id"_o, a_o, T_o, sigma_o, "Offer"(o), C_o)$ and acceptance $pi_u = ("id"_u, a_u, T_u, sigma_u, "Use"(u), C_u)$ are *statically compatible*, written `staticBindable`$(pi_o, pi_u)$, iff:
$ a_u in T_o and "inScope"(pi_o, a_u) and a_o in T_u and "noOpaqueWall"(a_o, a_u) and "overlap"(o, u) != "none". $

== Autonomy-Grounded Conditional Formulas

In Promise Theory, an agent may condition its own promises only on information grounded in its own autonomy—never directly on an arbitrary unaccepted remote promise. Baugr's condition grammar `Cond<P>` enforces this structurally through four local atomic predicates and two combinators:

- `SelfPromise(q)`: promise $q$ by the *same* promiser $a$ is quenched and locally kept ($Q(q) and alpha_a (q)$) @burgess2026quantitative.
- `Assisted(u, k)`: the promiser's own `Use` promise $u$ is quenched and statically compatible with at least $k$ quenched offers $pi_o$ assessed kept by $a$ ($Q("id"_o) and alpha_a ("id"_o)$) @burgess2014spacetimes1.
- `Accepted(o, k)`: the promiser's own `Offer` promise $o$ is quenched and accepted by at least $k$ quenched `Use` promises $pi_u$ visible in scope to $a$ ($"inScope"(pi_u, a) and Q("id"_u) and alpha_a ("id"_u)$), directly modeling Burgess's tenancy template @burgess2015spacetimes2.
- `Interior(q)`: promise $q$ made by a strict sub-agent $b$ inside superagent $a$ ($a #splus b$) is quenched and assessed kept by $a$, enabling *irreducible emergent superagent promises* (such as 2-of-3 quorum consensus) @burgess2015spacetimes2 (Lemma L1975).
- `AtLeast(k, cs)`: monotone $k$-of-$n$ threshold combinator unifying unconditional (`k = 0, cs = []`), conjunction (`all`), disjunction (`any`), and quorums.
- `Not(c)` (`!c` in Rust via `core::ops::Not`): stratified negation enabling failover/fallback semantics (e.g., `battery:backup | !assisted(sense_grid)`).

== Stratified Fixed-Point Quenching Semantics

Given observer-local assessment $alpha : A times P -> "Bool"$, the one-step quenching operator $T_alpha (Q)(p) := "evalCond"(alpha, Q, a_p, C_p)$ updates the set of quenched promises $Q : P -> "Bool"$. Syntactic dependency extraction `condDeps` collects pairs $(d, "neg")$ recording whether $p$ depends on $d$ through an odd (`true`) or even (`false`) number of negations.

A rank assignment $"rank" : P -> NN$ is a *valid stratification* (`ValidStratification`) iff for every promise $p$ and $(d, "neg") in "condDeps"("false", C_p)$:
$ "neg" = "true" => "rank"(d) < "rank"(p), quad "and" quad "neg" = "false" => "rank"(d) <= "rank"(p). $
In Rust, `PromiseSystem::stratify` computes a minimal valid stratification via iterative Kosaraju strongly connected component (SCC) decomposition, rejecting any SCC containing a negated edge with `EvalError::UnstratifiableNegativeCycle`. Resolution proceeds stratum-by-stratum for $s = 0, dots, M$, iterating `stratumStep` from the frozen lower-stratum solution until fixed point. Finally, active cooperative bindings pair every quenched offer $pi_o$ and compatible quenched acceptance $pi_u$ where the consumer assesses the offer as kept ($alpha_(a_u) ("id"_o) = "true"$), attaching the mutual-information overlap $m = "overlap"(o, u)$.

Complementing resolution, `check_complete_information` flags any conditional promise whose target agent lies outside the observability scope $sigma$ of one of its assisting `Use` promises (`IncompleteInfoWarning`) @burgess2015spacetimes2 @burgess2026quantitative.

= Strict Semantic Spacetime $gamma(3,4)$ & Canonical Projection $Phi$

== Typed Transition Matrix and Dual-Link Normalization

Semantic Spacetime $gamma(3,4)$ @burgess2025sst classifies every node into three meta-types—*Event* ($e$, ephemeral realized timelike process), *Thing* ($t$, invariant realized spacelike agent), and *Concept* ($c$, persistent unrealized attribute or intent)—connected by four signed link meta-types: symmetric *Near* ($0$, $N$), causal *LeadsTo / Follows* ($plus.minus 1$, $plus.minus L$), spatial *Contains / ContainedBy* ($plus.minus 2$, $plus.minus C$), and expressive *Expresses / ExpressedBy* ($plus.minus 3$, $plus.minus E$).

#figure(
  {
    set text(size: 8.8pt)
    table(
      columns: (auto, auto, auto, auto, auto),
      inset: 5pt,
      align: center,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*Transition*], [`Near` ($0$)], [`+LeadsTo` ($+1$)], [`+Contains` ($+2$)], [`+Expresses` ($+3$)],
      [$e -> e$], [Yes], [Yes], [Yes], [No],
      [$e -> t$], [No], [No], [Yes], [No],
      [$e -> c$], [No], [No], [No], [Yes],
      [$t -> e$], [No], [No], [No], [No],
      [$t -> t$], [Yes], [No], [Yes], [No],
      [$t -> c$], [No], [No], [No], [Yes],
      [$c -> e$], [No], [No], [No], [No],
      [$c -> t$], [No], [No], [No], [No],
      [$c -> c$], [Yes], [No], [No], [Yes],
    )
  },
  caption: [Strict $gamma(3,4)$ positive admissibility table (`LinkKind::allowed`). Negative links (`Follows`, `ContainedBy`, `ExpressedBy`) are the exact antisymmetric converses: $"allowed"(u, r, v) = "allowed"(v, r^(-1), u)$.],
) <tab-gamma34>

In Rust, `SstGraph` maintains $gamma(3,4)$ well-formedness as an unbreakable structural invariant: `add_node` rejects conflicting re-typing (`SstError::KindConflict`) and `add_edge` enforces `LinkKind::allowed`. Furthermore, `axis_edges`, $O(V+E)$ `reachable_along`, `forward_causal_cone` ($J^+$), `reverse_causal_cone` ($J^-$), `sources`, `sinks`, `appointed_hubs`, and `branching_points` normalize dual inverse links automatically (`b -L a` contributes `(a, b)` to `+L`, and `Near` is symmetric). Quotient coarse-graining `coarse_grain` ($bold(G)$) collapses nodes under any kind-homogeneous partition, dropping interior self-loops and rejecting inhomogeneous grains (`CoarseGrainError`).

== Canonical Functor $Phi : "PromiseSystem" -> gamma(3,4)$

Burgess's Appendix A rule—_"only events can lead to events"_ @burgess2025sst—yields a canonical embedding `project_sst` ($Phi$) mapping each agent $a$ to a *Thing* (`SstNode::Agent(a)`), each promise $p$ to an *Event* (`SstNode::Promise(p)`), and each promise intent to a *Concept* (`SstNode::Intent(p)`):

- *Superagent containment*: $"Agent"(s) arrow.r^(+C) "Agent"(c)$ (`t +C t`) for each parent edge $s = "parent"(c)$.
- *Promise participation*: $"Promise"(p) arrow.r^(+C) "Agent"(a_p)$ (`e +C t`).
- *Intent expression*: $"Agent"(a_p) arrow.r^(+E) "Intent"(p)$ (`t +E c`) and $"Promise"(p) arrow.r^(+E) "Intent"(p)$ (`e +E c`).
- *Causal precedence*: $"Promise"(d) arrow.r^(+L) "Promise"(p)$ (`e +L e`) for every existing dependency $d in "condDeps"("false", C_p)$.

Crucially, projecting causal edges at the *promise-event* level rather than the *agent-thing* level eliminates false agent-level cycles in bidirectional protocols (such as `A:net -> B:dns -> A:tls`), while making causal light cones $J^plus.minus_Phi (pi)$ exact per promise. Alongside $Phi$, `directory_of` extracts the `CoarseGrainingDirectory` $pi_"directory" (S)$ separating a superagent's interior agents/promises from its exterior surface promises @burgess2015spacetimes2 (Def. L1736).

= Generalized Monoidal Valency & Open `ScopeLaw` Verification

Earlier prototypes hard-coded a closed four-variant binding discipline enum (`Exclusive`, `Broadcast`, `Partitioned`, `Budgeted`). Baugr replaces that closed enum with two strictly more general, open mathematical abstractions derived from @burgess2015spacetimes2 (§2.7) and @burgess2014spacetimes1 (L2575):

+ *Ordered Commutative Monoid (`ResourceMonoid`)*: A triple $(R, 0, plus, <=)$ where $(0, plus)$ is a commutative monoid, $<=$ is a preorder with $0 <= x$, and $plus$ is monotone in both arguments. This single trait subsumes exclusive fermionic slots (`MaxOne`, `+b#1`), broadcast bosonic slots (`Unbounded`, `+b#∞`), integer slot/wattage capacities (`u32`, `u64`, `u128`, `usize`), and arbitrary Cartesian product budgets `(R1, R2)` (e.g., `(CpuMillis, RamMiB)`).
+ *Open Composable Laws (`ScopeLaw`)*: Any user-defined invariant implements `ScopeLaw<A, P, D>` over a read-only `ResolutionView` with a typed diagnostic error implementing `core::error::Error`. Baugr ships five reusable standard instances: `ValencyLaw`, `QuorumLaw`, `UniqueProviderLaw`, `DisjointBy` (checking pairwise distinct keys `(system, binding) -> Option<K>`, e.g., `Some((host, port))` across all hosts in a single pass), and `AgreementBy` (Burgess's coordination $C(b)$ checking grouped consensus `(system, binding) -> Option<(Group, Value)>`).

= Formal Verification in Lean 4

Baugr's formal kernel (`lean/Baugr/`) uses pure Lean 4 core (`lean4` 4.35.0) with *zero `Mathlib`* and *zero external dependencies*, organized into four specification modules (`Spacetime`, `Promise`, `Projection`, `Law`) and seven mirrored proof modules under `lean/Baugr/Thm/`. Every theorem in @tab-theorems is mechanically audited by `Baugr/Audit.lean` in Nix CI with `0` warnings and `0 sorryAx`.

#figure(
  {
    set text(size: 8.3pt)
    show raw: text.with(size: 7.4pt)
    table(
      columns: (auto, 1.55fr, 1.8fr, auto),
      inset: 4.5pt,
      align: left,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*ID*], [*Lean 4 Theorem*], [*Verified Mathematical Property*], [*Axioms*],
      [T5a], [`LinkKind.inv_inv`], [Link inversion is an exact involution: $(r^(-1))^(-1) = r$.], [_(none)_],
      [T5a], [`allowed_antisym`], [Exact antisymmetry: $"allowed"(u, r, v) = "allowed"(v, r^(-1), u)$.], [`P`],
      [T5b], [`allowed_pos_trans`], [Transitive closure of all four $gamma(3,4)$ axes.], [`P`],
      [T5c], [`inference_contains_expresses`], [Couch/Burgess inference: `Contains ; Expresses` $subset.eq$ `Expresses`.], [`P`],
      [T5c], [`inference_near_expresses`], [Couch/Burgess inference: `Near ; Expresses` $subset.eq$ `Expresses`.], [`P`],
      [T5c], [`coarseGrain_wellFormed`], [Quotient functor $bold(G)$ preserves $gamma(3,4)$ well-formedness.], [`P, Q`],
      [T1a], [`evalCond_mono`, \ `quenchStep_mono`], [Positive condition & step monotonicity in $Q$.], [`P, Q`],
      [T1b–c], [`quenchIter_le_any_prefixed`, \ `quenchIter_chain`], [Knaster–Tarski leastness & ascending chain monotonicity @tarski1955fixedpoint.], [`P, Q`],
      [T2], [`cyclic_conditional_never_quenches`], [Closed circular self-dependent subsets never quench in `lfp`.], [`P, Q`],
      [T3a], [`stratified_agrees_with_positive`], [Single-stratum `evalStratified` equals `quenchIter` on positive systems.], [`P, C, Q`],
      [T3b], [`evalCond_mono_pol`, \ `stratumStep_mono`], [Polarity-indexed monotonicity under arbitrary nested `Not` within strata.], [`P, Q`],
      [T3c], [`stratumIter_fixed_point`, \ `evalStratified_fixed_point`], [Finite convergence in $<= |P|+1$ steps to a global fixed point of $T_alpha$.], [`P, C, Q`],
      [T3d], [`stratification_independent`], [*Apt–Blair–Walker Theorem*: any two valid stratifications yield the exact same fixed point.], [`P, C, Q`],
      [T4], [`autonomy_unaccepted_offer_inert`], [*Axiom of Autonomy*: an unaccepted offer/imposition cannot alter any existing condition.], [`P, Q`],
      [T5d], [`projectSst_wellFormed`], [Canonical functor $Phi : "PromiseSystem" -> gamma(3,4)$ is always well-formed.], [`P, Q`],
      [T6], [`perturbation_in_reverse_cone`], [*Crown Jewel*: assessment perturbations outside $J^-_Phi (pi)$ leave $pi$ invariant.], [`P, Q`],
      [T7a], [`noOpaqueWall_symm`, \ `opaque_non_piercing`, \ `opaque_non_piercing_inward`], [Opaque superagents mechanically block outward and inward piercing bindings.], [`P, C, Q`],
      [T7b], [`opaque_interior_perturbation_` \ `contained`], [Interior perturbations of an opaque superagent cannot affect external cones.], [`P, Q`],
      [T8a–b], [`valency_withdrawal_safe`, \ `allLaws_cons`], [Monoidal valency downward closure under withdrawal & `ScopeLaw` conjunction.], [`P, Q`],
    )
  },
  caption: [Complete catalog of 26 audited Lean 4 theorems (`0 sorryAx`). Axioms: `P` = `propext`, `Q` = `Quot.sound`, `C` = `Classical.choice`.],
) <tab-theorems>

== Flagship Unification Proofs

Two theorems stand out because they directly connect Promise Theory semantics to the Semantic Spacetime causal structure $Phi$:

#thmbox("Theorem T6", [Reverse Light Cone Perturbation Containment — `perturbation_in_reverse_cone`])[
  Let $alpha_1, alpha_2 : A times P -> "Bool"$ be two observer-local assessment functions that agree on every promise $d$ in the Semantic Spacetime reverse causal light cone of $"target"$—that is, whenever $"CausalReach"(Phi("sys"), "Promise"(d), "Promise"("target"))$. Then for any stratification `rank`, step count `steps`, and top stratum `maxS`:
  $ "evalStratified"("sys", alpha_1, "rank", "steps", "maxS", "target") = "evalStratified"("sys", alpha_2, "rank", "steps", "maxS", "target"). $
]

*Proof architecture* (`Baugr/Thm/LightCone.lean`): We first establish local congruence (`evalCond_local`), proving `evalCond` depends only on $Q(d)$ and $alpha("me", d)$ for syntactic dependencies $d in "condDeps"("false", C)$ that exist in `sys`. Since every such dependency projects to a `+LeadsTo` edge in $Phi("sys")$ (`dep_gives_leadsTo`), induction over strata $s$ and inner iterations $n$ shows that equality on the reverse light cone $J^-_Phi ("target")$ is preserved through both positive thresholds and stratified negations.

#thmbox("Theorem T3d", [Apt–Blair–Walker Stratification Independence — `stratification_independent`])[
  Let $"rank"_1, "rank"_2 : P -> NN$ be *any* two valid stratifications of `sys` bounded by $M_1, M_2$, and let $"steps" >= |"sys.promises"| + 1$. Then:
  $ "evalStratified"("sys", alpha, "rank"_1, "steps", M_1) = "evalStratified"("sys", alpha, "rank"_2, "steps", M_2). $
]

*Proof architecture* (`Baugr/Thm/Stratification.lean`): This classic result @apt1988stratified receives an unusually direct constructive proof by combining three lemmas:
+ *Polarity-indexed monotonicity* (`evalCond_mono_pol`): Under arbitrary nesting of `Not`, `evalCond` is monotone in positive dependencies and antitone in negative dependencies; since every negative dependency lies strictly below stratum $s$ where $Q$ is frozen, `stratumStep` is monotone on stratum $s$ (`stratumStep_mono`).
+ *Pigeonhole finite fixed-point convergence* (`stratumIter_fixed_point`, `evalStratified_fixed_point`): Because the quenched count on the finite list `sys.promises` is non-decreasing and bounded by $|P|$, the ascending chain must repeat within $|P|$ steps, after which `quenchStep_ext_promises` freezes it permanently into a global fixed point of $T_alpha$.
+ *Symmetric light-cone induction*: Every causal path in $Phi("sys")$ is monotone in any valid rank (`causalReach_rank_le`). By induction on $k = "rank"_1 (p) + "rank"_2 (p)$, for any $p$ we construct the pre-fixed point $G(x)$ equal to `base` below $"rank"_1 (p)$, equal to $F_2 (x)$ on $J^-_Phi (p)$ at $"rank"_1 (p)$, and `true` outside $J^-_Phi (p)$. Knaster–Tarski leastness (`stratumIter_le_any_prefixed`) yields $F_1 (p) <= F_2 (p)$, and symmetry yields $F_2 (p) <= F_1 (p)$.

= Verification-Guided Development: Rust $arrow.l.r$ Lean 4 Bridge

Following AWS Cedar Verification-Guided Development @cutler2024cedar, Baugr avoids fragile automated code extraction in favor of an idiomatic `#![no_std]` Rust crate mechanically locked to the Lean 4 specification via *Differential Randomized Testing (DRT)*.

- *Production Rust optimizations & invariants*: The Rust crate (`src/`, 10 modules, 67–462 LOC each) precomputes a static compatibility index `CompatIndex` once per `stratify()`, `resolve()`, or `project_sst()` call so neither `no_opaque_wall` nor `BodyAlgebra::overlap` is re-evaluated inside Knaster–Tarski loops. Both `SstGraph::add_node` and `PromiseSystem::contain` enforce structural invariants at mutation time, and all 9 error types implement `#![no_std]` `core::error::Error`.
- *500-case DRT oracle* (`tests/drt.rs` $arrow.l.r$ `Baugr/Oracle/Main.lean`): A deterministic zero-dependency `xorshift64*` generator builds 500 randomized stratifiable Promise Systems with random opaque/transparent hierarchies, 3-bit bitmask mutual-information overlap $b_1 inter b_2 = (o \& u) != 0$, positive dependency cycles, nested `AtLeast` thresholds, stratified `Not` fallbacks, and observer-local broken assessments. Each case is evaluated by both Rust and the compiled Lean 4 `baugr-oracle` binary, asserting *zero divergences* across `QUENCHED`, `BINDINGS` (including exact overlap bitmasks), and projected $gamma(3,4)$ `SST` edges (`0.25 s` release), alongside randomized checks of T5d, T6, and T7a.

= Cross-Domain Evaluation & Verification Gates

To verify genuine domain neutrality, Baugr ships three standalone zero-dependency runnable examples (`examples/`) and an automated L0 purity test (`tests/domains.rs`) asserting that zero domain-specific or OS I/O tokens appear anywhere in `src/`:

+ *Microgrid Power Failover (`examples/microgrid.rs`)*: Models 230V mains, battery sensing, stratified backup failover (`!Cond::assisted("bat:sense_grid")`), observer-local split blackouts ($alpha_"battery" ("grid") != alpha_"factory" ("grid")$), and wattage `ValencyLaw(1500W)`.
+ *Opaque Raft Consensus (`examples/raft.rs`)*: Models an opaque superagent `raft` containing replicas `{n1, n2, n3}` with an irreducible 2-of-3 quorum surface promise (`Cond::at_least(2, [Interior(..)])`), mechanically blocking exterior piercing to `n1` and isolating unrelated promises outside $J^-_Phi ("client:app")$.
+ *Multi-Tenant Cloud Tenancy (`examples/tenancy.rs`)*: Models Burgess's tenancy template (`+slot | terms` and `+power | Accepted(slot)`), checks per-host TCP port uniqueness across all hosts simultaneously via a single `DisjointBy`, and verifies fleet-wide protocol version agreement $C(b)$ via `AgreementBy`.

The entire repository is verified offline by `nix flake check -L` across seven hermetic gates: `fmt`, `clippy` (`pedantic = "deny"`, `unsafe_code = "forbid"`, `unwrap`/`expect`/`indexing`/`arithmetic`/`as` denied), `doc` (`RUSTDOCFLAGS="--deny warnings"`), `test` (unit, domain, purity, 500 property cases, and 4 executable doctests), `lean-audit` (26 theorems, `0 sorryAx`), `drt` (500/500 Rust $arrow.l.r$ Lean equivalence), and `paper` (offline Typst PDF compilation).

#v(0.4em)
#bibliography("refs.bib", style: "ieee")
