// Baugr — A Formally Verified Algebra of Voluntary Coordination in Semantic Spacetime
// Build offline with: `typst compile paper/baugr.typ paper/baugr.pdf` or `nix build .#paper`

#set document(
  title: "Baugr: A Formally Verified Algebra of Voluntary Coordination in Semantic Spacetime",
  author: "LW-54",
)

#set page(
  paper: "a4",
  margin: (x: 2.0cm, y: 1.95cm),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 8.4pt, fill: luma(105))
      _Baugr — A Formally Verified Algebra of Voluntary Coordination in Semantic Spacetime_
      #h(1fr)
      #counter(page).display()
    ]
  },
  footer: [],
)

#set text(font: "Libertinus Serif", size: 9.8pt, lang: "en")
#set par(justify: true, leading: 0.57em)
#set heading(numbering: "1.1")
#show heading: set block(sticky: true)
#show heading.where(level: 1): it => {
  v(0.75em, weak: true)
  set text(size: 12.2pt, weight: "bold", fill: rgb("#163858"))
  it
  v(0.32em, weak: true)
}
#show heading.where(level: 2): it => {
  v(0.55em, weak: true)
  set text(size: 10.4pt, weight: "bold", fill: rgb("#1f4e79"))
  it
  v(0.22em, weak: true)
}
#show raw.where(block: true): it => block(
  width: 100%,
  fill: luma(248),
  stroke: (left: 2pt + rgb("#1f4e79"), rest: 0.4pt + luma(220)),
  inset: (x: 8pt, y: 5pt),
  radius: 2pt,
  breakable: true,
  {
    set par(leading: 0.45em)
    text(size: 7.3pt, it)
  },
)
#show raw.where(block: false): text.with(size: 8.6pt)

// Clean left-aligned cells inside all tables (prevents stretched spaces or overflows)
#show table.cell: it => {
  set par(justify: false, leading: 0.50em)
  it
}

#let accent = rgb("#1f4e79")
#let deep = rgb("#163858")
#let softbg = rgb("#f4f7fa")
#let warmbg = rgb("#fdf8f0")
#let warmedge = rgb("#a86414")
#let greenbg = rgb("#f2f8f3")
#let greenedge = rgb("#2b6e3f")
#let rosebg = rgb("#fdf2f2")
#let roseedge = rgb("#9e2a2b")
#let splus = $attach(prec, tr: +)$

#let defbox(kind, label, body) = block(
  width: 100%,
  fill: softbg,
  stroke: (left: 2.5pt + accent, rest: 0.4pt + luma(210)),
  inset: (x: 9pt, y: 7pt),
  radius: 2pt,
  breakable: false,
  [
    #set par(leading: 0.72em)
    #text(weight: "bold", fill: accent)[#kind (#label).] #body
  ],
)

#let lawbox(num, name, body) = block(
  width: 100%,
  fill: greenbg,
  stroke: (left: 2.5pt + greenedge, rest: 0.4pt + rgb("#c6dec9")),
  inset: (x: 9pt, y: 7pt),
  radius: 2pt,
  breakable: false,
  [
    #text(weight: "bold", fill: greenedge)[Law #num — #name.] #body
  ],
)

// ============================================================================
// Title & Abstract
// ============================================================================

#align(center)[
  #text(size: 16.5pt, weight: "bold", fill: deep)[
    Baugr: A Formally Verified Algebra of \
    Voluntary Coordination in Semantic Spacetime
  ]
  #v(0.45em)
  #text(size: 9.8pt, fill: luma(75))[
    Promise Theory, Strict $gamma(3,4)$ Causal Geometry, and Four Universal Laws \
    `baugr` v0.4 — `https://github.com/LW-54/baugr`
  ]
]

#v(0.65em)

#block(
  width: 100%,
  fill: luma(248),
  stroke: 0.5pt + luma(200),
  inset: 10.5pt,
  radius: 3pt,
)[
  #align(center)[#text(weight: "bold", size: 9.5pt, fill: deep)[Abstract]]
  #v(0.3em)
  #set text(size: 9.2pt)
  Decentralized systems—from electrical microgrids and fault-tolerant consensus clusters to multi-tenant cloud fabrics—are composed of autonomous actors that cannot coerce one another and rarely agree on a single global view of the world. Yet most formal modeling tools inherit two centralizing fictions: top-down *obligation* (where an environment or authority compels behavior) and *global objective truth* (where every component shares one view of what is working). Conversely, unrestricted rule languages such as raw Datalog can encode decentralized systems, but offer no structural guarantee that a model respects autonomy, abstraction boundaries, or blast-radius locality.

  *Baugr* is a minimal, domain-agnostic mathematical model—and machine-checked formal library—of *voluntary coordination in causal spacetime*, derived directly from the Promise Theory and Semantic Spacetime $gamma(3,4)$ foundations of Jan Bergstra and Mark Burgess. By supporting both static conditional promises (`±b | C`) and symmetric *value-dependent conditional promises* (`±f(obs) | C`—covering both derived offers `+f(obs)` and derived acceptances `-f(obs)`) restricted strictly to four autonomy-grounded local observations—and canonically projecting every promise system into strict Semantic Spacetime (mapping agents to _Things_, promises to _Events_, and intents to _Concepts_)—Baugr turns four foundational guarantees of decentralized engineering into *universal theorems* holding automatically for every expressible system: *Non-Coercion* (external unaccepted impositions are unconditionally inert), *Boundary Integrity* (opaque superagents form topological event-horizon vertex cuts across arbitrarily nested hierarchies), *Causal Locality* (observer-local failures outside a promise's reverse causal light cone cannot alter its resolved body value, even across failover negation and value derivation), and *Order Independence* (any valid stratification converges finitely to the same canonical value state, proved constructively via spacetime light cones). We machine-check all 30 theorems in pure Lean 4 (`0 sorryAx`, zero external proof libraries), position Baugr against adjacent formalisms, and realize the calculus as a zero-dependency executable engine mechanically locked to its formal specification.
]

#v(0.45em)

// ============================================================================
// Section 1
// ============================================================================

= Introduction: The Problem of Voluntary Coordination

Modern distributed systems are rarely governed by a single omniscient controller. Power inverters decide locally whether to supply backup current; consensus replicas vote based on the messages they individually received; sovereign tenants accept or reject service offerings according to local policy; software teams expose public interfaces while refactoring internal subsystems behind firm encapsulation boundaries.

When we try to reason formally about such systems, conventional tools pull us toward two quiet centralizing fictions:

+ *The Fiction of Coercion and Obligation.* Imperative orchestration, access-control scripts, and classic Assume–Guarantee contracts @benveniste2018contracts treat coordination as obligation: if an assumption holds, a component is *required* to satisfy its guarantee. In genuinely autonomous systems, however, no agent can force another agent's behavior @bergstra2008static @bergstra2014impositions. An unsolicited command—what Promise Theory calls an *imposition*—has zero effect unless the recipient voluntarily chooses to accept it.
+ *The Fiction of Single Global Truth.* Classical logic models assume a single world state in which a service is either up or down. In reality, failures are *observer-local* @burgess2026quantitative: during a partial power outage or network partition, a battery controller may observe the electrical mains as dead while a factory on a separate feeder observes the exact same mains as healthy.

One might try to encode autonomy and local observers inside a general-purpose logic language such as Datalog or relational logic. That approach works for one model at a time, but surrenders the deepest benefit of a formal calculus: *structural guarantees*. In an unrestricted rule language, nothing stops a rule from peeking across an encapsulation wall, reacting to an unaccepted imposition, or creating an invisible global dependency—so every new system must be re-audited from scratch.

== Baugr's Thesis: Structural Autonomy in Causal Spacetime

Baugr takes the opposite approach. Instead of building an unconstrained language and auditing away accidental coupling later, Baugr defines a small, closed algebra of *voluntary promises* coupled by a canonical functor $Phi$ to *strict Semantic Spacetime* $gamma(3,4)$ @burgess2025sst—where $gamma(3,4)$ names Burgess's typed graph family with *3* ontological node kinds (_Events_, _Things_, _Concepts_) and *4* signed link axes (_Near_, _LeadsTo_, _Contains_, _Expresses_). Every construct in the algebra is drawn directly from seven primary papers of Bergstra and Burgess @bergstra2008static @bergstra2014impositions @burgess2014spacetimes1 @burgess2015spacetimes2 @burgess2016spacetimes3 @burgess2025sst @burgess2026quantitative. Because the condition grammar admits *only* observations grounded in an agent's own autonomy and superagent boundaries, *four universal laws* emerge automatically for *every* system expressible in Baugr—without per-model proof effort:

#block(
  width: 100%,
  fill: softbg,
  stroke: 0.6pt + accent,
  inset: 9pt,
  radius: 3pt,
  breakable: false,
)[
  #set par(justify: false)
  #text(weight: "bold", fill: deep)[The Four Universal Laws of Baugr]
  #v(0.25em)
  + *Non-Coercion (Autonomy):* Adding an unaccepted offer or imposition from an external agent can never alter the activation or derived body value of any existing promise—unconditionally, even across negation.
  + *Boundary Integrity (Event-Horizon Vertex Cut):* An opaque superagent acts as a hermetic event horizon: no binding or `+LeadsTo` causal edge can cross its wall (even from an enclosing parent superagent), and every causal path across it must pass through an explicit surface promise.
  + *Causal Locality (Light-Cone Containment):* No observer-local failure outside a promise's reverse causal light cone $J^-_Phi (pi)$ can change $pi$'s resolved body—even across non-monotonic failover and value-derivation rules.
  + *Order Independence (Canonicality):* Even with nested failover negation and value-derived bodies, every valid stratification converges in at most $|P|+1$ steps to the exact same steady state.
]

== Discipline of Scope

Baugr is intentionally small and strictly domain-agnostic. It models *voluntary intent, static and value-derived conditional activation (`±b | C`, `±f(obs) | C`), observer-local assessment, hierarchical boundaries, and causal geometry*. It refuses to hardcode domain-specific resource orderings, schedulers, or external "law" taxonomies—because bindings in general need not be quantifiable or ordered, and domain invariants (resource budgets, exclusive leases, quorums, protocol alignment) emerge cleanly from autonomous promises and conditions themselves. It likewise excludes wire protocols, multi-step temporal interleaving (where tools such as TLA+ and Quint excel @lamport2002tla), authorization policy languages, configuration syntax sugar, and domain vocabularies. Higher-level systems—whether energy grids, distributed platforms, or multi-tenant infrastructure—compose Baugr as a clean mathematical kernel without inheriting foreign assumptions.

// ============================================================================
// Section 2
// ============================================================================

= Intuition First: Two Running Examples

Before writing formal definitions, we ground every concept in Baugr using two completely different autonomous systems: a physical *hospital microgrid* and a distributed *consensus cluster*. We will revisit both throughout the paper.

== Example 1: The Autonomous Hospital Microgrid

Consider an electrical site shared by independent actors: the municipal `mains`, an on-site backup battery `bank` (an opaque superagent containing three 800 W internal cells), a high-priority `hospital` ward (1000 W), a lower-priority `clinic` (800 W) with a local diesel generator and secondary `aux` supplier, and an adjacent `factory`.

- *Voluntary bilateral alignment (`+` and `-`):* `mains` voluntarily *offers* 230 V power up to 5000 W (`+power`). That offer alone powers nothing; `hospital` must independently declare that it *accepts* 230 V power (`-draw`). Cooperation occurs only where an offer and an acceptance meet with compatible physical parameters (matching voltage and overlapping wattage)—a *mutual-information overlap* $b_1 inter b_2$ @burgess2014spacetimes1.
- *Failover and symmetric value-derived coordination (`±f(obs) | C`):* `bank` accepts a grid-sensing signal (`-sense`) and voluntary power requests (`-recv_req`). When `mains` fails and at least 2 of its 3 interior cells are healthy, `bank` activates via stratified negation (`not assisted(sense)`) and uses a *derived offer* (`+f(obs) | C`) to sum its healthy interior cells (1600 W if one cell crashed; 2400 W if all three live) and emit *separate concrete offers*: `+Power(1000 W)` to `hospital` and the exact leftover `+Power(600 W)` to `clinic`. `clinic` then decides *autonomously* how to respond: a partial clinic accepts 600 W and uses a *derived acceptance* (`-f(obs) | C`) to draw the exact 200 W residual shortfall from `aux` (staying silent when already satisfied), whereas a strict clinic (`min 800 W`) rejects 600 W and fires its own #box[`!assisted(draw)`] diesel backup.
- *Observer-local subjectivity:* Suppose a local breaker trips on the hospital feeder while the industrial feeder stays live. Now `bank` assesses `mains`'s offer as *broken* ($alpha_"bank" ("mains") = bot$), whereas `factory` assesses the *very same* `mains` offer as *kept* ($alpha_"factory" ("mains") = top$). In a single-truth logic this state is contradictory; in Baugr it is ordinary reality. `bank` activates backup grants for `hospital` and `clinic`, while `factory` continues reading healthy mains—and crucially, nothing that happens to `factory`'s monitoring can ever perturb `hospital`'s operation, because `factory` lies outside `hospital`'s reverse causal light cone.
- *Constraints via conditions, not bolted-on laws:* Capacity limits, passive overload monitors (a Stratum-1 promise observing `Obs::accepted`), exclusive leases, and quorums require zero external scheduler or numeric-monoid assumptions in the kernel: every domain expresses its own coordination policy directly through voluntary promises, `overlap`, and `±f(obs) | C`.

== Example 2: The Opaque Consensus Cluster

Now consider a distributed storage service `cluster` built internally from three independent replica nodes $\{n_1, n_2, n_3\}$ serving an external `client` alongside an unrelated `metrics` observer.

- *Opaque boundary (recursive Russian-doll encapsulation):* `cluster` is declared an *opaque superagent* containing $\{n_1, n_2, n_3\}$ @burgess2015spacetimes2. Inside the wall, the replicas freely exchange replication promises with one another. Outside the wall, `client` is structurally prevented from binding directly to replica $n_1$—and even if `cluster` itself is placed inside an enclosing `datacenter` superagent, `datacenter` may observe `cluster`'s surface promises but cannot pierce `cluster`'s opaque wall to inspect $n_1$.
- *Irreducible emergence:* No single replica can promise fault-tolerant durability on its own. Instead, `cluster` itself makes a *surface promise* of durable writes (`+durable`) conditioned on *at least 2 of its 3 interior replicas* keeping their internal replication promises (`atLeast(2, [interior(n1), interior(n2), interior(n3)])`).
- *Absorbing internal churn:* If replica $n_1$ crashes, `cluster` still observes $n_2$ and $n_3$ keeping their promises, so the 2-of-3 quorum holds and `client` observes zero disruption. Even if a fourth internal helper inside `cluster` is unreferenced by the surface promise, its failure is mechanically guaranteed not to cross the opaque boundary.

#figure(
  kind: image,
  supplement: [Figure],
  block(
    width: 100%,
    inset: 9pt,
    stroke: 0.5pt + luma(195),
    radius: 3pt,
    fill: white,
  )[
    #set par(justify: false)
    #set text(size: 8.4pt)
    #grid(
      columns: (1.55fr, auto, 1.0fr),
      align: center + horizon,
      gutter: 8pt,
      // Left: Opaque Superagent box
      block(
        width: 100%,
        fill: softbg,
        stroke: (paint: accent, thickness: 1.5pt, dash: "dashed"),
        inset: 8pt,
        radius: 4pt,
      )[
        #align(left)[#text(weight: "bold", fill: accent)[Opaque Superagent `cluster` (Event Horizon)]]
        #v(4pt)
        #grid(
          columns: (1fr, 1fr, 1fr),
          gutter: 5pt,
          block(width: 100%, fill: rosebg, stroke: 0.7pt + roseedge, inset: 5pt, radius: 2pt)[
            *`n1`* (failed)\
            $alpha = bot$
          ],
          block(width: 100%, fill: greenbg, stroke: 0.7pt + greenedge, inset: 5pt, radius: 2pt)[
            *`n2`* (kept)\
            $alpha = top$
          ],
          block(width: 100%, fill: greenbg, stroke: 0.7pt + greenedge, inset: 5pt, radius: 2pt)[
            *`n3`* (kept)\
            $alpha = top$
          ],
        )
        #v(5pt)
        #block(width: 100%, fill: white, stroke: 0.8pt + greenedge, inset: 5pt, radius: 2pt)[
          *Emergent Surface Offer* `+durable`\
          `AtLeast(2, [Interior(n1..n3)])` #text(fill: greenedge, weight: "bold")[$arrow.r$ Quenched ($2 >= 2$)]
        ]
      ],
      // Middle arrows
      stack(
        spacing: 9pt,
        align(center)[
          #text(size: 8pt, fill: roseedge, weight: "bold")[piercing `n1`]\
          #text(size: 10pt, fill: roseedge, weight: "bold")[$arrow.r.not$ BLOCKED]
        ],
        align(center)[
          #text(size: 8pt, fill: greenedge, weight: "bold")[surface `+durable`]\
          #text(size: 10pt, fill: greenedge, weight: "bold")[$arrow.l.r$ BOUND]
        ],
      ),
      // Right: Exterior agents
      stack(
        spacing: 8pt,
        block(width: 100%, fill: luma(248), stroke: 0.7pt + luma(140), inset: 6pt, radius: 2pt)[
          *External `client`*\
          `-use_durable` (binds surface)\
          `-pierce_n1` (blocked by wall)
        ],
        block(width: 100%, fill: warmbg, stroke: 0.6pt + warmedge, inset: 6pt, radius: 2pt)[
          *Unrelated `metrics`*\
          Outside $J^-_Phi ("client")$\
          (provably isolated)
        ],
      ),
    )
  ],
  caption: [Conceptual illustration of an opaque superagent. Internal replicas `{n1, n2, n3}` coordinate behind a non-piercing wall; an emergent 2-of-3 surface promise survives `n1`'s failure while external piercing attempts are structurally rejected.],
) <fig-opaque>

Every mathematical piece in the rest of this paper exists purely to make scenarios like these exact, composable, and provably well-behaved across *any* domain.

// ============================================================================
// Section 3
// ============================================================================

= The Promise Algebra

Let $A$ be a finite set of autonomous *agents* and $P$ a finite set of *promise identifiers*. A *Promise System* $cal(S)$ specifies a hierarchy of agents, a domain algebra of promise bodies, and a finite collection of directed conditional promises.

== Polarity, Mutual Information, and Visibility Scope

Every promise carries one of exactly *two polarities* @bergstra2014impositions:
- An *Offer* $+o$ (giving/providing a behavior $o in O$), or
- A *Use* $-u$ (accepting/relying on a behavior $u in U$).

Why not add a third polarity for commands or impositions? Bergstra and Burgess @bergstra2014impositions (§1.5) show that an imposition requires no separate primitive: an agent imposing a request simply emits an offer-like proposal, and *compliance* happens if and only if the recipient voluntarily issues an acceptance. By restricting the algebra to `+` and `-`, coercion becomes structurally inexpressible—a property we prove formally as *Law I (Autonomy)*.

Rather than inventing a rigid predicate language to decide when an offer satisfies an acceptance, Baugr parameterizes the entire algebra over a domain-supplied *body algebra*: a partial mutual-information overlap operation @burgess2014spacetimes1 @burgess2026quantitative
$ inter : O times U -> "Option"(M), $
returning the shared commitment $m in M$ when $o$ and $u$ are compatible, and `none` otherwise.

*Why $+o$ and $-u$ instead of uniform $plus.minus b$?* Classical Promise Theory writes $+b_1$ and $-b_2$ with overlap $b_1 inter b_2$ over a single homogeneous space $B$ of promise bodies. In real engineering domains, however, offers and acceptances frequently have *asymmetric shapes*: in the microgrid, a power source offers a *capacity ceiling* (`230 V, max 5000 W` $in O$), whereas a load requests a *specific draw* (`230 V, need 900 W` $in U$), and their overlap is the *allocated power* (`900 W` $in M$); similarly, a TLS server offers a version *range* while a client states a *minimum requirement*. Separating $(O, U, M)$ accommodates both worlds cleanly: whenever a domain truly is symmetric (e.g., matching capability sets or meet-semilattices), setting $O = U = M = B$ recovers classical $plus.minus b$ and $b_1 inter b_2$ identically.

A directed promise is a six-tuple $pi = ("id", a, T, sigma, beta, C)$ where $a in A$ is the promiser, $T subset.eq A$ is the set of intended *targets* (promisees), $sigma subset.eq A$ is the *visibility scope* (who can observe the promise), $beta in "Body"("Spec"(O), "Spec"(U))$ encodes polarity *once* paired orthogonally with either a static constant payload (`Spec::Fixed`) or a *value-derived* payload (`Spec::Derived(obs, f)` over a canonical deduplicated observation set `obs`, §3.3), and $C$ is a boolean activation condition. Following @bergstra2008static @bergstra2014impositions, targets and observability scope are kept distinct: an agent may target one recipient while broadcasting visibility to an auditor, or hide a promise from third parties. Every promiser automatically observes its own promises:
$ "inScope"(pi, x) quad <=> quad (x = a) or (x in sigma). $

== Superagent Hierarchies and Opaque Event Horizons

Autonomous agents group into recursive *superagents* @burgess2015spacetimes2 (§3.3–3.7). A hierarchy $cal(H) = ("parent", "opaque")$ assigns each agent at most one parent (enforcing a strict acyclic forest with idempotent registration and rejecting silent reparenting or cycles by construction) and marks each superagent either *transparent* (a logical grouping whose interior members remain directly reachable) or *opaque* (an encapsulated unit with a hard boundary).

Write $s #splus a$ if $s$ is a strict ancestor of $a$ in $cal(H)$, and $s prec.eq a$ if $a = s$ or $s #splus a$.

#defbox("Definition 1", [Non-Piercing Opaque Wall])[
  Two agents $a, b in A$ respect every opaque boundary in $cal(H)$, written $"noOpaqueWall"(cal(H), a, b)$, if and only if for every $s in A$ with $"opaque"(s) = top$:
  $ (s #splus a => s prec.eq b) quad and quad (s #splus b => s prec.eq a). $
]

This symmetric, reflexive relation captures exact Russian-doll encapsulation: agents strictly inside an opaque superagent $s$ may cooperate freely with one another and with $s$'s own boundary, but can never form a direct link to any agent outside $s$—not even to an enclosing ancestor superagent above $s$.

Combining bilateral targeting, visibility, opaque boundaries, and static body/channel compatibility yields the conservative predicate $"mayBind"(pi_o, pi_u)$ governing stratification and causal projection:
$ "structBindable"(pi_o, pi_u) quad <=> quad "isOffer"(pi_o) and "isUse"(pi_u) and a_u in T_o and "inScope"(pi_o, a_u) and a_o in T_u and "noOpaqueWall"(a_o, a_u). $
When both $pi_o$ and $pi_u$ have fixed payloads $(+o, -u)$, $"mayBind"$ checks exact $o inter u != "none"$; when either endpoint is value-derived, $"mayBind"$ consults an optional channel-compatibility filter (`may_overlap` / `ruleCompat`, defaulting to `true`), keeping multi-protocol derived graphs (such as `Request` $arrow.r$ `Grant` $arrow.r$ `Ack`) acyclic and their causal light cones sharp, while runtime overlap always gates on $"mayBind"$ to preserve 100% formal soundness.

== Autonomy-Grounded Conditions and Value-Derived Promises (`±f(obs) | C`)

How may an agent condition a promise—or compute its offered/accepted value—from the world around it? In an arbitrary rule engine, agent $a$ could peek across an opaque wall or react to an unaccepted imposition. Baugr prohibits such non-autonomous peeking by construction. Both boolean conditions $C$ and value-derivation observation selectors `Obs` are restricted strictly to *four autonomy-grounded local observations*:

+ *Self-reliance* (`Self(q)`): promise $q$ made by *the same agent $a$* is active and locally kept by $a$ ($alpha_a (q) = top$) @burgess2026quantitative.
+ *Assisted reliance* (`Assisted(u, k)` / `Obs::Assisted(u)`): $a$'s own *Use* promise $u$ is active, locally kept ($alpha_a (u) = top$), and compatible with active offers $pi_o$ that $a$ locally assesses as kept ($alpha_a ("id"_o) = top$) @burgess2014spacetimes1.
+ *Voluntary tenancy / acceptance* (`Accepted(o, k)` / `Obs::Accepted(o)`): $a$'s own *Offer* promise $o$ is active, locally kept ($alpha_a (o) = top$), and accepted by active *Use* promises $pi_u$ visible in scope to $a$ and locally assessed kept ($alpha_a ("id"_u) = top$) @burgess2015spacetimes2.
+ *Visible superagent interior emergence* (`Interior(q)`): promise $q$ made by a strict sub-agent $b$ inside superagent $a$ with *no intervening opaque wall* ($a #splus b and "noOpaqueWall"(a, b)$) is active and assessed kept by $a$ ($alpha_a (q) = top$) @burgess2015spacetimes2. Thus an enclosing superagent can inspect transparent sub-groups and an opaque child's *surface*, but can never pierce an inner opaque boundary.

Boolean conditions $C$ combine these four atoms via two combinators: *monotone threshold* `AtLeast(k, [c_1, ..., c_n])` (unifying unconditional promises $k=0$, conjunction $k=n$, disjunction $k=1$, and quorums @burgess2016spacetimes3) and *stratified negation* `not c` (enabling autonomous failover such as `not Assisted(sense, 1)` or exact cardinality bounds such as `Assisted(u, 1)` $and$ `not Assisted(u, 2)`).

*Symmetric value-dependent conditional promises (`+f(obs) | C` and `-f(obs) | C`):* Realizing Burgess's functional tenancy law $+f(C, R) | -R$ @burgess2015spacetimes2 (§4.1) symmetrically across *both* polarities, neither an offer nor an acceptance need carry a static constant payload. A *derived* offer (`+f(obs) | C`) or *derived* use (`-f(obs) | C`) declares a canonical *deduplicated set* `obs` (preventing double-counting by construction) drawn from the exact same four autonomy-grounded selectors and a pure deterministic function $f : "LocalObs" -> "Option"(O)$ (or $"Option"(U)$). Notice what this single symmetric primitive unlocks with *zero* special-case law or scheduler machinery in the kernel:
- *Provider-side allocation & exclusive leasing (`+f(obs) | C`):* Consumers voluntarily promise requests (`+Request(...)` or `+PortReq(80)`); the provider accepts them (`-AcceptRequests`) and derives separate concrete grants (`+Power(1000W)` to `hospital`, leftover `+Power(600W)` to `clinic`, proportional shares, FCFS, or exclusive port leases granting TCP port 80 to at most one tenant)—with zero assumption that bindings are numeric or ordered.
- *Consumer-side residual & peer-coordinated acceptance (`-f(obs) | C`):* A consumer observes what it already received (`Obs::assisted("clinic:draw")`) or what a peer broadcast, and dynamically sizes its acceptance from a secondary supplier (`-Draw(200W)` from `aux`, withdrawing to `None` once satisfied).
- *Emergent superagent capacity & declarative monitors (`+f(obs) | C`):* An opaque battery bank sums its healthy interior cells (`1600 W` with 2 cells, `2400 W` with 3), and any agent or superagent can expose a Stratum-1 health/limit monitor observing `Obs::accepted` or `Obs::interior` without cycles or external law wrappers.

== Observer-Local Assessment and Stratified Value Quenching

Promises express *intent*; whether a promise is actually *kept* is always judged subjectively by an observer @bergstra2008static @burgess2026quantitative. Baugr represents the current state of the world as an *observer-local assessment function*:
$ alpha : A times P -> \{bot, top\}, $
where $alpha_a (p) = top$ means *"agent $a$ assesses promise $p$ as kept."* Crucially, $alpha_a (p)$ and $alpha_b (p)$ need not agree—and self-assessment $alpha_a (u)$ is checked consistently across `Self`, `Assisted`, `Accepted`, `Obs`, and active bindings (so if `bank`'s own sensor promise fails, `Assisted(sense)` becomes $bot$).

Because derived promises compute concrete bodies, the resolved state is a partial map from promises to their effective bodies:
$ S : P -> "Option"("Body"(O, U)), $
ordered by the flat information order $S_1 <= S_2 quad <=> quad forall p, b, thin S_1 (p) = "some"(b) => S_2 (p) = "some"(b)$ (where `none` means unquenched and $"some"(b)$ means quenched with body $b$).

- *Positive single-stratum systems & circularity rejection:* When no condition contains negation and no promise carries `Obs` value dependencies, the one-step quenching operator $T_alpha (S)$ is monotone under $<=$. By Tarski's theorem @tarski1955fixedpoint, iterating $T_alpha$ from $bot = (lambda p. thin "none")$ reaches the *unique least fixed point* $"lfp"(T_alpha)$ in at most $|P|+1$ steps, mechanically rejecting self-justifying circular promises.
- *Autonomy-guarded stratification across negation and value derivation:* Because both negation (`not`) and arbitrary body derivation (`f(obs)`) can be non-monotonic, we extract the unified dependency set $"promiseDeps"(pi) = "condDeps"(a_pi, C_pi) union "obsDeps"(a_pi, beta_pi)$, guarding every atom on its static ownership, polarity, and $"noOpaqueWall"$ checks (so structurally dead or wall-blocked references never emit phantom causal edges) and marking every odd-parity negated edge *and* every `Obs` value edge as *strict* (`true`). A rank assignment $"rank" : P -> NN$ is a *valid stratification* iff:
  $ (d, "strict") in "promiseDeps"(pi) => "rank"(d) < "rank"(pi), quad "and" quad (d, "non-strict") in "promiseDeps"(pi) => "rank"(d) <= "rank"(pi). $
  Any system free of strict cycles admits a valid stratification; any system containing a negated cycle or cyclic value-derivation loop is rejected as `UnstratifiableCycle`. Within each stratum $s$, every negated dependency *and* every `Obs` input lies strictly below $s$ and is already frozen, so every derived promise's candidate body is *constant* throughout stratum $s$. Hence the per-stratum operator stays monotone under $<=$ and converges in $<= |P|+1$ steps to a global fixed point $S^* = T_alpha (S^*)$.

Once $S^*$ is computed, the *active cooperative bindings* are all pairs $(pi_o, pi_u)$ with $"mayBind"(pi_o, pi_u)$, resolved bodies $S^* ("id"_o) = "some"(+o)$ and $S^* ("id"_u) = "some"(-u)$, non-empty runtime overlap $m = o inter u$, and local consumer assessment $alpha_(a_u) ("id"_o) = alpha_(a_u) ("id"_u) = top$.

Finally, static *complete-information* checks (covering all surface dependencies across `Self`, `Assisted`, `Accepted`, and `Obs`, while respecting opaque `Interior` hiding) and `lint()` diagnostics flag dangling IDs, wrong promisers, polarity mismatches, non-interior or opaque-wall-blocked references (`OpaqueWallBlocked`), unregistered explicit targets (`UnknownTargetAgent`), and permanently *null-potent* thresholds across `Assisted`, `Accepted`, and `AtLeast(k, cs)` (`UnsatisfiableMinCount`) before deployment.

// ============================================================================
// Section 4
// ============================================================================

= The Geometry of Semantic Spacetime $gamma(3,4)$

So far we have defined an *operational* semantics: given promises and assessments, which promises activate and bind? Now we turn to the second pillar of Baugr: *causal geometry*.

== Three Node Kinds and Four Signed Axes

Semantic Spacetime @burgess2016spacetimes3 @burgess2025sst observes that structured knowledge and distributed processes do not live in an untyped graph. Every entity falls into one of *three disjoint ontological kinds*:

- *Event* ($e$): an ephemeral, timelike happening or process realization (a promise activation, a message exchange, a failover transition).
- *Thing* ($t$): an enduring, spacelike physical or logical carrier of agency (a battery, a server, a superagent cluster).
- *Concept* ($c$): a persistent, unrealized attribute, type, or intent (a voltage specification, a durability SLA, a protocol name).

Nodes are connected by *four irreducible signed link axes* @burgess2016spacetimes3 @burgess2025sst:
+ *Near* ($0$, symmetric): proximity, equivalence, or similarity ($N$).
+ *LeadsTo / Follows* ($plus.minus 1$): temporal or causal precedence ($+L$ forward, $-L$ backward).
+ *Contains / ContainedBy* ($plus.minus 2$): spatial or logical containment / membership ($+C$, $-C$).
+ *Expresses / ExpressedBy* ($plus.minus 3$): attribution of a property or intent ($+E$, $-E$).

Not every combination of node kinds and link axes makes physical sense—a timeless Concept cannot causally precede a physical Thing, nor can a Thing "lead to" another Thing without an Event mediating the change. Baugr adopts Burgess's *strict* $gamma(3,4)$ admissibility matrix (@tab-gamma34), where negative links are the exact antisymmetric converses of positive links: $"allowed"(u, r, v) = "allowed"(v, r^(-1), u)$.

#figure(
  {
    set text(size: 8.8pt)
    table(
      columns: (auto, auto, auto, auto, auto),
      inset: 5pt,
      align: center,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*Transition*], [*Near* ($0$)], [*+LeadsTo* ($+1$)], [*+Contains* ($+2$)], [*+Expresses* ($+3$)],
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
  caption: [Strict $gamma(3,4)$ admissibility matrix for positive links @burgess2025sst. Inverse links (`-LeadsTo`, `-Contains`, `-Expresses`) obey exact antisymmetry. Notice that `+LeadsTo` is permitted *only* between Events ($e -> e$).],
) <tab-gamma34>

This strict discipline yields three clean algebraic properties (all formally verified in §5):
- *Dual-link symmetry:* Storing a forward link $u arrow.r^(+r) v$ or its inverse $v arrow.r^(-r) u$ represents the *same* underlying relationship; causal reachability and light cones normalize both directions seamlessly.
- *Transitivity and inference closure:* Every positive axis is transitively closed, and Couch/Burgess semantic inference holds identically: if $x$ contains $y$ and $y$ expresses concept $z$, then $x$ can validly express $z$ (`Contains ; Expresses` $subset.eq$ `Expresses`); similarly `Near ; Expresses` $subset.eq$ `Expresses`.
- *Causal queries & quotient coarse-graining $bold(G)$:* Directed `sources(axis)` and `sinks(axis)` filter strictly to node meta-types admissible on `axis` (so causal `LeadsTo` sources/sinks return *only* Events, never Things or Concepts). Any kind-homogeneous partition collapses a $gamma(3,4)$ graph into a coarser well-formed $gamma(3,4)$ graph (dropping interior self-loops), letting architects zoom out from fine components to high-level subsystems without breaking spacetime invariants.

== The Canonical Functor $Phi$ and Causal Light Cones

Now comes the unifying bridge between Promise Theory and Semantic Spacetime. Look at the `+LeadsTo` column of @tab-gamma34: *only Events can lead to Events* @burgess2025sst (Appendix A).

Why does that rule matter so much in practice? Suppose host $A$ provides network routing to host $B$, host $B$ provides DNS resolution to host $A$, and host $A$ then establishes TLS using that DNS answer. If you draw causal arrows between *agents* ($A -> B -> A$), you see a spurious cycle! When you obey *"only events can lead to events,"* you instead map each *agent* to an enduring *Thing*, each *promise* to a causal *Event*, and each promise's *intent* to an expressed *Concept*:

#defbox("Definition 2", [Canonical Projection Functor $Phi : "PromiseSystem" -> gamma(3,4)$])[
  Given a Promise System $cal(S)$, the canonical graph $Phi(cal(S))$ has nodes $"Agent"(a) : t$, $"Promise"(p) : e$, and $"Intent"(p) : c$, with four families of well-formed links:
  + *Superagent containment* ($t arrow.r^(+C) t$): $"Agent"(s) arrow.r^(+C) "Agent"(c)$ whenever $s = "parent"(c)$.
  + *Promise participation* ($e arrow.r^(+C) t$): $"Promise"(p) arrow.r^(+C) "Agent"(a_p)$ linking each promise event to its promiser.
  + *Intent expression* ($t arrow.r^(+E) c$ and $e arrow.r^(+E) c$): both $"Agent"(a_p)$ and $"Promise"(p)$ express $"Intent"(p)$.
  + *Causal precedence* ($e arrow.r^(+L) e$): $"Promise"(d) arrow.r^(+L) "Promise"(p)$ for every existing dependency $d in "promiseDeps"(p)$ (both boolean `condDeps` and value-derivation `obsDeps`).
]

In the $A$/$B$ networking example, the causal chain becomes the clean acyclic event path $"A:net" arrow.r^(+L) "B:dns" arrow.r^(+L) "A:tls"$—the false agent cycle vanishes!

More profoundly, once a Promise System lives in $gamma(3,4)$, every promise $pi$ automatically acquires two canonical geometric objects borrowed from relativistic physics:
- Its *forward causal light cone* $J^+_Phi (pi)$: all promise events reachable from $pi$ along $+L$ (everything $pi$ can possibly influence—its exact *blast radius*).
- Its *reverse causal light cone* $J^-_Phi (pi)$: all promise events from which $pi$ is reachable along $+L$ (everything that can possibly influence $pi$—its exact *causal ancestry*).

@fig-microgrid illustrates this projection directly on the Hospital Microgrid from §2.1: the left side shows the voluntary promise network; the right side shows its canonical $gamma(3,4)$ image $Phi(cal(S))$, revealing cleanly why `factory`'s monitoring lies strictly outside $J^-_Phi ("hospital:operate")$.

#figure(
  kind: image,
  supplement: [Figure],
  block(
    width: 100%,
    inset: 9pt,
    stroke: 0.5pt + luma(195),
    radius: 3pt,
    fill: white,
  )[
    #set par(justify: false)
    #set text(size: 8.1pt)
    #grid(
      columns: (0.88fr, auto, 1.54fr),
      align: center + horizon,
      gutter: 6pt,
      // Left: Promise System
      block(
        width: 100%,
        fill: luma(249),
        stroke: 0.6pt + luma(170),
        inset: 7pt,
        radius: 3pt,
      )[
        #align(left)[#text(weight: "bold", fill: deep)[Promise Network $cal(S)$]]
        #v(5pt)
        #block(width: 100%, fill: white, stroke: 0.6pt + accent, inset: 4.5pt, radius: 2pt)[
          *`mains`*: `+power` (230V, 5kW)
        ]
        #v(4pt)
        #text(size: 7.6pt, fill: luma(80))[voluntary `+`/`-` overlap $b_1 inter b_2$]
        #v(4pt)
        #block(width: 100%, fill: white, stroke: 0.6pt + accent, inset: 4.5pt, radius: 2pt)[
          *`bank`* (opaque): #box[`-sense`], #box[`-recv_req`]\
          `+grant` $|$ `not Assisted(sense)` $and$ `AtLeast(2)`
        ]
        #v(4pt)
        #grid(
          columns: (1fr, 1fr),
          gutter: 5pt,
          block(width: 100%, fill: greenbg, stroke: 0.6pt + greenedge, inset: 4.5pt, radius: 2pt)[
            *`hospital`*\
            `-draw` (mains/bank)\
            `+operate | Assisted(draw)`
          ],
          block(width: 100%, fill: warmbg, stroke: 0.6pt + warmedge, inset: 4.5pt, radius: 2pt)[
            *`factory`*\
            `-monitor`\
            (mains only)
          ],
        )
      ],
      // Arrow Phi
      align(center)[
        #text(size: 10pt, weight: "bold", fill: accent)[$Phi$]\
        #text(size: 13pt, weight: "bold", fill: accent)[$arrow.r$]
      ],
      // Right: gamma(3,4) projection
      block(
        width: 100%,
        fill: white,
        stroke: 0.6pt + accent,
        inset: 7pt,
        radius: 3pt,
      )[
        #align(left)[#text(weight: "bold", fill: deep)[Semantic Spacetime $Phi(cal(S)) in gamma(3,4)$]]
        #v(4pt)
        // Things layer
        #block(width: 100%, fill: softbg, stroke: 0.5pt + luma(185), inset: 4.5pt, radius: 2pt)[
          #align(left)[*Things ($t$)*: `mains`, `bank` ($arrow.r^(+C)$ `cells`), `hospital`, `factory` #h(1fr) _($e arrow.r^(+C) t$)_]
        ]
        #v(4pt)
        // Events layer with shaded reverse light cone
        #grid(
          columns: (1.74fr, 0.78fr),
          gutter: 5pt,
          block(
            width: 100%,
            fill: greenbg,
            stroke: (paint: greenedge, thickness: 1.0pt, dash: "dashed"),
            inset: 4.5pt,
            radius: 3pt,
          )[
            #align(left)[#text(size: 7.3pt, weight: "bold", fill: greenedge)[Events ($e$) inside $J^-_Phi ("hospital:operate")$]]
            #v(3pt)
            #text(size: 6.9pt)[`mains:power` $arrow.r^(+L)$ `bank:sense`]\
            #text(size: 6.9pt)[`bank:sense`, `cells` $arrow.r^(+L)$ `bank:grant`]\
            #text(size: 6.9pt)[`mains:power`, `bank:grant`, `hosp:draw` $arrow.r^(+L)$ *`hosp:operate`*]
          ],
          block(
            width: 100%,
            fill: warmbg,
            stroke: 0.6pt + warmedge,
            inset: 4.5pt,
            radius: 3pt,
          )[
            #align(left)[#text(size: 7.3pt, weight: "bold", fill: warmedge)[Outside $J^-$]]
            #v(3pt)
            #text(size: 6.9pt)[`factory:monitor`]\
            #text(size: 6.8pt, fill: luma(80))[no $+L$ path]
          ],
        )
        #v(4pt)
        // Concepts layer
        #block(width: 100%, fill: luma(247), stroke: 0.5pt + luma(185), inset: 4.5pt, radius: 2pt)[
          #align(left)[*Concepts ($c$)*: Intent of each promise #h(1fr) _($t, e arrow.r^(+E) c$)_]
        ]
      ],
    )
  ],
  caption: [Canonical projection $Phi$ of the Hospital Microgrid into strict Semantic Spacetime $gamma(3,4)$. Notice that `+LeadsTo` flows into conditional promise `hosp:operate` (via `Assisted(draw)`), not into unconditional `hosp:draw`. Even across the negated failover link `bank:sense` $arrow.r^(+L)$ `bank:grant`, Law III guarantees that any perturbation to `factory:monitor` (outside the dashed reverse light cone $J^-$) leaves `hosp:operate` strictly invariant.],
) <fig-microgrid>

Complementing $Phi$, every superagent $S$ also induces a *coarse-graining directory* $pi_"directory" (S)$ @burgess2015spacetimes2 (Def. L1736), partitioning $S$'s interior sub-agents and interior promises from the explicit surface promises visible to external observers.

// ============================================================================
// Section 5
// ============================================================================

= The Four Universal Laws (Machine-Checked in Lean 4)

We now state the four universal laws guaranteed for *every* Promise System expressible in Baugr, explain *why* each holds mathematically, and catalog all *30 machine-checked theorems* proved in pure Lean 4 (zero external proof libraries, zero `sorryAx`).

== Law I — Non-Coercion (Axiom of Autonomy)

#lawbox("I", [Non-Coercion (`autonomy_unaccepted_offer_inert`)])[
  Let $cal(S)$ be any Promise System and extend $cal(S)$ with a fresh offer $pi_"new"$ (`find? id = none`) from any external agent (distinct from $pi$'s promiser and not a directly visible interior sub-agent of $pi$'s promiser) that is not statically bindable (`mayBind`) to any existing `Use` promise in $cal(S)$. Then—*unconditionally*, with zero syntactic side-conditions—one-step quenching `quenchStep` (both boolean activation *and* derived body computation) for $pi$ in $cal(S) union \{pi_"new"\}$ yields the exact same `Option(Body(O, U))` as in $cal(S)$.
]

*Why it holds:* Both condition atoms and `LocalObs` views enforce strict ownership, polarity, and visible-interior predicates on every reference. Because $pi_"new"$ is an unaccepted offer from an external agent, neither `evalCond` nor `buildLocalObs` can observe it—even if an existing promise contained a dangling reference to $pi_"new"$'s ID. In Promise Theory terms, an external unaccepted imposition has zero causal power.

== Law II — Boundary Integrity (Event-Horizon Vertex Cut)

#lawbox("II", [Boundary Integrity (`opaque_non_piercing`, `opaque_no_direct_causal_crossing`, `opaque_event_horizon_cut`)])[
  Let $s$ be an opaque superagent in $cal(H)$, let $a$ be a strict interior member ($s #splus a$), and let $b$ be an exterior agent ($not (s prec.eq b)$—including an enclosing parent superagent above $s$). Then:
  + *Non-piercing (outward and inward):* Neither an offer (fixed or derived) from $a$ to $b$ nor from $b$ to $a$ can ever form an active binding (`mayBind = false`).
  + *No direct causal crossing:* Every `+LeadsTo` edge in $Phi(cal(S))$ satisfies `noOpaqueWall` between source and target promisers (`opaque_no_direct_causal_crossing`).
  + *Event-horizon vertex cut & interior isolation:* Every causal path in $Phi(cal(S))$ from any strict interior promise of $s$ to any exterior promise *must* pass through an intermediate *surface promise* owned by $s$ (`opaque_event_horizon_cut`), and any interior perturbation outside $J^-_Phi (pi_"ext")$ leaves $pi_"ext"$ strictly invariant.
]

*Why it holds:* Both `mayBind` and `Interior` enforce `noOpaqueWall`, and `promiseDeps` guards every dependency on the exact same boundary predicate. Consequently, no direct causal arrow can jump across an opaque wall—the surface promises of $s$ form a genuine graph-theoretic *vertex cut* in Semantic Spacetime separating $s$'s entire interior from the outside universe (even across arbitrarily nested opaque superagents).

== Law III — Causal Locality (Reverse Light-Cone Containment)

#lawbox("III", [Causal Locality (`perturbation_in_reverse_cone`)])[
  Let $alpha_1, alpha_2 : A times P -> \{bot, top\}$ be any two observer-local assessments that agree on every promise $d$ inside the Semantic Spacetime reverse causal light cone of a target promise $pi$—that is, whenever $"Promise"(d)$ can reach $"Promise"(pi)$ along dual-normalized `+LeadsTo` edges in $Phi(cal(S))$. Then for any stratification $"rank"$, step count, and top stratum, $pi$ resolves to the exact same `Option(Body(O, U))` under $alpha_1$ and $alpha_2$.
]

*Why it holds:* This is the centerpiece theorem linking operational promise semantics to Semantic Spacetime geometry. First, local congruence lemmas (`evalCond_local`, `buildLocalObs_local`, `evalRule_local`) prove that both boolean conditions and value-derivation functions depend solely on the resolved bodies and local assessments of their declared dependencies $d in "promiseDeps"(p)$ present in $cal(S)$. Second, the functor $Phi$ emits a `+LeadsTo` edge $"Promise"(d) arrow.r^(+L) "Promise"(p)$ for every such dependency—regardless of whether $d$ appears positively, under negation, or inside a derived `Obs`. Therefore, by induction over strata and fixed-point iterations, any assessment perturbation outside $J^-_Phi (pi)$ is causally unreachable from $pi$.

== Law IV — Order Independence (Apt–Blair–Walker via Light Cones)

#lawbox("IV", [Order Independence (`stratification_independent`)])[
  Let $"rank"_1, "rank"_2 : P -> NN$ be *any* two valid stratifications of $cal(S)$ bounded by $M_1, M_2$, and let each stratum iterate at least $|P|+1$ times. Then evaluating $cal(S)$ under $"rank"_1$ and under $"rank"_2$ converges to the *exact same* global value fixed point of $T_alpha$:
  $ "evalStratified"(cal(S), alpha, "rank"_1, M_1) = "evalStratified"(cal(S), alpha, "rank"_2, M_2) : P -> "Option"("Body"(O, U)). $
]

*Proof insight (geometry proves semantics):* While Apt, Blair, and Walker's classic theorem @apt1988stratified is traditionally proved for boolean Herbrand interpretations, Baugr's coupling with Semantic Spacetime yields a constructive proof over *full value-carrying derived promises* in three steps:
+ *Polarity-indexed monotonicity & frozen derivations:* Under arbitrarily nested negations, condition evaluation is monotone in even-parity dependencies and antitone in odd-parity dependencies under the flat order `StateLe`. Within stratum $s$, every odd-parity dependency *and* every `Obs` value-derivation input sits strictly below $s$ and is frozen, so every derived body is constant within stratum $s$ and the per-stratum operator is monotone.
+ *Finite pigeonhole convergence:* On a finite system of $|P|$ promises, the count of quenched (`isSome`) promises along an ascending `StateLe` chain can increase at most $|P|$ times; thus every stratum freezes at its exact least fixed point within $|P|+1$ iterations, assembling into a global fixed point of $T_alpha$.
+ *Symmetric light-cone induction:* Every causal path in $Phi(cal(S))$ is non-decreasing in *any* valid rank. By strong induction on $k = "rank"_1 (p) + "rank"_2 (p)$, to compare the two solutions $F_1$ and $F_2$ at promise $p$, we construct a pre-fixed point $G$ matching the lower strata below $"rank"_1 (p)$, matching $F_2$ on the reverse light cone $J^-_Phi (p)$ at stratum $"rank"_1 (p)$, and returning each promise's base-frozen `evalRule` outside $J^-_Phi (p)$. Leastness under `StateLe` forces $F_1 (p) = "some"(b) => F_2 (p) = "some"(b)$, and symmetry forces exact equality $F_1 (p) = F_2 (p)$.

== Complete Machine-Checked Theorem Catalog

@tab-theorems lists all *30 audited theorems* verified in pure Lean 4 (`lean4` 4.35.0, zero `Mathlib`, `0` warnings, `0 sorryAx`). Every theorem depends strictly on Lean's standard logical foundations (`propext`, `Quot.sound`, and where classical decidability enters, `Classical.choice`).

#figure(
  {
    set text(size: 7.9pt)
    show raw: text.with(size: 7.1pt)
    table(
      columns: (auto, 1.62fr, 1.82fr, auto),
      inset: 3.5pt,
      align: left,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*Family*], [*Lean 4 Theorem*], [*Verified Mathematical Property*], [*Axioms*],
      [SST], [`LinkKind.inv_inv`, `hasEdge_inv`], [Link inversion is an exact involution; dual-normalized edges are symmetric.], [_(none)_],
      [SST], [`allowed_antisym`, `hasEdge_wellFormed`], [Exact $gamma(3,4)$ antisymmetry & well-formedness of dual-normalized edges.], [`P`],
      [SST], [`allowed_pos_trans`], [Transitive closure of all four positive $gamma(3,4)$ axes.], [`P`],
      [SST], [`inference_contains_expresses`, \ `inference_near_expresses`], [Couch/Burgess semantic inference closure (`Contains;E`, `Near;E` $subset.eq$ `E`).], [`P`],
      [SST], [`coarseGrain_wellFormed`], [Kind-homogeneous quotient $bold(G)$ preserves $gamma(3,4)$ well-formedness.], [`P, Q`],
      [Quench], [`evalCond_mono`, `evalCond_mono_pol`, \ `quenchStep_mono`], [Positive monotonicity & polarity-indexed monotonicity under nested `Not`.], [`P, Q`],
      [Quench], [`quenchIter_le_any_prefixed`, \ `quenchIter_chain`], [Knaster–Tarski least fixed point & ascending chain monotonicity @tarski1955fixedpoint.], [`P, Q`],
      [Quench], [`cyclic_conditional_never_quenches`], [Closed circular self-dependent subsets never quench in `lfp`.], [`P, Q`],
      [Law IV], [`stratified_agrees_with_positive`], [Single-stratum stratified evaluation coincides with positive `lfp`.], [`P, C, Q`],
      [Law IV], [`checkValidStratification_sound`], [Executable stratification validator implies formal `ValidStratification`.], [`P, Q`],
      [Law IV], [`stratumStep_mono`], [Per-stratum step operator is monotone once lower strata are frozen.], [`P, Q`],
      [Law IV], [`stratumIter_fixed_point`, \ `evalStratified_fixed_point`], [Finite convergence ($<= |P|+1$ steps) to a global fixed point of $T_alpha$.], [`P, C, Q`],
      [Law IV], [`stratification_independent`], [*Order Independence*: any two valid stratifications yield the same value fixed point.], [`P, C, Q`],
      [Law I], [`autonomy_unaccepted_offer_inert`], [*Non-Coercion*: external unaccepted offers are unconditionally inert on `quenchStep`.], [`P, Q`],
      [Law III], [`projectSst_wellFormed`], [Canonical functor $Phi : "PromiseSystem" -> gamma(3,4)$ is always well-formed.], [`P, Q`],
      [Law III], [`perturbation_in_reverse_cone`], [*Causal Locality*: perturbations outside $J^-_Phi (pi)$ leave $pi$'s resolved body invariant.], [`P, Q`],
      [Law II], [`noOpaqueWall_refl`, `noOpaqueWall_symm`], [Opaque boundary non-piercing predicate is reflexive and symmetric.], [`P, Q`],
      [Law II], [`opaque_non_piercing`, \ `opaque_non_piercing_inward`], [*Boundary Integrity*: opaque superagents block outward & inward piercing.], [`P, C, Q`],
      [Law II], [`opaque_interior_perturbation_` \ `contained`], [Interior perturbations of an opaque superagent stay contained outside $J^-$.], [`P, Q`],
      [Law II], [`opaque_no_direct_causal_crossing`, \ `opaque_event_horizon_cut`], [*Event-Horizon Vertex Cut*: no `+L` crosses a wall; every path hits a surface promise.], [`P, Q`],
    )
  },
  caption: [Complete catalog of all 30 audited Lean 4 theorems (`0 sorryAx`, zero `Mathlib`). Axioms: `P` = `propext`, `Q` = `Quot.sound`, `C` = `Classical.choice`.],
) <tab-theorems>

// ============================================================================
// Section 6
// ============================================================================

= Positioning and Comparison to Existing Systems

Does anything like Baugr already exist? To answer accurately, we surveyed five neighboring ecosystems: existing Promise Theory / SST implementations, Assume–Guarantee contract frameworks, Stratified Datalog and Answer Set Programming engines, relational/temporal model checkers, and categorical graph libraries. @tab-compare summarizes the landscape honestly, including where each neighboring tool strictly outperforms Baugr.

#figure(
  {
    set text(size: 7.7pt)
    table(
      columns: (1.05fr, 0.55fr, 0.55fr, 0.55fr, 0.6fr, 0.8fr, 1.35fr),
      inset: 4pt,
      align: (left, center, center, center, center, left, left),
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*System / Paradigm*], [*Voluntary `+`/`-` & Autonomy*], [*Observer Subjectivity*], [*Opaque Walls*], [*SST $gamma(3,4)$*], [*Machine Proofs*], [*Where It Beats Baugr*],
      [*Baugr v0.4*], [*Yes* (Law I)], [*Yes* (Law III)], [*Yes* (Law II)], [*Yes* (strict)], [Lean 4 (30 thms) + DRT], [Minimal verified autonomy + symmetric `±f(obs)` PT + causal geometry],
      [*SSTorytime / N4L* @burgess2025sstorytime], [No], [No], [Partial (`+C`)], [*Yes* (relaxed)], [No], [Human N4L authoring, PostgreSQL knowledge graphs, fuzzy search],
      [*CFEngine* @burgess1995cfengine], [Yes (OS domain)], [Local host], [Bundles (informal)], [No], [No], [Battle-tested Linux convergence runtime across millions of hosts],
      [*Assume–Guarantee / Pacti* @benveniste2018contracts @incer2025pacti], [No (global $A => G$)], [No], [Composition $times.o$], [No], [Algebraic solvers], [Continuous/hybrid CPS synthesis, polyhedral quotients & refinement],
      [*Stratified Datalog* (`Soufflé`, AFP) @jordan2016souffle @schlichtkrull2024datalog], [No (open rules)], [Manual], [Manual], [No], [AFP Isabelle (raw Datalog)], [Million-tuple compiled C++ analytics (`Soufflé`), general program analysis],
      [*ASP (`Clingo`)* @gebser2019clingo], [No], [Manual], [Manual], [No], [No], [Unstratified negative cycles (multiple stable equilibria) & NP optimization],
      [*Alloy* @jackson2012alloy], [No], [Manual], [Manual], [No], [Bounded SAT], [Automatic finite counterexample discovery for arbitrary relational designs],
      [*TLA+ / Quint* @lamport2002tla], [No], [Explicit msgs], [Action scoping], [No], [Model check / TLAPS], [Multi-step temporal liveness, fairness, asynchronous interleavings],
      [*Catlab.jl (C-Sets)* @patterson2022acsets], [No], [No], [Operads / cospans], [Encodable], [No], [General categorical data migrations, double-pushout rewriting, ODEs],
    )
  },
  caption: [Comparative landscape positioning Baugr against adjacent formalisms and tools across five ecosystems.],
) <tab-compare>

== Promise Theory and Semantic Spacetime Tooling

Mark Burgess's own `SSTorytime` @burgess2025sstorytime (successor to his earlier `SemanticSpaceTime` Go repository) realizes Semantic Spacetime as a PostgreSQL-backed knowledge-graph engine paired with the human-readable N4L narrative language. Its strength is rich knowledge representation and interactive graph exploration; it does not implement conditional promise quenching, observer-local assessment, opaque wall enforcement, or interactive theorem proving. Similarly, `CFEngine` @burgess1995cfengine pioneered Promise Theory in production Linux administration, and Cisco's OpFlex drew inspiration from Promise Theory for software-defined networking, but both embed promise concepts tightly inside domain-specific runtimes rather than exposing a reusable, formally proved mathematical kernel. (Meanwhile, existing Rust libraries carrying "promise" in their name implement JavaScript-style asynchronous futures, unrelated to Bergstra–Burgess Promise Theory.)

== Assume–Guarantee Contracts (Benveniste et al., Pacti)

Assume–Guarantee (A/G) contract theory @benveniste2018contracts and its modern algebraic engine `Pacti` @incer2025pacti are the closest conceptual relatives to conditional promises (`+b | -c`): both enable modular reasoning about complex systems without monolithic state-space explosion. Yet the two formalisms rest on fundamentally different epistemologies. A/G contracts model *obligations* over a single objective environment ($A => G$) and focus on *refinement, quotient, and continuous/polyhedral synthesis* for cyber-physical systems. Promise Theory rejects obligation in favor of *voluntary bilateral alignment* ($+o$ meeting $-u$ via overlap $o inter u$) and treats *subjective observer disagreement* ($alpha_a (pi) != alpha_b (pi)$) as first-class. `Pacti` dominates continuous control synthesis and algebraic contract decomposition; Baugr dominates decentralized autonomy, observer-local failure isolation, and causal light-cone analysis.

== Stratified Datalog and Answer Set Programming

Operationally, Baugr's stratified quenching fixed point is a disciplined instance of Apt–Blair–Walker stratified logic programming @apt1988stratified—recently formalized in general for raw Datalog in Isabelle/HOL @schlichtkrull2024datalog and executed at massive scale by engines such as `Soufflé` @jordan2016souffle. The vital difference is *grammatical discipline*. Raw Datalog allows any rule to join any global relation, silently piercing boundaries or reacting to unaccepted offers unless the author proves otherwise for every program. Baugr trades general-purpose relational expressiveness for *structural universality*: Laws I–III hold once and for all across every Baugr system. Conversely, whenever a problem requires million-tuple analytical joins (`Soufflé`) or unstratified negative cycles with multiple competing equilibria and optimization (`Clingo` @gebser2019clingo), general-purpose logic-programming engines are strictly the right tool.

== Relational, Temporal, and Categorical Frameworks

`Alloy` @jackson2012alloy excels at rapid bounded counterexample search during exploratory modeling, whereas Baugr's Lean 4 proofs establish universal theorems valid for finite systems of *arbitrary* size. `TLA+` @lamport2002tla and `Quint` verify *multi-step temporal traces*, asynchronous message interleavings, and liveness under fairness; Baugr models *quasi-static voluntary intent and causal geometry* at any observer-local snapshot $alpha$. The two are naturally complementary—a multi-layer architecture can use Baugr to govern static structural intent, autonomy, and causal boundaries while verifying runtime state transitions with TLA+ or Quint. Finally, `Catlab.jl` @patterson2022acsets offers a general categorical framework (attributed C-sets) in which $gamma(3,4)$ schemas could certainly be encoded, but focuses on scientific computing migrations and rewriting rather than formally verified Promise Theory semantics.

*Summary of Baugr's niche:* To our knowledge, no prior library or proof-assistant formalization unifies Bergstra–Burgess conditional Promise Theory with strict $gamma(3,4)$ Semantic Spacetime in a minimal, domain-agnostic, machine-checked kernel where Autonomy, Opaque Encapsulation, Reverse Light-Cone Locality, and Stratification Independence are proved once for all systems.

// ============================================================================
// Section 7
// ============================================================================

= Practical Guide: Using Baugr in Real Systems

How does an engineer turn an informal architecture into a formally checked Baugr model and extract actionable answers from it? In practice, every application of Baugr follows the same four-step workflow, regardless of domain.

== The Four-Step Practitioner Workflow

+ *Define your domain compatibility as native code (`BodyAlgebra`).* Decide what an offer looks like ($O$), what an acceptance looks like ($U$), and what non-empty shared commitment ($M$) emerges when they match (`fn overlap(&self, o: &O, u: &U) -> Option<Self::Overlap>`). Much like Rust's `Iterator::Item` / `Option<Self::Item>`, keeping `Option` on the method return lets Baugr's engine distinguish compatible from incompatible pairs while guaranteeing every active `Binding` carries a plain, non-empty `M` without unwrapping. Use symmetric types ($O = U = M$) via `SymmetricMeet`, or asymmetric structs when offers and uses carry distinct domain semantics—with zero requirement that bindings be numeric or ordered.
+ *Declare agents, superagent walls, and voluntary promises (`Promise::offer`, `accept`, `derive_offer`, `derive_use`).* Register superagents (`add_superagent(name, opaque)`) and containment edges (`contain(superagent, child)`), then attach static promises (`±b | C`) or symmetric value-derived promises (`+f(obs) | C` and `-f(obs) | C` via `DeriveAlgebra`), explicit visibility scopes (`.with_scope(...)`), and boolean conditions. Domain policies—resource allocation, exclusive leases, passive overload monitors, protocol alignment, quorums, and failover—are all expressed directly through autonomous promises and conditions.
+ *Run static diagnostics before evaluating anything (`lint()`).* Catch modeling bugs—typos in promise IDs, referencing another agent's promise inside `SelfPromise`, polarity mismatches, pointing `Interior` outside a superagent's children or across an inner opaque wall (`OpaqueWallBlocked`), targeting unregistered agents (`UnknownTargetAgent`), permanently *null-potent* thresholds (`UnsatisfiableMinCount` across `Assisted`, `Accepted`, and `AtLeast`), or leaving a target blind to a surface dependency's scope—before simulation or deployment.
+ *Evaluate observer-local scenarios and query causal geometry.* Call `resolve_optimistic()` to verify the healthy steady state, pass arbitrary observer-local assessment closures `resolve(|observer, promise| ...)` to test partial blackouts, partitions, or sensor failures, inspect resolved bodies via `resolved.body(&id)` / `resolved.offer(&id)` / `resolved.use_body(&id)` and active bindings via `resolved.bindings`, project via `project_sst(&sys)` for `forward_causal_cone()` ($J^+$) and `reverse_causal_cone()` ($J^-$), and call `directory_of(&sys, &superagent)`.

== Worked Showcase: Microgrid with Emergent 2-of-3 Bank & Symmetric `±f(obs) | C` Coordination

Combining both running examples from §2 into one end-to-end system (`examples/microgrid.rs`), suppose the site's backup `bank` is an *opaque superagent* encapsulating three 800 W internal battery cells `{cell1, cell2, cell3}`. Rather than hardcoding a static wattage or bolting on external law wrappers, agents coordinate symmetrically through both `+f(obs) | C` and `-f(obs) | C`:
+ `hospital` (1000 W, priority 1) and `clinic` (800 W, priority 2) voluntarily send `Request` offers to `bank`, which accepts them via `bank:recv_req`.
+ During a blackout with $>=$ 2 healthy interior cells, `bank` uses a *derived offer* (`+f(obs) | C`) to sum its healthy interior cells (1600 W if `cell1` crashed; 2400 W if all 3 live) and emit separate concrete grants—`+Power(1000 W)` to `hospital` and the exact leftover `+Power(600 W)` to `clinic` (or full 800 W if `hospital` is offline).
+ `clinic` then decides *autonomously* how to respond: a *partial* clinic (`min_w: 1`) binds 600 W and uses a *derived acceptance* (`-f(obs) | C`, `clinic:draw_aux`) to draw the exact 200 W shortfall from secondary supplier `aux` (falling silent when already satisfied); a *strict* clinic (`min_w: 800`) rejects 600 W, activating its own #box[`!Cond::assisted("clinic:draw")`] local diesel backup!

$ "bank" arrow.r^(+C) \{"cell"_1, "cell"_2, "cell"_3\} quad ("opaque"), \
  "hosp" arrow.r^(+"Req"(1000"W", 1)) "bank", quad "clinic" arrow.r^(+"Req"(800"W", 2)) "bank", \
  "bank" arrow.r^(+f_("prio")("recv_req", "cells") | not "Assisted"("sense") and "AtLeast"(2, "Interior")) \{"hosp", "clinic"\}, \
  "clinic" arrow.r^(+"diesel" | not "Assisted"("draw")) "clinic", quad "clinic" arrow.r^(-f_("rem")("draw") | "Assisted"("draw")) "aux". $

Below is the direct, verified Rust realization (abbreviated only in struct field repetition) exercising symmetric `derive_offer` (`+f(obs) | C`) and `derive_use` (`-f(obs) | C`), channel-sharp `may_overlap`, deduplicated `Obs`, opaque encapsulation, emergent interior-cell wattage, autonomous partial vs. strict failover, reverse light cones $J^-$, and `directory_of`:

```rust
use baugr::{
    AgentSet, Body, BodyAlgebra, Cond, DeriveAlgebra, LocalView, Obs, Promise, PromiseSystem,
    SpecRef, SstNode, directory_of, project_sst,
};

enum GridOffer {
    CellPower(u32), Request { w: u32, prio: u8 }, Power { v: u16, w: u32 }, Diesel,
}
enum GridUse  { AcceptReqs, Draw { v: u16, min_w: u32, max_w: u32 } }
enum GridRule { PriorityGrant(&'static str), ResidualDraw { wanted: u32 } }
struct GridAlgebra;

impl BodyAlgebra for GridAlgebra {
    type Offer = GridOffer; type Use = GridUse; type Overlap = (u16, u32);
    fn overlap(&self, o: &GridOffer, u: &GridUse) -> Option<Self::Overlap> {
        match (o, u) {
            (GridOffer::Request { w, .. }, GridUse::AcceptReqs) => Some((0, *w)),
            (GridOffer::Power { v, w }, GridUse::Draw { v: uv, min_w, max_w })
                if v == uv && w >= min_w => Some((*v, (*w).min(*max_w))),
            _ => None,
        }
    }
}

impl DeriveAlgebra<&'static str, &'static str, GridRule> for GridAlgebra {
    fn may_overlap(
        &self, offer: SpecRef<'_, GridOffer, GridRule>, use_: SpecRef<'_, GridUse, GridRule>,
    ) -> bool {
        matches!(
            (offer, use_),
            (SpecRef::Derived(GridRule::PriorityGrant(_)), SpecRef::Fixed(GridUse::Draw { .. }))
            | (SpecRef::Fixed(GridOffer::Power { .. }), SpecRef::Derived(GridRule::ResidualDraw { .. }))
        )
    }
    fn derive_offer(
        &self, rule: &GridRule, obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<GridOffer> {
        let GridRule::PriorityGrant(recipient) = rule else { return None; };
        // Emergent cap = sum of healthy interior cells (1600W w/ 2/3, 2400W w/ 3/3)
        let cap: u32 = obs.interior_entries().iter().filter_map(|(_, _, b)| match b {
            Body::Offer(GridOffer::CellPower(w)) => Some(*w), _ => None,
        }).sum();
        let mut reqs: Vec<_> = obs.assisted("bank:recv_req").filter_map(|e| match e.offer {
            GridOffer::Request { w, prio } => Some((*prio, *e.promiser, *w)), _ => None,
        }).collect();
        reqs.sort_by_key(|(p, a, _)| (*p, *a));
        let mut rem = cap;
        for (_, agent, want) in reqs {
            let g = want.min(rem); rem = rem.saturating_sub(g);
            if agent == *recipient {
                return (g > 0).then_some(GridOffer::Power { v: 230, w: g });
            }
        }
        None
    }
    fn derive_use(
        &self, rule: &GridRule, obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<GridUse> {
        let GridRule::ResidualDraw { wanted } = rule else { return None; };
        let got: u32 = obs.assisted("clinic:draw").map(|e| e.overlap.1).sum();
        let deficit = wanted.saturating_sub(got);
        (deficit > 0).then_some(GridUse::Draw { v: 230, min_w: deficit, max_w: deficit })
    }
}

// Opaque 2-of-3 superagent `bank`, provider `+f(obs) | C` grants & consumer `-f(obs) | C` draw:
let mut sys = PromiseSystem::with_rules(GridAlgebra);
sys.add_superagent("bank", true);
for (c, pid) in [("cell1", "cell1:chg"), ("cell2", "cell2:chg"), ("cell3", "cell3:chg")] {
    sys.contain("bank", c)?;
    sys.add_promise(Promise::offer(pid, c, AgentSet::All, GridOffer::CellPower(800)));
}
// ... add `grid:mains`, `aux:power` (500W), `bank:sense`, `bank:recv_req`, `hosp:req`, `clinic:req`
let bank_obs = [
    Obs::assisted("bank:recv_req"), Obs::interior("cell1:chg"),
    Obs::interior("cell2:chg"), Obs::interior("cell3:chg"),
];
let failover = Cond::all(vec![!Cond::assisted("bank:sense"), Cond::at_least(2, vec![
    Cond::interior("cell1:chg"), Cond::interior("cell2:chg"), Cond::interior("cell3:chg"),
])]);
for (pid, who) in [("bank:grant_hosp", "hospital"), ("bank:grant_clinic", "clinic")] {
    sys.add_promise(Promise::derive_offer(pid, "bank", AgentSet::single(who), bank_obs,
        GridRule::PriorityGrant(who)).when(failover.clone()));
}
// Consumer-side `-f(obs) | C`: partial clinic draws exact 200W shortfall from `aux`;
// strict clinic (`min_w: 800`) rejects 600W -> `!Cond::assisted("clinic:draw")` fires diesel!
sys.add_promise(Promise::derive_use("clinic:draw_aux", "clinic", AgentSet::single("aux"),
    [Obs::assisted("clinic:draw")], GridRule::ResidualDraw { wanted: 800 })
    .when(Cond::assisted("clinic:draw")));

let blackout = |obs: &&str, p: &&str| !(*obs == "bank" && matches!(*p, "grid:mains" | "cell1:chg"));
let r = sys.resolve(blackout)?;
assert_eq!(r.offer("bank:grant_hosp"),   Some(&GridOffer::Power { v: 230, w: 1000 }));
assert_eq!(r.offer("bank:grant_clinic"), Some(&GridOffer::Power { v: 230, w: 600 }));
assert_eq!(r.use_body("clinic:draw_aux"), Some(&GridUse::Draw { v: 230, min_w: 200, max_w: 200 }));
let cone = project_sst(&sys).reverse_causal_cone(&SstNode::Promise("clinic:draw_aux")); // 11 nodes
let dir  = directory_of(&sys, &"bank");                                                 // 3 int / 4 surf
```

== Three Practical Deployment Patterns

Because Baugr imposes no runtime framework or domain schema, teams typically embed it in one of three roles:
+ *Pre-flight topology and architecture gate (CI / GitOps):* Deserialize infrastructure manifests, service meshes, or microservice contracts in a thin outer layer, compile them into a `PromiseSystem`, and fail builds automatically whenever an opaque subsystem boundary is pierced, a conditional promise lacks complete information, an unstratifiable cycle appears, or an unintended dependency enters a critical service's reverse light cone $J^-$.
+ *Interactive fault-impact and failover simulator:* Given a live fleet snapshot, sweep observer-local assessments $alpha$ (single-node failures, asymmetric network partitions, regional blackouts) to verify *before* an outage that every critical promise either fails over cleanly or stays isolated outside the blast radius $J^+$.
+ *Embedded coordination kernel:* Because the execution library requires no operating-system I/O and no standard library (`#![no_std]` + `alloc`), it embeds directly inside edge controllers, custom schedulers, or policy engines as a fast, deterministic, formally verified decision core.

// ============================================================================
// Section 8
// ============================================================================

= Verified Realization and Empirical Validation

To make the calculus directly usable inside real software systems without sacrificing formal rigor, Baugr follows the *Verification-Guided Development* (VGD) methodology pioneered by AWS Cedar @cutler2024cedar: rather than relying on fragile automated code extraction, we maintain two clean, mirroring artifacts mechanically locked together by differential testing.

- *Formal Kernel (Lean 4):* Three small specification modules mirroring §§3–4 (`Spacetime`, `Promise`, `Projection`) and six proof modules verifying all 30 theorems of @tab-theorems with zero `Mathlib` and zero `sorryAx`, compiled offline into an executable reference oracle.
- *Executable Library (Rust):* A zero-runtime-dependency, `#![no_std]` (`alloc`), `#![forbid(unsafe_code)]` Rust crate exposing the exact three mathematical modules. Polarity and static-vs-derived payloads factor cleanly as `Body<Spec<P, O, R>, Spec<P, U, R>>` with canonical deduplicated `BTreeSet<Obs<P>>` observation sets; static systems carry zero derivation boilerplate (`R = Infallible`), while symmetric value-derived promises (`±f(obs) | C`) implement `DeriveAlgebra` with optional channel-sharp `may_overlap`. Structural invariants—acyclic non-reparenting superagent containment, consistent $gamma(3,4)$ node typing, and strict transition admissibility—are enforced at mutation time; and `lint()` flags dangling IDs, wrong promisers, polarity mismatches, non-interior or `OpaqueWallBlocked` references, `UnknownTargetAgent`, permanently null-potent `UnsatisfiableMinCount` bounds across `Assisted`/`Accepted`/`AtLeast`, and incomplete-information surface scopes across both `Cond` and `Obs`.
- *Closing the Verification Loop via Oracle-Verified DRT:* In production execution, Rust computes minimal strata via Kosaraju's strongly connected component algorithm. Rather than trusting that algorithm blindly, our differential test suite generates *500 randomized stratifiable Promise Systems*—mixing static promises and *value-derived offers and acceptances* (`±f(obs) | C`, exercising all four `Obs` kinds with non-monotonic XOR/OR derivation rules and randomized `may_overlap` channel masks), random nested opaque/transparent hierarchies, bitmask mutual-information overlap, positive dependency cycles, nested `AtLeast` thresholds, *arbitrarily nested negations*, and broken observer-local assessments—and sends each system *together with Rust's computed stratification* to the compiled Lean 4 oracle. On every single case, Lean mechanically executes our proved-sound `checkValidStratification` validator before verifying bit-for-bit agreement between Rust and Lean across all *resolved promise bodies*, active bindings (including exact overlap values), projected $gamma(3,4)$ edges, and zero direct `+LeadsTo` crossings across any opaque wall (`0` divergences across 500/500 cases).
- *Cross-Domain Validation:* Three self-contained runnable examples exercise the library across unrelated domains—the *Hospital Microgrid* (opaque 2-of-3 emergent capacity, provider `+f(obs) | C` priority grants, consumer `-f(obs) | C` residual draw, strict local diesel failover, and channel-sharp `may_overlap`), the *Opaque Raft Cluster* (2-of-3 quorum emergence, blocked piercing, light-cone isolation), and *Multi-Tenant Cloud Tenancy* (Burgess `Accepted` tenancy, exclusive per-port leasing via `±f(obs) | C`, and protocol alignment via `BodyAlgebra::overlap`)—alongside an automated purity check confirming zero domain-specific terms or operating-system I/O inside the core library.

@tab-lineage records the exact traceability from the seven foundational papers to Baugr's formal definitions.

#figure(
  {
    set text(size: 8.2pt)
    table(
      columns: (auto, 1.55fr, 1.25fr),
      inset: 4.5pt,
      align: left,
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*Primary Source*], [*Mathematical Concept Adopted*], [*Realization in Baugr*],
      [@bergstra2008static], [Distinct target $T$ vs. visibility scope $sigma$; subjective assessment], [Directed promises; observer-local $alpha$],
      [@bergstra2014impositions], [Two polarities (`+`, `-`); impositions as offers + compliance; $a in sigma$], [`Offer`/`Use` body; Law I (Autonomy)],
      [@burgess2014spacetimes1], [Mutual-information overlap $b_1 inter b_2$; assisted quenching], [Body algebra; `Assisted`],
      [@burgess2015spacetimes2], [Opaque/transparent superagents; directories $pi_"directory"$; emergence; functional tenancy $plus.minus f(C, R) | C$; incomplete info], [`Hierarchy` & Law II; `Interior`/`Accepted`; `Spec::Derived` (`±f(obs)`); complete-info check],
      [@burgess2016spacetimes3], [Four irreducible spacetime axes; multi-condition aggregation], [`LinkKind` ($0, plus.minus 1, plus.minus 2, plus.minus 3$); `AtLeast`],
      [@burgess2025sst], [Strict $gamma(3,4)$ rules 1–2; antisymmetry; Couch/Burgess inference; quotient $bold(G)$], [Strict `SstGraph`; dual cones; `coarse_grain`; $Phi$],
      [@burgess2026quantitative], [Observer-local assessment $alpha_a (pi)$; self & assisted quenching], [Assessment map $alpha$; `Self`; stratified `resolve`],
    )
  },
  caption: [Direct mathematical lineage from the seven primary Bergstra and Burgess papers to Baugr.],
) <tab-lineage>

// ============================================================================
// Section 9
// ============================================================================

= Scope Boundaries and Future Directions

Keeping a mathematical kernel deep means knowing precisely where it stops. Baugr deliberately leaves four adjacent problems to composable layers above it:

+ *Multi-step temporal dynamics:* Baugr analyzes voluntary activation and causal geometry at any observer-local snapshot $alpha$. Time-evolving protocols, asynchronous message queues, and liveness under fairness belong in a temporal specification layer (such as TLA+ or Quint) whose state invariants may invoke Baugr.
+ *Three-valued, probabilistic, and continuous assessments:* Baugr fixes exact boolean assessments $alpha : A times P -> \{bot, top\}$ to preserve sharp Knaster–Tarski fixed points and exact stratification. Three-valued ("unknown") uncertainty, Bayesian trust distributions @burgess2026quantitative, or continuous control envelopes can layer cleanly over the boolean core via Kleene intervals or Monte Carlo sampling.
+ *Unstratified negative cycles:* Systems containing genuine cyclic mutual negation (for instance, symmetry-breaking election without tie-breakers) admit zero or multiple stable equilibria rather than a unique canonical model; Baugr flags them explicitly so callers can either break symmetry or delegate to an ASP solver.
+ *Domain syntax and authorization policy:* Schema desugaring, configuration languages, and capability/policy engines compose naturally *on top* of Baugr without leaking domain ontology into the domain-agnostic mathematical core.

By refusing to dilute its foundations with domain specifics, Baugr provides a small, auditable, domain-neutral algebraic bedrock where autonomy, encapsulation, order independence, and causal locality are not aspirations—they are proved theorems.

#v(0.35em)
#show bibliography: set text(size: 8.6pt)
#show bibliography: set par(leading: 0.48em)
#bibliography("refs.bib", style: "ieee")
