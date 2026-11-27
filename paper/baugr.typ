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
    `baugr` v0.2 — `https://github.com/LW-54/baugr`
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

  *Baugr* is a minimal, domain-agnostic mathematical model—and machine-checked formal library—of *voluntary coordination in causal spacetime*, derived directly from the Promise Theory and Semantic Spacetime $gamma(3,4)$ foundations of Jan Bergstra and Mark Burgess. By restricting conditional rules strictly to four autonomy-grounded local observations and canonically projecting every promise system into strict Semantic Spacetime (mapping agents to _Things_, promises to _Events_, and intents to _Concepts_), Baugr turns four foundational guarantees of decentralized engineering into *universal theorems* that hold automatically for every expressible system: *Non-Coercion* (unaccepted impositions are inert), *Boundary Integrity* (opaque superagents act as non-piercing event horizons), *Causal Locality* (observer-local failures outside a promise's reverse causal light cone cannot affect it, even across failover negation), and *Order Independence* (any valid stratification converges finitely to the same canonical steady state, proved constructively via spacetime light cones). We machine-check all 29 theorems in pure Lean 4 (`0 sorryAx`, zero external proof libraries), position Baugr against existing contract, logic-programming, model-checking, and knowledge-graph systems, and realize the calculus as a zero-dependency executable engine mechanically locked to its formal specification.
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

Baugr takes the opposite approach. Instead of building an unconstrained language and auditing away accidental coupling later, Baugr defines a small, closed algebra of *voluntary promises* coupled by a canonical functor $Phi$ to *strict Semantic Spacetime* $gamma(3,4)$ @burgess2025sst. Every construct in the algebra is drawn directly from seven primary papers of Bergstra and Burgess @bergstra2008static @bergstra2014impositions @burgess2014spacetimes1 @burgess2015spacetimes2 @burgess2016spacetimes3 @burgess2025sst @burgess2026quantitative. Because the condition grammar admits *only* observations grounded in an agent's own autonomy and superagent boundaries, *four universal laws* emerge automatically for *every* system expressible in Baugr—without per-model proof effort:

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
  + *Non-Coercion (Autonomy):* Adding an unaccepted offer or imposition can never alter the activation of any existing promise—not even indirectly through negation.
  + *Boundary Integrity (Opaque Encapsulation):* An opaque superagent acts as an event horizon: interior agents cannot bind across its wall, and internal failures cannot leak outside except through explicit surface promises.
  + *Causal Locality (Light-Cone Containment):* No observer-local failure outside a promise's reverse causal light cone $J^-_Phi (pi)$ can change whether $pi$ activates—even across non-monotonic failover rules.
  + *Order Independence (Canonicality):* Even with nested failover negation, every valid stratification converges in at most $|P|+1$ steps to the exact same steady state.
]

== Discipline of Scope

Baugr is intentionally small and strictly domain-agnostic. It models *voluntary intent, conditional activation, observer-local assessment, hierarchical boundaries, causal geometry, resource valency, and system-wide coordination laws*. It deliberately excludes wire protocols, multi-step temporal interleaving (where tools such as TLA+ and Quint excel @lamport2002tla), authorization policy languages, configuration syntax sugar, and domain vocabularies. Higher-level systems—whether energy grids, distributed platforms, or multi-tenant infrastructure—compose Baugr as a clean mathematical kernel without inheriting foreign assumptions.

// ============================================================================
// Section 2
// ============================================================================

= Intuition First: Two Running Examples

Before writing formal definitions, we ground every concept in Baugr using two completely different autonomous systems: a physical *hospital microgrid* and a distributed *consensus cluster*. We will revisit both throughout the paper.

== Example 1: The Autonomous Hospital Microgrid

Consider four independent actors sharing an electrical site: the municipal `mains`, an on-site `battery`, a critical `hospital` ward, and an adjacent `factory`.

- *Voluntary bilateral alignment (`+` and `-`):* `mains` voluntarily *offers* 230 V power up to 5000 W (`+power`). That offer alone powers nothing; `hospital` must independently declare that it *accepts* 230 V power (`-power`). Cooperation occurs only where an offer and an acceptance meet with compatible physical parameters (matching voltage and overlapping wattage)—a *mutual-information overlap* $b_1 inter b_2$ @burgess2014spacetimes1.
- *Failover via stratified negation:* `battery` accepts a grid-sensing signal from `mains` (`-sense`), and makes a *conditional* backup offer: _"I offer 230 V backup power (up to 1500 W) *if* my grid-sensing promise is *not* assisted by a working mains offer"_ (`+backup | not assisted(sense)`). When `mains` is healthy, `battery` stays quiet; when `mains` fails, `battery` automatically activates its backup offer, and `hospital` seamlessly binds to it.
- *Observer-local subjectivity:* Suppose a local breaker trips on the hospital feeder while the industrial feeder stays live. Now `battery` assesses `mains`'s offer as *broken* ($alpha_"battery" ("mains") = bot$), whereas `factory` assesses the *very same* `mains` offer as *kept* ($alpha_"factory" ("mains") = top$). In a single-truth logic this state is contradictory; in Baugr it is ordinary reality. `battery` activates backup power for `hospital`, while `factory` continues reading healthy mains—and crucially, nothing that happens to `factory`'s monitoring can ever perturb `hospital`'s power, because `factory` lies outside `hospital`'s reverse causal light cone.
- *Resource valency:* Even when `battery` activates, its inverter has a finite budget of 1500 W (`+backup#1500W`). If `hospital` draws 900 W and a secondary clinic draws 800 W, each individual bilateral binding is physically valid, yet the combined load (1700 W) violates `battery`'s *Promise Valency* budget.

== Example 2: The Opaque Consensus Cluster

Now consider a distributed storage service `cluster` built internally from three independent replica nodes $\{n_1, n_2, n_3\}$ serving an external `client` alongside an unrelated `metrics` observer.

- *Opaque boundary:* `cluster` is declared an *opaque superagent* containing $\{n_1, n_2, n_3\}$ @burgess2015spacetimes2. Inside the wall, the replicas freely exchange replication promises with one another. Outside the wall, `client` is structurally prevented from binding directly to replica $n_1$—even if $n_1$ publishes a broad offer and `client` tries to accept it.
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

Rather than inventing a rigid predicate language to decide when an offer $+o$ satisfies a use $-u$, Baugr parameterizes the entire algebra over a domain-supplied *body algebra*: a partial mutual-information overlap operation @burgess2014spacetimes1 @burgess2026quantitative
$ inter : O times U -> "Option"(M), $
returning the shared commitment $m in M$ (for instance, `"230 V, 900 W"` in the microgrid, or an agreed TLS version in a network protocol) when $o$ and $u$ are compatible, and `"none"` when they are incompatible.

A directed promise is a six-tuple $pi = ("id", a, T, sigma, b, C)$ where $a in A$ is the promiser, $T subset.eq A$ is the set of intended *targets* (promisees), $sigma subset.eq A$ is the *visibility scope* (who can observe the promise), $b in "Offer"(O) union "Use"(U)$ is the polarized body, and $C$ is an activation condition. Following @bergstra2008static @bergstra2014impositions, targets and observability scope are kept distinct: an agent may target one recipient while broadcasting visibility to an auditor, or hide a promise from third parties. Every promiser automatically observes its own promises:
$ "inScope"(pi, x) quad <=> quad (x = a) or (x in sigma). $

== Superagent Hierarchies and Opaque Event Horizons

Autonomous agents group into recursive *superagents* @burgess2015spacetimes2 (§3.3–3.7). A hierarchy $cal(H) = ("parent", "opaque")$ assigns each agent an optional parent (forming a strict acyclic forest—no agent may contain itself directly or transitively) and marks each superagent either *transparent* (a logical grouping whose interior members remain directly reachable) or *opaque* (an encapsulated unit with a hard boundary).

Write $s #splus a$ if $s$ is a strict ancestor of $a$ in $cal(H)$, and $s prec.eq a$ if $a = s$ or $s #splus a$.

#defbox("Definition 1", [Non-Piercing Opaque Wall])[
  Two agents $a, b in A$ respect every opaque boundary in $cal(H)$, written $"noOpaqueWall"(cal(H), a, b)$, if and only if for every $s in A$ with $"opaque"(s) = top$:
  $ (s #splus a => s prec.eq b) quad and quad (s #splus b => s prec.eq a). $
]

This symmetric condition captures an exact physical intuition: agents strictly inside an opaque superagent $s$ may cooperate freely with one another and with $s$'s own boundary, but can never form a direct link to any agent outside $s$.

Combining mutual-information overlap, bilateral targeting, visibility, and opaque boundaries yields the single static compatibility predicate governing when an offer $pi_o = ("id"_o, a_o, T_o, sigma_o, +o, C_o)$ and an acceptance $pi_u = ("id"_u, a_u, T_u, sigma_u, -u, C_u)$ can cooperate:
$ "staticBindable"(pi_o, pi_u) quad <=> quad a_u in T_o and "inScope"(pi_o, a_u) and a_o in T_u and "noOpaqueWall"(a_o, a_u) and (o inter u != "none"). $

== Autonomy-Grounded Conditions

How may an agent condition a promise on the world around it? In an arbitrary rule engine, agent $a$ could write _"activate my promise if remote agent $b$ made promise $q$"_—even if $a$ never accepted $q$, or even if $b$ lives behind an opaque wall. Baugr prohibits such non-autonomous peeking by construction. Every condition $C$ attached to a promise made by agent $a$ is built inductively from just *four autonomy-grounded atomic observations* and *two combinators*:

+ *Self-reliance* (`Self(q)`): promise $q$ made by *the same agent $a$* is active and locally kept by $a$ @burgess2026quantitative.
+ *Assisted reliance* (`Assisted(u, k)`): $a$'s own *Use* promise $u$ is active and statically compatible with at least $k$ active offers $pi_o$ that $a$ locally assesses as kept @burgess2014spacetimes1. (In the microgrid, `battery` senses `mains` via `Assisted(sense, 1)`.)
+ *Voluntary tenancy / acceptance* (`Accepted(o, k)`): $a$'s own *Offer* promise $o$ is active and accepted by at least $k$ active *Use* promises $pi_u$ visible in scope to $a$ and locally assessed kept @burgess2015spacetimes2. (A landlord or cloud provider commits power only after a tenant accepts its slot terms.)
+ *Superagent interior emergence* (`Interior(q)`): promise $q$ made by a *strict sub-agent* $b$ inside superagent $a$ ($a #splus b$) is active and assessed kept by $a$ @burgess2015spacetimes2. (In the consensus cluster, `cluster` observes replicas $n_1, n_2, n_3$.)
+ *Monotone threshold* (`AtLeast(k, [c_1, ..., c_n])`): at least $k$ of the sub-conditions hold—unifying unconditional promises ($k = 0$), logical conjunction ($k = n$), disjunction ($k = 1$), and quorums ($2$-of-$3$) in a single monotone combinator @burgess2016spacetimes3.
+ *Stratified negation* (`not c`): logical negation, enabling autonomous failover and fallback behavior such as `battery`'s `not Assisted(sense, 1)`.

Notice what is *absent*: there is no atom allowing agent $a$ to directly inspect an arbitrary promise of an unrelated agent $b$. To react to $b$, agent $a$ must either *voluntarily accept* $b$'s offer (`Assisted`), *voluntarily offer* something $b$ accepts (`Accepted`), or *enclose* $b$ as a superagent (`Interior`). That single grammatical discipline is the root source of Baugr's universal theorems.

== Observer-Local Assessment and Stratified Quenching

Promises express *intent*; whether a promise is actually *kept* is always judged subjectively by an observer @bergstra2008static @burgess2026quantitative. Baugr represents the current state of the world as an *observer-local assessment function*:
$ alpha : A times P -> \{bot, top\}, $
where $alpha_a (p) = top$ means *"agent $a$ assesses promise $p$ as kept."* Crucially, $alpha_a (p)$ and $alpha_b (p)$ need not agree—modeling split blackouts, network partitions, and asymmetric trust natively without contradiction.

Given an assessment $alpha$ and a candidate set of active ("quenched") promises $Q : P -> \{bot, top\}$, the one-step *quenching operator* $T_alpha (Q)$ evaluates each promise's condition $C_p$ under $(alpha, Q)$.

- *Positive systems & circularity rejection:* When no condition contains negation, $T_alpha$ is monotone on the finite boolean lattice $P -> \{bot, top\}$. By Tarski's theorem @tarski1955fixedpoint, iterating $T_alpha$ from the empty set $bot$ reaches the *unique least fixed point* $"lfp"(T_alpha)$ in at most $|P|+1$ steps. Crucially, taking the *least* fixed point rejects self-justifying circular promises ("$p_1$ activates if $p_2$ activates, and $p_2$ activates if $p_1$ activates"): unsupported cycles stay permanently unquenched.
- *Failover negation & stratification:* When conditions include negation (`not`), $T_alpha$ is no longer globally monotone—and a direct negative paradox ("activate $p$ iff $p$ is not active") has no canonical answer. Following Apt, Blair, and Walker @apt1988stratified, we extract the signed syntactic dependency set $"condDeps"(C_p)$ recording every promise $d$ referenced by $C_p$ together with the *parity* (even or odd number of enclosing negations) of the reference. A rank assignment $"rank" : P -> NN$ is a *valid stratification* iff:
  $ (d, "odd") in "condDeps"(C_p) => "rank"(d) < "rank"(p), quad "and" quad (d, "even") in "condDeps"(C_p) => "rank"(d) <= "rank"(p). $
  Any system free of negative cycles admits a valid stratification (computable via strongly connected components); any system containing a negative cycle is explicitly rejected as ill-posed. Resolution then proceeds stratum by stratum ($s = 0, 1, dots, M$): within each stratum $s$, all negative dependencies lie strictly below $s$ and are already frozen, making the restricted operator monotone again and converging finitely to a global fixed point $Q^* = T_alpha (Q^*)$.

Once $Q^*$ is computed, the *active cooperative bindings* of the system are all pairs $(pi_o, pi_u)$ such that $"staticBindable"(pi_o, pi_u)$, both $pi_o$ and $pi_u$ are quenched in $Q^*$, and the consumer locally assesses the offer as kept ($alpha_(a_u) ("id"_o) = top$), carrying their exact mutual-information overlap $m = o inter u$.

Finally, because malformed conditions fail silently to $bot$ under strict autonomy semantics (for example, referencing a nonexistent promise, naming another agent's promise inside `Self`, or leaving a promise's target outside the visibility scope $sigma$ of its assisting dependency @burgess2015spacetimes2), Baugr complements runtime resolution with static *complete-information* and *condition-lint* checks that flag modeling mistakes before deployment without relaxing the core semantics.

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

This strict discipline yields three clean algebraic properties (all formally verified in §6):
- *Dual-link symmetry:* Storing a forward link $u arrow.r^(+r) v$ or its inverse $v arrow.r^(-r) u$ represents the *same* underlying relationship; causal reachability and light cones normalize both directions seamlessly.
- *Transitivity and inference closure:* Every positive axis is transitively closed, and Couch/Burgess semantic inference holds identically: if $x$ contains $y$ and $y$ expresses concept $z$, then $x$ can validly express $z$ (`Contains ; Expresses` $subset.eq$ `Expresses`); similarly `Near ; Expresses` $subset.eq$ `Expresses`.
- *Quotient coarse-graining $bold(G)$:* Any partition grouping nodes of the *same* kind collapses a $gamma(3,4)$ graph into a coarser well-formed $gamma(3,4)$ graph (dropping interior self-loops), letting architects zoom out from fine components to high-level subsystems without breaking spacetime invariants.

== The Canonical Functor $Phi$ and Causal Light Cones

Now comes the unifying bridge between Promise Theory and Semantic Spacetime. Look at the `+LeadsTo` column of @tab-gamma34: *only Events can lead to Events* @burgess2025sst (Appendix A).

Why does that rule matter so much in practice? Suppose host $A$ provides network routing to host $B$, host $B$ provides DNS resolution to host $A$, and host $A$ then establishes TLS using that DNS answer. If you draw causal arrows between *agents* ($A -> B -> A$), you see a spurious cycle! When you obey *"only events can lead to events,"* you instead map each *agent* to an enduring *Thing*, each *promise* to a causal *Event*, and each promise's *intent* to an expressed *Concept*:

#defbox("Definition 2", [Canonical Projection Functor $Phi : "PromiseSystem" -> gamma(3,4)$])[
  Given a Promise System $cal(S)$, the canonical graph $Phi(cal(S))$ has nodes $"Agent"(a) : t$, $"Promise"(p) : e$, and $"Intent"(p) : c$, with four families of well-formed links:
  + *Superagent containment* ($t arrow.r^(+C) t$): $"Agent"(s) arrow.r^(+C) "Agent"(c)$ whenever $s = "parent"(c)$.
  + *Promise participation* ($e arrow.r^(+C) t$): $"Promise"(p) arrow.r^(+C) "Agent"(a_p)$ linking each promise event to its promiser.
  + *Intent expression* ($t arrow.r^(+E) c$ and $e arrow.r^(+E) c$): both $"Agent"(a_p)$ and $"Promise"(p)$ express $"Intent"(p)$.
  + *Causal precedence* ($e arrow.r^(+L) e$): $"Promise"(d) arrow.r^(+L) "Promise"(p)$ for every existing dependency $d in "condDeps"(C_p)$.
]

In the $A$/$B$ networking example, the causal chain becomes the clean acyclic event path $"A:net" arrow.r^(+L) "B:dns" arrow.r^(+L) "A:tls"$—the false agent cycle vanishes!

More profoundly, once a Promise System lives in $gamma(3,4)$, every promise $pi$ automatically acquires two canonical geometric objects borrowed from relativistic physics:
- Its *forward causal light cone* $J^+_Phi (pi)$: all promise events reachable from $pi$ along $+L$ (everything $pi$ can possibly influence—its exact *blast radius*).
- Its *reverse causal light cone* $J^-_Phi (pi)$: all promise events from which $pi$ is reachable along $+L$ (everything that can possibly influence $pi$—its exact *causal ancestry*).

@fig-microgrid illustrates this projection directly on the Hospital Microgrid from §2.1: the left side shows the voluntary promise network; the right side shows its canonical $gamma(3,4)$ image $Phi(cal(S))$, revealing cleanly why `factory`'s monitoring lies strictly outside $J^-_Phi ("hospital:power")$.

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
      columns: (0.86fr, auto, 1.56fr),
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
          *`battery`*: `-sense` (mains)\
          `+backup` $|$ `not Assisted(sense)`
        ]
        #v(4pt)
        #grid(
          columns: (1fr, 1fr),
          gutter: 5pt,
          block(width: 100%, fill: greenbg, stroke: 0.6pt + greenedge, inset: 4.5pt, radius: 2pt)[
            *`hospital`*\
            `-use_power`\
            (mains / bat)
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
          #align(left)[*Things ($t$)*: `mains`, `battery`, `hospital`, `factory` #h(1fr) _($e arrow.r^(+C) t$)_]
        ]
        #v(4pt)
        // Events layer with shaded reverse light cone
        #grid(
          columns: (1.72fr, 0.80fr),
          gutter: 5pt,
          block(
            width: 100%,
            fill: greenbg,
            stroke: (paint: greenedge, thickness: 1.0pt, dash: "dashed"),
            inset: 4.5pt,
            radius: 3pt,
          )[
            #align(left)[#text(size: 7.3pt, weight: "bold", fill: greenedge)[Events ($e$) inside $J^-_Phi ("hospital:use_power")$]]
            #v(3pt)
            #text(size: 6.9pt)[`mains:power` $arrow.r^(+L)$ `bat:sense` $arrow.r^(+L)$ `bat:backup`]\
            #text(size: 6.9pt)[`mains:power`, `bat:backup` $arrow.r^(+L)$ *`hospital:use_power`*]
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
  caption: [Canonical projection $Phi$ of the Hospital Microgrid into strict Semantic Spacetime $gamma(3,4)$. Even across the negated failover link `bat:sense` $arrow.r^(+L)$ `bat:backup`, Law III guarantees that any perturbation to `factory:monitor` (outside the dashed reverse causal light cone $J^-$) leaves `hospital:use_power` strictly invariant.],
) <fig-microgrid>

Complementing $Phi$, every superagent $S$ also induces a *coarse-graining directory* $pi_"directory" (S)$ @burgess2015spacetimes2 (Def. L1736), partitioning $S$'s interior sub-agents and interior promises from the explicit surface promises visible to external observers.

// ============================================================================
// Section 5
// ============================================================================

= Generalized Valency and Composable System Laws

Bilateral promise resolution tells us *which* voluntary relationships are locally active. Yet real systems also obey *collective capacity and coordination laws* across a set of simultaneous bindings—such as the hospital battery's 1500 W inverter limit, a port allocator preventing two containers from binding TCP port 443 on the same host, or a fleet agreeing on one wire protocol version.

Rather than baking a closed menu of special-case binding modes into the core calculus, Baugr expresses collective invariants through two minimal, open algebraic abstractions:

+ *Monoidal Promise Valency (`+b#n`):* Burgess introduces *Promise Valency* @burgess2015spacetimes2 (§2.7) to describe how many simultaneous consumers an offer can sustain—from *exclusive* ("fermionic", `#1`, like a hardware lock or dedicated port), to *bounded capacity* (`#1500W`, `#8` replicas), to *unlimited broadcast* ("bosonic", `#∞`, like a public time signal). Baugr observes that all of these are instances of a single algebraic structure: an *Ordered Commutative Monoid* $(R, 0, +, <=)$, where $(0, +)$ is a commutative monoid, $<=$ is a preorder with $0 <= x$, and $+$ is monotone in both arguments. Every active binding contributes a cost $w in R$, and an offer with capacity $c in R$ satisfies valency iff $sum w_i <= c$. Because Cartesian products of ordered commutative monoids are again ordered commutative monoids, multi-dimensional budgets—such as `("CPU millicores", "RAM MiB")`—fall out for free with zero extra machinery. Moreover, monotonicity guarantees *withdrawal safety*: if an agent voluntarily withdraws a binding, a valid system can never become overloaded.
+ *Open Composable Scope Laws:* Any global or scoped system invariant is simply a predicate over the resolved system (returning typed diagnostics on violation) closed under conjunction. Five canonical laws cover the classic patterns of distributed coordination:
  - *Valency*: every offer's cumulative monoidal load stays within its declared capacity $c in R$.
  - *Quorum*: a designated promise achieves at least $k$ active cooperative bindings.
  - *Unique Provider*: a designated consumer binds to at most one active offer.
  - *Pairwise Disjointness*: active bindings carry pairwise distinct extracted keys—for instance, mapping each binding to `(host, tcp_port)` checks port uniqueness across an entire multi-host fleet in one unified law.
  - *Coordination Agreement* $C(b)$ @burgess2014spacetimes1 (L2575): active bindings grouped by coordination domain agree on a single shared value (e.g., protocol version or consensus epoch), flagging drift across autonomous peers.

Crucially, because these laws sit *above* the core quenching semantics, users can add arbitrary domain laws without weakening any of the four universal theorems proved for the underlying calculus.

// ============================================================================
// Section 6
// ============================================================================

= The Four Universal Laws (Machine-Checked in Lean 4)

We now state the four universal laws guaranteed for *every* Promise System expressible in Baugr, explain *why* each holds mathematically, and catalog all *29 machine-checked theorems* proved in pure Lean 4 (zero external proof libraries, zero `sorryAx`).

== Law I — Non-Coercion (Axiom of Autonomy)

#lawbox("I", [Non-Coercion (`autonomy_unaccepted_offer_inert`)])[
  Let $cal(S)$ be any Promise System and suppose we extend $cal(S)$ by adding a new offer $pi_"new"$ that is not statically bindable to any existing `Use` promise in $cal(S)$ and is not already referenced by any existing `Self` or `Interior` condition. Then for *every* existing agent $a$, condition $C$, assessment $alpha$, and quenched set $Q$, evaluating $C$ in $cal(S) union \{pi_"new"\}$ yields the exact same boolean result as in $cal(S)$.
]

*Why it holds:* Every condition atom inspects either the promiser's own promises, its interior sub-agents, offers compatible with its own `Use` promises, or `Use` promises compatible with its own offers. Because $pi_"new"$ is an unaccepted offer, none of the four atoms can observe it—and by structural induction across `AtLeast` and `Not`, no compound formula can detect its presence either. In Promise Theory terms, an unaccepted imposition has zero causal power.

== Law II — Boundary Integrity (Opaque Encapsulation)

#lawbox("II", [Boundary Integrity (`opaque_non_piercing`, `opaque_interior_perturbation_contained`)])[
  Let $s$ be an opaque superagent in $cal(H)$, let $a$ be a strict interior member ($s #splus a$), and let $b$ be an exterior agent ($not (s prec.eq b)$). Then:
  + *Non-piercing (outward and inward):* Neither an offer from $a$ to $b$ nor an offer from $b$ to $a$ can ever form an active binding.
  + *Interior isolation:* If two assessments $alpha_1, alpha_2$ differ *only* on promises inside $s$ that do not lie in the reverse causal light cone $J^-_Phi (pi_"ext")$ of an exterior promise $pi_"ext"$, then $pi_"ext"$ has the identical quenched state under $alpha_1$ and $alpha_2$.
]

*Why it holds:* Part (1) follows directly from the symmetry and enforcement of `noOpaqueWall` inside `staticBindable`. Part (2) composes boundary discipline with Law III: internal changes inside an opaque superagent can affect the outside world *only* if they travel along an explicit causal path through a surface promise exposed by $s$ itself (such as `cluster`'s 2-of-3 emergent `+durable` offer in @fig-opaque).

== Law III — Causal Locality (Reverse Light-Cone Containment)

#lawbox("III", [Causal Locality (`perturbation_in_reverse_cone`)])[
  Let $alpha_1, alpha_2 : A times P -> \{bot, top\}$ be any two observer-local assessments that agree on every promise $d$ inside the Semantic Spacetime reverse causal light cone of a target promise $pi$—that is, whenever $"Promise"(d)$ can reach $"Promise"(pi)$ along dual-normalized `+LeadsTo` edges in $Phi(cal(S))$. Then for any stratification $"rank"$, step count, and top stratum, $pi$ has the exact same quenched state under $alpha_1$ and $alpha_2$.
]

*Why it holds:* This is the centerpiece theorem linking operational promise semantics to Semantic Spacetime geometry. First, a local congruence lemma proves that evaluating any condition $C$ depends solely on the quenched states and local assessments of its syntactic dependencies $d in "condDeps"(C)$ present in $cal(S)$. Second, the functor $Phi$ emits a `+LeadsTo` edge $"Promise"(d) arrow.r^(+L) "Promise"(p)$ for every such dependency—regardless of whether $d$ appears positively or under negation! Therefore, by induction over strata and fixed-point iterations, any assessment perturbation outside $J^-_Phi (pi)$ is causally unreachable from $pi$. Even non-monotonic failover rules cannot violate the speed-of-light causal boundary encoded in $Phi(cal(S))$.

== Law IV — Order Independence (Apt–Blair–Walker via Light Cones)

#lawbox("IV", [Order Independence (`stratification_independent`)])[
  Let $"rank"_1, "rank"_2 : P -> NN$ be *any* two valid stratifications of $cal(S)$ bounded by $M_1, M_2$, and let each stratum iterate at least $|P|+1$ times. Then evaluating $cal(S)$ under $"rank"_1$ and under $"rank"_2$ converges to the *exact same* global fixed point of $T_alpha$:
  $ "evalStratified"(cal(S), alpha, "rank"_1, M_1) = "evalStratified"(cal(S), alpha, "rank"_2, M_2). $
]

*Proof insight (geometry proves semantics):* While Apt, Blair, and Walker's classic theorem @apt1988stratified is traditionally proved via Herbrand interpretations and transfinite operators, Baugr's coupling with Semantic Spacetime yields a remarkably crisp constructive proof in three steps:
+ *Polarity-indexed monotonicity:* Under arbitrarily nested negations, condition evaluation is monotone in even-parity dependencies and antitone in odd-parity dependencies. Within stratum $s$, every odd-parity dependency sits strictly below $s$ and is frozen, so the per-stratum operator is monotone.
+ *Finite pigeonhole convergence:* On a finite system of $|P|$ promises, the count of quenched promises along an ascending chain can increase at most $|P|$ times; thus every stratum freezes at its exact Knaster–Tarski least fixed point within $|P|+1$ iterations, assembling into a global fixed point of $T_alpha$.
+ *Symmetric light-cone induction:* Every causal path in $Phi(cal(S))$ is non-decreasing in *any* valid rank. By strong induction on $k = "rank"_1 (p) + "rank"_2 (p)$, to compare the two solutions $F_1$ and $F_2$ at promise $p$, we construct a pre-fixed point $G$ matching the lower strata below $"rank"_1 (p)$, matching $F_2$ on the reverse light cone $J^-_Phi (p)$ at stratum $"rank"_1 (p)$, and returning $top$ outside $J^-_Phi (p)$. Knaster–Tarski leastness forces $F_1 (p) <= F_2 (p)$, and symmetry gives $F_2 (p) <= F_1 (p)$.

== Complete Machine-Checked Theorem Catalog

@tab-theorems lists all *29 audited theorems* verified in pure Lean 4 (`lean4` 4.35.0, zero `Mathlib`, `0` warnings, `0 sorryAx`). Every theorem depends strictly on Lean's standard logical foundations (`propext`, `Quot.sound`, and where classical decidability enters, `Classical.choice`).

#figure(
  placement: top,
  {
    set text(size: 8.0pt)
    show raw: text.with(size: 7.2pt)
    table(
      columns: (auto, 1.60fr, 1.82fr, auto),
      inset: 3.8pt,
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
      [Law IV], [`stratification_independent`], [*Order Independence*: any two valid stratifications yield the same fixed point.], [`P, C, Q`],
      [Law I], [`autonomy_unaccepted_offer_inert`], [*Non-Coercion*: unaccepted offers/impositions cannot alter any condition.], [`P, Q`],
      [Law III], [`projectSst_wellFormed`], [Canonical functor $Phi : "PromiseSystem" -> gamma(3,4)$ is always well-formed.], [`P, Q`],
      [Law III], [`perturbation_in_reverse_cone`], [*Causal Locality*: assessment perturbations outside $J^-_Phi (pi)$ leave $pi$ invariant.], [`P, Q`],
      [Law II], [`noOpaqueWall_symm`], [Opaque boundary non-piercing predicate is symmetric.], [`P, Q`],
      [Law II], [`opaque_non_piercing`, \ `opaque_non_piercing_inward`], [*Boundary Integrity*: opaque superagents block outward & inward piercing.], [`P, C, Q`],
      [Law II], [`opaque_interior_perturbation_` \ `contained`], [Interior perturbations of an opaque superagent stay contained outside $J^-$.], [`P, Q`],
      [Valency], [`valency_withdrawal_safe`], [Monoidal valency is downward-closed under voluntary binding withdrawal.], [`P`],
      [Laws], [`allLaws_cons`], [Open `ScopeLaw` conjunction composes soundly.], [`P, Q`],
    )
  },
  caption: [Complete catalog of all 29 audited Lean 4 theorems (`0 sorryAx`, zero `Mathlib`). Axioms: `P` = `propext`, `Q` = `Quot.sound`, `C` = `Classical.choice`.],
) <tab-theorems>

// ============================================================================
// Section 7
// ============================================================================

= Positioning and Comparison to Existing Systems

Does anything like Baugr already exist? To answer accurately, we surveyed five neighboring ecosystems: existing Promise Theory / SST implementations, Assume–Guarantee contract frameworks, Stratified Datalog and Answer Set Programming engines, relational/temporal model checkers, and categorical graph libraries. @tab-compare summarizes the landscape honestly, including where each neighboring tool strictly outperforms Baugr.

#figure(
  placement: top,
  {
    set text(size: 7.7pt)
    table(
      columns: (1.05fr, 0.55fr, 0.55fr, 0.55fr, 0.6fr, 0.8fr, 1.35fr),
      inset: 4pt,
      align: (left, center, center, center, center, left, left),
      stroke: (x: none, y: 0.4pt + luma(200)),
      fill: (_, row) => if row == 0 { softbg } else { none },
      [*System / Paradigm*], [*Voluntary `+`/`-` & Autonomy*], [*Observer Subjectivity*], [*Opaque Walls*], [*SST $gamma(3,4)$*], [*Machine Proofs*], [*Where It Beats Baugr*],
      [*Baugr v0.2*], [*Yes* (Law I)], [*Yes* (Law III)], [*Yes* (Law II)], [*Yes* (strict)], [Lean 4 (29 thms) + DRT], [Minimal verified autonomy + causal-geometry kernel],
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
// Section 8
// ============================================================================

= Verified Realization and Empirical Validation

To make the calculus directly usable inside real software systems without sacrificing formal rigor, Baugr follows the *Verification-Guided Development* (VGD) methodology pioneered by AWS Cedar @cutler2024cedar: rather than relying on fragile automated code extraction, we maintain two clean, mirroring artifacts mechanically locked together by differential testing.

- *Formal Kernel (Lean 4):* Four small specification modules mirroring §§3–5 (`Spacetime`, `Promise`, `Projection`, `Law`) and seven proof modules verifying all 29 theorems of @tab-theorems with zero `Mathlib` and zero `sorryAx`, compiled offline into an executable reference oracle.
- *Executable Library (Rust):* A zero-runtime-dependency, `#![no_std]` (`alloc`), `#![forbid(unsafe_code)]` Rust crate exposing the exact four mathematical modules. Structural invariants—acyclic superagent containment, consistent $gamma(3,4)$ node typing, and strict transition admissibility—are enforced at mutation time; overwriting an existing promise ID returns the displaced promise explicitly rather than discarding it silently; a precomputed static compatibility index avoids repeated overlap and wall checks during fixed-point iteration; a static `lint()` pass flags dangling references, wrong promisers, polarity mismatches, non-interior sub-agent checks, and incomplete-information scopes; and zero-annotation helpers (`check_valency`, `check_disjoint`, `check_agreement`) keep common law checks concise.
- *Closing the Verification Loop via Oracle-Verified DRT:* In production execution, Rust computes minimal strata via Kosaraju's strongly connected component algorithm. Rather than trusting that algorithm blindly, our differential test suite generates *500 randomized stratifiable Promise Systems*—incorporating random opaque/transparent hierarchies, bitmask mutual-information overlap, positive dependency cycles, nested `AtLeast` thresholds, *arbitrarily nested negations* (`not (AtLeast(..., [not ...]))`), and broken observer-local assessments—and sends each system *together with Rust's computed stratification* to the compiled Lean 4 oracle. On every single case, Lean mechanically executes our proved-sound `checkValidStratification` validator (rejecting any invalid rank with a hard failure) before verifying bit-for-bit agreement between Rust and Lean across all quenched promises, active bindings (including exact overlap values), and projected $gamma(3,4)$ edges (`0` divergences across 500/500 cases).
- *Cross-Domain Validation:* Three self-contained runnable examples exercise the library across unrelated domains—the *Hospital Microgrid* (failover negation, split blackout, wattage valency), the *Opaque Raft Cluster* (2-of-3 quorum emergence, blocked piercing, light-cone isolation), and *Multi-Tenant Cloud Tenancy* (`Accepted` tenancy, simultaneous fleet-wide per-host port disjointness, and Burgess coordination agreement $C(b)$)—alongside an automated purity check confirming zero domain-specific terms or operating-system I/O inside the core library.

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
      [@burgess2014spacetimes1], [Mutual-information overlap $b_1 inter b_2$; assisted quenching; coordination $C(b)$], [Body algebra; `Assisted`; `AgreementBy`],
      [@burgess2015spacetimes2], [Valency `+b#n`; opaque/transparent superagents; directories $pi_"directory"$; emergence; tenancy; incomplete info], [Ordered monoid valency; `Hierarchy` & Law II; `Interior`/`Accepted`; complete-info check],
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
