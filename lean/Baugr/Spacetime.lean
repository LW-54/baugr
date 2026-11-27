/-
  Baugr.Spacetime — Strict Semantic Spacetime γ(3,4) Algebra
  Derived directly from Mark Burgess (2025, arXiv:2506.07756v2 §§3-5).
-/

namespace Baugr

/-- The 3 node meta-types of Semantic Spacetime γ(3,4) (arXiv:2506.07756v2 §3.2). -/
inductive NodeKind where
  | event   -- e: ephemeral, realized, timelike process agent
  | thing   -- t: invariant, realized, spacelike persistent agent
  | concept -- c: persistent, unrealized, virtual attribute / property / intent
  deriving DecidableEq, Repr

/-- The 4 signed link meta-types of Semantic Spacetime γ(3,4) (arXiv:2506.07756v2 §3.1, Table 1). -/
inductive LinkKind where
  | near        --  0: symmetric proximity / similarity (N)
  | leadsTo     -- +1: causal / temporal precedence (+L)
  | follows     -- -1: causal / temporal dependence (-L)
  | contains    -- +2: spatial containment / membership (+C)
  | containedBy -- -2: interiority / participation (-C)
  | expresses   -- +3: qualitative property / promise expression (+E)
  | expressedBy -- -3: expressed-by / attribute-of (-E)
  deriving DecidableEq, Repr

/-- Exact algebraic inverse of each γ(3,4) link kind. -/
def LinkKind.inv : LinkKind → LinkKind
  | .near        => .near
  | .leadsTo     => .follows
  | .follows     => .leadsTo
  | .contains    => .containedBy
  | .containedBy => .contains
  | .expresses   => .expressedBy
  | .expressedBy => .expresses

/-- Strict γ(3,4) forward transition rules (arXiv:2506.07756v2 Rules 1-2, L614-624, L1234-1245):
    - Near (0): strictly homogeneous (`e-e`, `t-t`, `c-c`)
    - +LeadsTo (+1): strictly `event → event`
    - +Contains (+2): realized non-ascending (`e→e`, `e→t`, `t→t`; concepts never contained)
    - +Expresses (+3): target is strictly `concept` (`e→c`, `t→c`, `c→c`; things never expressed). -/
def allowedPos : NodeKind → LinkKind → NodeKind → Bool
  | k₁,     .near,      k₂       => decide (k₁ = k₂)
  | .event, .leadsTo,   .event   => true
  | .event, .contains,  .event   => true
  | .event, .contains,  .thing   => true
  | .thing, .contains,  .thing   => true
  | _,      .expresses, .concept => true
  | _,      _,          _        => false

/-- Full signed γ(3,4) admissibility predicate (negative links are exact converses). -/
def allowed (u : NodeKind) (r : LinkKind) (v : NodeKind) : Bool :=
  match r with
  | .near | .leadsTo | .contains | .expresses => allowedPos u r v
  | .follows | .containedBy | .expressedBy    => allowedPos v r.inv u

/-- A directed typed edge in a Semantic Spacetime graph. -/
structure SstEdge (N : Type) where
  src  : N
  kind : LinkKind
  dst  : N
  deriving DecidableEq, Repr

/-- A Semantic Spacetime γ(3,4) graph with node meta-typing. -/
structure SstGraph (N : Type) where
  kindOf : N → NodeKind
  edges  : List (SstEdge N)

/-- Well-formedness: every edge obeys the strict γ(3,4) transition rules. -/
def SstGraph.WellFormed {N : Type} (g : SstGraph N) : Prop :=
  ∀ e ∈ g.edges, allowed (g.kindOf e.src) e.kind (g.kindOf e.dst) = true

/-- Normalized directed edge relation honoring γ(3,4) link inversion
    (`u --r--> v` directly, or `v --r⁻¹--> u` via its algebraic converse). -/
def SstGraph.hasEdge {N : Type} (g : SstGraph N) (u : N) (r : LinkKind) (v : N) : Prop :=
  SstEdge.mk u r v ∈ g.edges ∨ SstEdge.mk v r.inv u ∈ g.edges

/-- Directed causal reachability along normalized `+LeadsTo` edges (honoring dual `-Follows`). -/
inductive CausalReach {N : Type} (g : SstGraph N) : N → N → Prop where
  | refl (x : N) : CausalReach g x x
  | step {x y z : N} :
      g.hasEdge x .leadsTo y →
      CausalReach g y z →
      CausalReach g x z

theorem CausalReach.trans {N : Type} {g : SstGraph N} {x y z : N}
    (h1 : CausalReach g x y) (h2 : CausalReach g y z) : CausalReach g x z := by
  induction h1 with
  | refl _ => exact h2
  | step hedge _ ih => exact .step hedge (ih h2)

/-- Quotient coarse-graining functor G on an SST graph (arXiv:1505.01716v1 §3.5, arXiv:2506.07756v2 §4.4):
    collapses nodes via `f : N → M`, drops interior self-loops (`f src = f dst`),
    and preserves exterior edges with quotient node kinds `qKind`. -/
def SstGraph.coarseGrain {N M : Type} [DecidableEq M]
    (g : SstGraph N) (f : N → M) (qKind : M → NodeKind) : SstGraph M :=
  { kindOf := qKind
    edges  := g.edges.filterMap fun e =>
      let s := f e.src
      let d := f e.dst
      if s == d then none else some { src := s, kind := e.kind, dst := d } }

end Baugr
