/-
  Baugr.Promise — Pure Promise Theory Core
  Derived directly from Bergstra & Burgess:
    - 0810.3294v5 (Scope, Relative/Absolute Keeping, Assessment)
    - 1401.3381v1 (2 Polarities, Compliance as Conditional Promise, Scope ∋ Promiser)
    - 1411.5563   (Body Overlap b₁ ∩ b₂, Assisted Quenching)
    - 1505.01716v1 (Superagents, Opaque vs. Transparent, Irreducible Promises, Tenancy)
    - 2606.08552v1 (Observer-Local Assessment α_a(π), Self & Assisted Quenching)
-/

namespace Baugr

/-- Polarity + typed body unified so illegal states are unrepresentable (ADR-0018 A1). -/
inductive Body (O U : Type) where
  | offer (o : O) -- +b: assertion / offer
  | use   (u : U) -- -b: acceptance / use
  deriving DecidableEq, Repr

/-- Mutual-information body pairing `b₁ ∩ b₂` (arXiv:1411.5563 L2289, arXiv:2606.08552v1 L616). -/
structure BodyAlgebra (O U M : Type) where
  overlap : O → U → Option M

/-- Decidable set of agents (used for promisee `target` and observability `scope`). -/
abbrev AgentSet (A : Type) := A → Bool

/-- Condition formula on a promise (autonomy-grounded local atoms + monotone `atLeast` + stratified `not`). -/
inductive Cond (P : Type) where
  | selfPromise (q : P)
  | assisted    (useId : P) (minProviders : Nat)
  | accepted    (offerId : P) (minAcceptors : Nat)
  | interior    (q : P)
  | atLeast     (k : Nat) (cs : List (Cond P))
  | not         (c : Cond P)

def Cond.always {P : Type} : Cond P := .atLeast 0 []
def Cond.all {P : Type} (cs : List (Cond P)) : Cond P := .atLeast cs.length cs
def Cond.any {P : Type} (cs : List (Cond P)) : Cond P := .atLeast 1 cs

mutual
def Cond.isPositive {P : Type} : Cond P → Prop
  | .selfPromise _ | .assisted _ _ | .accepted _ _ | .interior _ => True
  | .atLeast _ cs => Cond.listPositive cs
  | .not _        => False

def Cond.listPositive {P : Type} : List (Cond P) → Prop
  | []      => True
  | c :: cs => c.isPositive ∧ Cond.listPositive cs
end

/-- Dressed superagent hierarchy with explicit opaque vs. transparent boundary flag (arXiv:1505.01716v1 §3.3-3.7). -/
structure Hierarchy (A : Type) where
  parent   : A → Option A
  isOpaque : A → Bool

/-- `isStrictAncAux h n s a`: `s` is a strict ancestor superagent of `a` within `n` steps. -/
def isStrictAncAux {A : Type} [DecidableEq A] (h : Hierarchy A) : Nat → A → A → Bool
  | 0,     _, _ => false
  | n + 1, s, a =>
      match h.parent a with
      | none   => false
      | some p => if p = s then true else isStrictAncAux h n s p

/-- Non-piercing encapsulation predicate (arXiv:1505.01716v1 §3.7):
    `a` and `b` do not cross an opaque superagent wall. -/
def noOpaqueWall {A : Type} [DecidableEq A] (h : Hierarchy A) (agents : List A) (a b : A) : Bool :=
  let depth := agents.length
  let isIn (s x : A) := (x = s) || isStrictAncAux h depth s x
  agents.all fun s =>
    if h.isOpaque s then
      let aStrict := isStrictAncAux h depth s a
      let bStrict := isStrictAncAux h depth s b
      (!aStrict || isIn s b) && (!bStrict || isIn s a)
    else
      true

/-- A directed conditional promise with explicit promisee `target` and observability `scope`. -/
structure Promise (A P O U : Type) where
  id       : P
  promiser : A
  target   : AgentSet A
  scope    : AgentSet A
  body     : Body O U
  cond     : Cond P

def Promise.isOffer {A P O U : Type} (pr : Promise A P O U) : Bool :=
  match pr.body with
  | .offer _ => true
  | .use   _ => false

def Promise.isUse {A P O U : Type} (pr : Promise A P O U) : Bool :=
  match pr.body with
  | .offer _ => false
  | .use   _ => true

/-- Effective scope always includes the promiser (arXiv:1401.3381v1 L663). -/
def inScope {A P O U : Type} [DecidableEq A] (pr : Promise A P O U) (obs : A) : Bool :=
  (obs == pr.promiser) || pr.scope obs

/-- Complete Promise System. -/
structure PromiseSystem (A P O U M : Type) where
  agents    : List A
  promises  : List (Promise A P O U)
  hierarchy : Hierarchy A
  algebra   : BodyAlgebra O U M

/-- Observer-local Boolean assessment α : Agent × Promise → Bool (ADR-0018 A3; arXiv:2606.08552v1 L1070). -/
abbrev Assessment (A P : Type) := A → P → Bool

def PromiseSystem.find? {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pid : P) : Option (Promise A P O U) :=
  sys.promises.find? (fun pr => pr.id == pid)

/-- Static compatibility of an offer `po` and a use `pu`:
    - `po` is `Offer(ob)` and `pu` is `Use(ub)` with non-empty `overlap ob ub`
    - mutual targeting + offer visible in `scope` to consumer
    - no opaque superagent wall pierced. -/
def staticBindable {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M)
    (po pu : Promise A P O U) : Bool :=
  match po.body, pu.body with
  | .offer ob, .use ub =>
      po.target pu.promiser &&
      inScope po pu.promiser &&
      pu.target po.promiser &&
      noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser &&
      (sys.algebra.overlap ob ub).isSome
  | _, _ => false

def countP {α : Type} (p : α → Bool) : List α → Nat
  | []      => 0
  | x :: xs => (if p x then 1 else 0) + countP p xs

mutual
/-- Evaluate condition `c` for promiser `me` under quenched set `Q` and local assessment `α`. -/
def evalCond {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q : P → Bool) (me : A) : Cond P → Bool
  | .selfPromise q =>
      match sys.find? q with
      | some pq => (pq.promiser == me) && Q q && α me q
      | none    => false
  | .assisted u minP =>
      match sys.find? u with
      | some pu =>
          if pu.promiser == me && pu.isUse && Q u then
            let n := countP (fun po =>
              staticBindable sys po pu && Q po.id && α me po.id) sys.promises
            decide (n ≥ minP)
          else false
      | none => false
  | .accepted o minA =>
      match sys.find? o with
      | some po =>
          if po.promiser == me && po.isOffer && Q o then
            let n := countP (fun pu =>
              staticBindable sys po pu && inScope pu me && Q pu.id && α me pu.id) sys.promises
            decide (n ≥ minA)
          else false
      | none => false
  | .interior q =>
      match sys.find? q with
      | some pq =>
          isStrictAncAux sys.hierarchy sys.agents.length me pq.promiser && Q q && α me q
      | none => false
  | .atLeast k cs =>
      decide (countSat sys α Q me cs ≥ k)
  | .not c => !(evalCond sys α Q me c)

def countSat {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q : P → Bool) (me : A) : List (Cond P) → Nat
  | []      => 0
  | c :: rs => (if evalCond sys α Q me c then 1 else 0) + countSat sys α Q me rs
end

/-- One-step quenching operator T(Q). -/
def quenchStep {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q : P → Bool) (pid : P) : Bool :=
  match sys.find? pid with
  | some pr => evalCond sys α Q pr.promiser pr.cond
  | none    => false

def SubSet {P : Type} (Q₁ Q₂ : P → Bool) : Prop :=
  ∀ p, Q₁ p = true → Q₂ p = true

def PositiveSystem {A P O U M : Type} (sys : PromiseSystem A P O U M) : Prop :=
  ∀ pr ∈ sys.promises, pr.cond.isPositive

/-- Iterate quenching from empty set ⊥ for `n` steps (Knaster-Tarski approximation). -/
def quenchIter {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) : Nat → (P → Bool)
  | 0     => fun _ => false
  | n + 1 => quenchStep sys α (quenchIter sys α n)

mutual
/-- Syntactic condition dependencies `(depId, isNegative)` for stratification & SST projection. -/
def condDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (neg : Bool) : Cond P → List (P × Bool)
  | .selfPromise q => [(q, neg)]
  | .assisted u _  =>
      match sys.find? u with
      | some pu =>
          (u, neg) :: (sys.promises.filter (fun po => staticBindable sys po pu)).map (fun po => (po.id, neg))
      | none => [(u, neg)]
  | .accepted o _  =>
      match sys.find? o with
      | some po =>
          (o, neg) :: (sys.promises.filter (fun pu => staticBindable sys po pu && inScope pu po.promiser)).map (fun pu => (pu.id, neg))
      | none => [(o, neg)]
  | .interior q    => [(q, neg)]
  | .atLeast _ cs  => listCondDeps sys neg cs
  | .not c         => condDeps sys (!neg) c

def listCondDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (neg : Bool) : List (Cond P) → List (P × Bool)
  | []      => []
  | c :: rs => condDeps sys neg c ++ listCondDeps sys neg rs
end

/-- Valid stratification: positive deps have `rank dep ≤ rank p`, negative deps `rank dep < rank p`. -/
def ValidStratification {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (rank : P → Nat) : Prop :=
  ∀ pr ∈ sys.promises, ∀ dep neg, (dep, neg) ∈ condDeps sys false pr.cond →
    if neg then rank dep < rank pr.id else rank dep ≤ rank pr.id

/-- Executable validator for `ValidStratification` (verified sound by `checkValidStratification_sound`). -/
def checkValidStratification {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (rank : P → Nat) : Bool :=
  sys.promises.all fun pr =>
    (condDeps sys false pr.cond).all fun (dep, neg) =>
      if neg then decide (rank dep < rank pr.id) else decide (rank dep ≤ rank pr.id)

def stratumStep {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : P → Bool) (Q : P → Bool) (pid : P) : Bool :=
  if rank pid < s then base pid
  else if rank pid == s then quenchStep sys α Q pid
  else false

def stratumIter {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : P → Bool) : Nat → (P → Bool)
  | 0     => fun pid => if rank pid < s then base pid else false
  | n + 1 => stratumStep sys α rank s base (stratumIter sys α rank s base n)

/-- Stratified fixed-point evaluator across strata `0 .. maxS`. -/
def evalStratified {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (stepsPerStratum : Nat) : Nat → (P → Bool)
  | 0     => stratumIter sys α rank 0 (fun _ => false) stepsPerStratum
  | s + 1 =>
      let prev := evalStratified sys α rank stepsPerStratum s
      stratumIter sys α rank (s + 1) prev stepsPerStratum

/-- Active bindings `(offerId, useId)` under resolved quenched set `Q` and local assessment `α`. -/
def activeBindings {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (Q : P → Bool) : List (P × P) :=
  sys.promises.flatMap fun po =>
    if po.isOffer && Q po.id then
      sys.promises.filterMap fun pu =>
        if pu.isUse && Q pu.id && staticBindable sys po pu && α pu.promiser po.id then
          some (po.id, pu.id)
        else none
    else []

end Baugr
