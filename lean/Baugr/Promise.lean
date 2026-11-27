/-
  Baugr.Promise — Pure Promise Theory Core (with Value-Dependent Conditional Promises)
  Derived directly from Bergstra & Burgess:
    - 0810.3294v5 (Scope, Relative/Absolute Keeping, Assessment)
    - 1401.3381v1 (2 Polarities, Compliance as Conditional Promise, Scope ∋ Promiser)
    - 1411.5563   (Body Overlap b₁ ∩ b₂, Assisted Quenching)
    - 1505.01716v1 (Superagents, Opaque vs. Transparent, Irreducible Promises, Tenancy +f(C,R)|-R)
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

/-- Autonomy-grounded local observation selector for value-derived promises (`+f(obs) | C`,
    arXiv:1505.01716v1 §4.1). Mirrors the exact four autonomy-grounded atoms of `Cond`. -/
inductive Obs (P : Type) where
  | selfPromise (q : P)
  | assisted    (useId : P)
  | accepted    (offerId : P)
  | interior    (q : P)
  deriving DecidableEq, Repr

/-- Local autonomy-grounded values exposed to a derived promise's body function. -/
structure LocalObs (A P O U M : Type) where
  selfBodies     : List (P × Body O U)
  assistedOffers : List (P × P × A × O × M)
  acceptedUses   : List (P × P × A × U × M)
  interiorBodies : List (P × A × Body O U)

/-- Orthogonal static-vs-derived body specification: polarity lives exclusively on `Body`. -/
inductive Spec (A P O U M T : Type) where
  | fixed   (val : T)
  | derived (obs : List (Obs P)) (produce : LocalObs A P O U M → Option T)

def Spec.obs {A P O U M T : Type} : Spec A P O U M T → List (Obs P)
  | .fixed _        => []
  | .derived os _   => os

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

/-- A directed conditional promise with explicit promisee `target`, observability `scope`,
    unified polarity/specification `body : Body (Spec ... O) (Spec ... U)`, and condition `cond`. -/
structure Promise (A P O U M : Type) where
  id       : P
  promiser : A
  target   : AgentSet A
  scope    : AgentSet A
  body     : Body (Spec A P O U M O) (Spec A P O U M U)
  cond     : Cond P

def Promise.isOffer {A P O U M : Type} (pr : Promise A P O U M) : Bool :=
  match pr.body with
  | .offer _ => true
  | .use   _ => false

def Promise.isUse {A P O U M : Type} (pr : Promise A P O U M) : Bool :=
  match pr.body with
  | .offer _ => false
  | .use   _ => true

def Promise.obs {A P O U M : Type} (pr : Promise A P O U M) : List (Obs P) :=
  match pr.body with
  | .offer sp => sp.obs
  | .use   sp => sp.obs

/-- Effective scope always includes the promiser (arXiv:1401.3381v1 L663). -/
def inScope {A P O U M : Type} [DecidableEq A] (pr : Promise A P O U M) (obs : A) : Bool :=
  (obs == pr.promiser) || pr.scope obs

/-- Complete Promise System.
    `ruleCompat` provides optional conservative channel filtering between promise pairs
    when at least one endpoint is value-derived (defaults to `true`, mirroring Rust's
    `DeriveAlgebra::may_overlap`). -/
structure PromiseSystem (A P O U M : Type) where
  agents     : List A
  promises   : List (Promise A P O U M)
  hierarchy  : Hierarchy A
  algebra    : BodyAlgebra O U M
  ruleCompat : P → P → Bool := fun _ _ => true

/-- Uniqueness of promise identifiers in `sys.promises` (guaranteed by Rust's `BTreeMap`). -/
def UniqueIds {A P O U M : Type} (sys : PromiseSystem A P O U M) : Prop :=
  ∀ p₁ ∈ sys.promises, ∀ p₂ ∈ sys.promises, p₁.id = p₂.id → p₁ = p₂

/-- Observer-local Boolean assessment α : Agent × Promise → Bool (ADR-0018 A3; arXiv:2606.08552v1 L1070). -/
abbrev Assessment (A P : Type) := A → P → Bool

/-- Resolved state mapping each promise to `none` (unquenched) or `some body` (quenched with effective body). -/
abbrev State (P O U : Type) := P → Option (Body O U)

def PromiseSystem.find? {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pid : P) : Option (Promise A P O U M) :=
  sys.promises.find? (fun pr => pr.id == pid)

/-- Structural offer-to-use compatibility independent of dynamic body values:
    opposite polarity, mutual targeting, offer visible in scope, and no opaque wall pierced. -/
def structBindable {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po pu : Promise A P O U M) : Bool :=
  po.isOffer &&
  pu.isUse &&
  po.target pu.promiser &&
  inScope po pu.promiser &&
  pu.target po.promiser &&
  noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser

/-- Conservative static bindability for stratification, SST projection, and autonomy:
    checks exact `overlap` when both bodies are fixed, and `ruleCompat` when either is derived. -/
def mayBind {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po pu : Promise A P O U M) : Bool :=
  if !structBindable sys po pu then false
  else match po.body, pu.body with
    | .offer (.fixed ob), .use (.fixed ub) => (sys.algebra.overlap ob ub).isSome
    | .offer _,           .use _           => sys.ruleCompat po.id pu.id
    | _,                  _                => false

/-- Runtime mutual-information overlap `b₁ ∩ b₂` under resolved state `S`. -/
def runtimeOverlap {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (S : State P O U)
    (po pu : Promise A P O U M) : Option M :=
  if !mayBind sys po pu then none
  else match S po.id, S pu.id with
    | some (.offer ob), some (.use ub) => sys.algebra.overlap ob ub
    | _, _                             => none

def countP {α : Type} (p : α → Bool) : List α → Nat
  | []      => 0
  | x :: xs => (if p x then 1 else 0) + countP p xs

/-- Deduplicate a list preserving first occurrence (mirrors Rust's `BTreeSet<Obs<P>>` uniqueness). -/
def dedupList {α : Type} [DecidableEq α] : List α → List α
  | []      => []
  | x :: xs => x :: (dedupList xs).filter (fun y => !(y == x))

/-- Direct visible interior relation: `me` strictly contains `sub` with NO intermediate
    opaque superagent wall separating them (enforces recursive Russian-doll Law II). -/
def visibleInterior {A : Type} [DecidableEq A]
    (h : Hierarchy A) (agents : List A) (me sub : A) : Bool :=
  isStrictAncAux h agents.length me sub && noOpaqueWall h agents me sub

mutual
/-- Evaluate condition `c` for promiser `me` under resolved state `S` and local assessment `α`.
    Enforces local self-assessment `α me own` across all observations AND recursive
    `noOpaqueWall` across `interior`. -/
def evalCond {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (me : A) : Cond P → Bool
  | .selfPromise q =>
      match sys.find? q with
      | some pq => (pq.promiser == me) && (S q).isSome && α me q
      | none    => false
  | .assisted u minP =>
      match sys.find? u with
      | some pu =>
          if pu.promiser == me && pu.isUse && (S u).isSome && α me u then
            let n := countP (fun po =>
              (runtimeOverlap sys S po pu).isSome && α me po.id) sys.promises
            decide (n ≥ minP)
          else false
      | none => false
  | .accepted o minA =>
      match sys.find? o with
      | some po =>
          if po.promiser == me && po.isOffer && (S o).isSome && α me o then
            let n := countP (fun pu =>
              (runtimeOverlap sys S po pu).isSome && inScope pu me && α me pu.id) sys.promises
            decide (n ≥ minA)
          else false
      | none => false
  | .interior q =>
      match sys.find? q with
      | some pq =>
          visibleInterior sys.hierarchy sys.agents me pq.promiser && (S q).isSome && α me q
      | none => false
  | .atLeast k cs =>
      decide (countSat sys α S me cs ≥ k)
  | .not c => !(evalCond sys α S me c)

def countSat {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (me : A) : List (Cond P) → Nat
  | []      => 0
  | c :: rs => (if evalCond sys α S me c then 1 else 0) + countSat sys α S me rs
end

/-- Constructs the deduplicated autonomy-grounded local observation snapshot for a derived promise. -/
def buildLocalObs {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (me : A) (obs : List (Obs P)) : LocalObs A P O U M :=
  let uobs := dedupList obs
  let selfBodies := uobs.filterMap fun o =>
    match o with
    | .selfPromise q =>
        match sys.find? q, S q with
        | some pq, some b => if pq.promiser == me && α me q then some (q, b) else none
        | _, _ => none
    | _ => none
  let assistedOffers := uobs.flatMap fun o =>
    match o with
    | .assisted u =>
        match sys.find? u, S u with
        | some pu, some (.use _) =>
            if pu.promiser == me && pu.isUse && α me u then
              sys.promises.filterMap fun po =>
                match runtimeOverlap sys S po pu, S po.id with
                | some m, some (.offer ob) =>
                    if α me po.id then some (u, po.id, po.promiser, ob, m) else none
                | _, _ => none
            else []
        | _, _ => []
    | _ => []
  let acceptedUses := uobs.flatMap fun o =>
    match o with
    | .accepted oid =>
        match sys.find? oid, S oid with
        | some po, some (.offer _) =>
            if po.promiser == me && po.isOffer && α me oid then
              sys.promises.filterMap fun pu =>
                match runtimeOverlap sys S po pu, S pu.id with
                | some m, some (.use ub) =>
                    if inScope pu me && α me pu.id then some (oid, pu.id, pu.promiser, ub, m) else none
                | _, _ => none
            else []
        | _, _ => []
    | _ => []
  let interiorBodies := uobs.filterMap fun o =>
    match o with
    | .interior q =>
        match sys.find? q, S q with
        | some pq, some b =>
            if visibleInterior sys.hierarchy sys.agents me pq.promiser && α me q then
              some (q, pq.promiser, b)
            else none
        | _, _ => none
    | _ => none
  { selfBodies, assistedOffers, acceptedUses, interiorBodies }

/-- Evaluates a promise's body specification (`fixed` or `derived`) under state `S`. -/
def evalRule {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (pr : Promise A P O U M) : Option (Body O U) :=
  match pr.body with
  | .offer (.fixed o) => some (.offer o)
  | .use   (.fixed u) => some (.use u)
  | .offer (.derived obs produce) =>
      (produce (buildLocalObs sys α S pr.promiser obs)).map .offer
  | .use   (.derived obs produce) =>
      (produce (buildLocalObs sys α S pr.promiser obs)).map .use

/-- One-step value-carrying quenching operator T(S). -/
def quenchStep {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (pid : P) : Option (Body O U) :=
  match sys.find? pid with
  | some pr =>
      if evalCond sys α S pr.promiser pr.cond then
        evalRule sys α S pr
      else none
  | none => none

/-- Flat information order on resolved promise states: `S₁ ≤ S₂` iff every quenched promise
    in `S₁` remains quenched with the identical body in `S₂`. -/
def StateLe {P O U : Type} (S₁ S₂ : State P O U) : Prop :=
  ∀ p b, S₁ p = some b → S₂ p = some b

/-- A positive single-stratum system has positive conditions and no `Obs` value-derivation barriers. -/
def PositiveSystem {A P O U M : Type} (sys : PromiseSystem A P O U M) : Prop :=
  ∀ pr ∈ sys.promises, pr.cond.isPositive ∧ pr.obs = []

/-- Iterate quenching from empty state `⊥` (`fun _ => none`) for `n` steps (Knaster-Tarski). -/
def quenchIter {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) : Nat → State P O U
  | 0     => fun _ => none
  | n + 1 => quenchStep sys α (quenchIter sys α n)

mutual
/-- Exact autonomy- & boundary-guarded syntactic condition dependencies `(depId, isStrict)`.
    Structurally dead references (wrong promiser, wrong polarity, or blocked by an opaque wall)
    emit zero phantom causal edges in `Φ(S)`. -/
def condDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) (neg : Bool) : Cond P → List (P × Bool)
  | .selfPromise q =>
      match sys.find? q with
      | some pq => if pq.promiser == me then [(q, neg)] else []
      | none    => []
  | .assisted u _  =>
      match sys.find? u with
      | some pu =>
          if pu.promiser == me && pu.isUse then
            (u, neg) :: (sys.promises.filter (fun po => mayBind sys po pu)).map (fun po => (po.id, neg))
          else []
      | none => []
  | .accepted o _  =>
      match sys.find? o with
      | some po =>
          if po.promiser == me && po.isOffer then
            (o, neg) :: (sys.promises.filter (fun pu => mayBind sys po pu && inScope pu me)).map (fun pu => (pu.id, neg))
          else []
      | none => []
  | .interior q    =>
      match sys.find? q with
      | some pq => if visibleInterior sys.hierarchy sys.agents me pq.promiser then [(q, neg)] else []
      | none    => []
  | .atLeast _ cs  => listCondDeps sys me neg cs
  | .not c         => condDeps sys me (!neg) c

def listCondDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) (neg : Bool) : List (Cond P) → List (P × Bool)
  | []      => []
  | c :: rs => condDeps sys me neg c ++ listCondDeps sys me neg rs
end

/-- Exact autonomy- & boundary-guarded value-observation dependencies (`isStrict = true`). -/
def obsEntryDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) : Obs P → List (P × Bool)
  | .selfPromise q =>
      match sys.find? q with
      | some pq => if pq.promiser == me then [(q, true)] else []
      | none    => []
  | .interior q    =>
      match sys.find? q with
      | some pq => if visibleInterior sys.hierarchy sys.agents me pq.promiser then [(q, true)] else []
      | none    => []
  | .assisted u    =>
      match sys.find? u with
      | some pu =>
          if pu.promiser == me && pu.isUse then
            (u, true) :: (sys.promises.filter (fun po => mayBind sys po pu)).map (fun po => (po.id, true))
          else []
      | none => []
  | .accepted o    =>
      match sys.find? o with
      | some po =>
          if po.promiser == me && po.isOffer then
            (o, true) :: (sys.promises.filter (fun pu => mayBind sys po pu && inScope pu me)).map (fun pu => (pu.id, true))
          else []
      | none => []

def obsDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) (obs : List (Obs P)) : List (P × Bool) :=
  obs.flatMap (obsEntryDeps sys me)

/-- Complete dependency list `(depId, isStrict)` of a promise (`condDeps` ++ `obsDeps`). -/
def promiseDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U M) : List (P × Bool) :=
  condDeps sys pr.promiser false pr.cond ++ obsDeps sys pr.promiser pr.obs

/-- Valid stratification: positive `Cond` deps satisfy `rank dep ≤ rank p`;
    negated `Cond` deps and all `Obs` value-derivation deps satisfy `rank dep < rank p`. -/
def ValidStratification {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (rank : P → Nat) : Prop :=
  ∀ pr ∈ sys.promises, ∀ dep strict, (dep, strict) ∈ promiseDeps sys pr →
    if strict then rank dep < rank pr.id else rank dep ≤ rank pr.id

/-- Executable validator for `ValidStratification` (verified sound by `checkValidStratification_sound`). -/
def checkValidStratification {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (rank : P → Nat) : Bool :=
  sys.promises.all fun pr =>
    (promiseDeps sys pr).all fun (dep, strict) =>
      if strict then decide (rank dep < rank pr.id) else decide (rank dep ≤ rank pr.id)

def stratumStep {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : State P O U) (S : State P O U) (pid : P) : Option (Body O U) :=
  if rank pid < s then base pid
  else if rank pid == s then quenchStep sys α S pid
  else none

def stratumIter {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : State P O U) : Nat → State P O U
  | 0     => fun pid => if rank pid < s then base pid else none
  | n + 1 => stratumStep sys α rank s base (stratumIter sys α rank s base n)

/-- Stratified fixed-point evaluator across strata `0 .. maxS`. -/
def evalStratified {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (stepsPerStratum : Nat) : Nat → State P O U
  | 0     => stratumIter sys α rank 0 (fun _ => none) stepsPerStratum
  | s + 1 =>
      let prev := evalStratified sys α rank stepsPerStratum s
      stratumIter sys α rank (s + 1) prev stepsPerStratum

/-- Active bindings `(offerId, useId)` under resolved state `S` and local assessment `α`. -/
def activeBindings {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (S : State P O U) : List (P × P) :=
  sys.promises.flatMap fun po =>
    if po.isOffer then
      sys.promises.filterMap fun pu =>
        if pu.isUse && (runtimeOverlap sys S po pu).isSome &&
           α pu.promiser po.id && α pu.promiser pu.id then
          some (po.id, pu.id)
        else none
    else []

/-- Maximal statically bindable offer-use pairs `B_max(S)` across all possible assessments `α`. -/
def staticMaxBindings {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) : List (P × P) :=
  sys.promises.flatMap fun po =>
    if po.isOffer then
      sys.promises.filterMap fun pu =>
        if pu.isUse && mayBind sys po pu then
          some (po.id, pu.id)
        else none
    else []

end Baugr
