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

/-- Polarity-preserving promise body specification: either a static body or a
    value-derived body computed strictly from declared local `Obs` observations. -/
inductive BodySpec (A P O U M : Type) where
  | fixedOffer   (o : O)
  | fixedUse     (u : U)
  | derivedOffer (obs : List (Obs P)) (produce : LocalObs A P O U M → Option O)
  | derivedUse   (obs : List (Obs P)) (produce : LocalObs A P O U M → Option U)

def BodySpec.isOffer {A P O U M : Type} : BodySpec A P O U M → Bool
  | .fixedOffer _ | .derivedOffer _ _ => true
  | .fixedUse _   | .derivedUse _ _   => false

def BodySpec.isUse {A P O U M : Type} : BodySpec A P O U M → Bool
  | .fixedOffer _ | .derivedOffer _ _ => false
  | .fixedUse _   | .derivedUse _ _   => true

def BodySpec.obs {A P O U M : Type} : BodySpec A P O U M → List (Obs P)
  | .fixedOffer _       => []
  | .fixedUse _         => []
  | .derivedOffer os _  => os
  | .derivedUse os _    => os

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
    static or value-derived body `spec`, and quenching condition `cond`. -/
structure Promise (A P O U M : Type) where
  id       : P
  promiser : A
  target   : AgentSet A
  scope    : AgentSet A
  spec     : BodySpec A P O U M
  cond     : Cond P

def Promise.isOffer {A P O U M : Type} (pr : Promise A P O U M) : Bool :=
  pr.spec.isOffer

def Promise.isUse {A P O U M : Type} (pr : Promise A P O U M) : Bool :=
  pr.spec.isUse

/-- Effective scope always includes the promiser (arXiv:1401.3381v1 L663). -/
def inScope {A P O U M : Type} [DecidableEq A] (pr : Promise A P O U M) (obs : A) : Bool :=
  (obs == pr.promiser) || pr.scope obs

/-- Complete Promise System. -/
structure PromiseSystem (A P O U M : Type) where
  agents    : List A
  promises  : List (Promise A P O U M)
  hierarchy : Hierarchy A
  algebra   : BodyAlgebra O U M

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
    checks exact `overlap` when both bodies are fixed, and `structBindable` when either is derived. -/
def mayBind {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po pu : Promise A P O U M) : Bool :=
  if !structBindable sys po pu then false
  else match po.spec, pu.spec with
    | .fixedOffer ob, .fixedUse ub => (sys.algebra.overlap ob ub).isSome
    | _, _                         => true

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

mutual
/-- Evaluate condition `c` for promiser `me` under resolved state `S` and local assessment `α`.
    Consistently enforces local self-assessment `α me own` across `SelfPromise`, `Assisted`, and `Accepted`. -/
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
          isStrictAncAux sys.hierarchy sys.agents.length me pq.promiser && (S q).isSome && α me q
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

/-- Constructs the autonomy-grounded local observation snapshot for a derived promise. -/
def buildLocalObs {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (me : A) (obs : List (Obs P)) : LocalObs A P O U M :=
  let selfBodies := obs.filterMap fun o =>
    match o with
    | .selfPromise q =>
        match sys.find? q, S q with
        | some pq, some b => if pq.promiser == me && α me q then some (q, b) else none
        | _, _ => none
    | _ => none
  let assistedOffers := obs.flatMap fun o =>
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
  let acceptedUses := obs.flatMap fun o =>
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
  let interiorBodies := obs.filterMap fun o =>
    match o with
    | .interior q =>
        match sys.find? q, S q with
        | some pq, some b =>
            if isStrictAncAux sys.hierarchy sys.agents.length me pq.promiser && α me q then
              some (q, pq.promiser, b)
            else none
        | _, _ => none
    | _ => none
  { selfBodies, assistedOffers, acceptedUses, interiorBodies }

/-- Evaluates a promise's body specification (`fixed` or `derived`) under state `S`. -/
def evalRule {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S : State P O U) (pr : Promise A P O U M) : Option (Body O U) :=
  match pr.spec with
  | .fixedOffer o => some (.offer o)
  | .fixedUse u   => some (.use u)
  | .derivedOffer obs produce =>
      (produce (buildLocalObs sys α S pr.promiser obs)).map .offer
  | .derivedUse obs produce =>
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
  ∀ pr ∈ sys.promises, pr.cond.isPositive ∧ pr.spec.obs = []

/-- Iterate quenching from empty state `⊥` (`fun _ => none`) for `n` steps (Knaster-Tarski). -/
def quenchIter {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) : Nat → State P O U
  | 0     => fun _ => none
  | n + 1 => quenchStep sys α (quenchIter sys α n)

mutual
/-- Syntactic condition dependencies `(depId, isStrict)` (`true` for negated edges). -/
def condDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (neg : Bool) : Cond P → List (P × Bool)
  | .selfPromise q => [(q, neg)]
  | .assisted u _  =>
      match sys.find? u with
      | some pu =>
          (u, neg) :: (sys.promises.filter (fun po => mayBind sys po pu)).map (fun po => (po.id, neg))
      | none => [(u, neg)]
  | .accepted o _  =>
      match sys.find? o with
      | some po =>
          (o, neg) :: (sys.promises.filter (fun pu => mayBind sys po pu && inScope pu po.promiser)).map (fun pu => (pu.id, neg))
      | none => [(o, neg)]
  | .interior q    => [(q, neg)]
  | .atLeast _ cs  => listCondDeps sys neg cs
  | .not c         => condDeps sys (!neg) c

def listCondDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (neg : Bool) : List (Cond P) → List (P × Bool)
  | []      => []
  | c :: rs => condDeps sys neg c ++ listCondDeps sys neg rs
end

/-- Value-observation dependencies (every `Obs` entry is a strict stratum barrier `isStrict = true`). -/
def obsEntryDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) : Obs P → List (P × Bool)
  | .selfPromise q => [(q, true)]
  | .interior q    => [(q, true)]
  | .assisted u    =>
      match sys.find? u with
      | some pu =>
          (u, true) :: (sys.promises.filter (fun po => mayBind sys po pu)).map (fun po => (po.id, true))
      | none => [(u, true)]
  | .accepted o    =>
      match sys.find? o with
      | some po =>
          (o, true) :: (sys.promises.filter (fun pu => mayBind sys po pu && inScope pu po.promiser)).map (fun pu => (pu.id, true))
      | none => [(o, true)]

def obsDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (obs : List (Obs P)) : List (P × Bool) :=
  obs.flatMap (obsEntryDeps sys)

/-- Complete dependency list `(depId, isStrict)` of a promise (`condDeps` ++ `obsDeps`). -/
def promiseDeps {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U M) : List (P × Bool) :=
  condDeps sys false pr.cond ++ obsDeps sys pr.spec.obs

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
