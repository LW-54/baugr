/-
  Baugr.Oracle.Main — Dev/CI Executable DRT Oracle (Cedar VGD)
  Reads compact CASE blocks from stdin, evaluates them using the EXACT Lean 4
  specification (`evalStratified`, `activeBindings`, `projectSst`) with a bitmask
  mutual-information BodyAlgebra (`b₁ ∩ b₂ = (o &&& u) ≠ 0`), and emits canonical
  sorted results to stdout for bit-for-bit Rust ↔ Lean differential testing.
-/
import Baugr

namespace Baugr.Oracle

open Baugr

/-- Bitmask mutual-information BodyAlgebra (`b₁ ∩ b₂ = o &&& u` when non-zero). -/
def bitmaskAlgebra : BodyAlgebra Nat Nat Nat :=
  { overlap := fun o u =>
      let m := o &&& u
      if m == 0 then none else some m }

private def parseNat (s : String) : Nat :=
  s.toNat?.getD 0

private def parseAgentSet (spec : String) : AgentSet Nat :=
  if spec == "*" then
    fun _ => true
  else if spec == "-" then
    fun _ => false
  else
    let ids := (spec.splitOn ",").map parseNat
    fun a => ids.contains a

/-- Total fuel-bounded prefix-notation Cond parser returning `(parsedCond, remainingTokens)`. -/
private def parseCondTokens : Nat → List String → Cond Nat × List String
  | 0, rest => (Cond.always, rest)
  | fuel + 1, toks =>
      match toks with
      | "T" :: rest => (Cond.always, rest)
      | "S" :: q :: rest => (Cond.selfPromise (parseNat q), rest)
      | "A" :: u :: k :: rest => (Cond.assisted (parseNat u) (parseNat k), rest)
      | "C" :: o :: k :: rest => (Cond.accepted (parseNat o) (parseNat k), rest)
      | "I" :: q :: rest => (Cond.interior (parseNat q), rest)
      | "N" :: rest =>
          let (inner, rem) := parseCondTokens fuel rest
          (Cond.not inner, rem)
      | "K" :: k :: n :: rest =>
          let rec go : Nat → List String → List (Cond Nat) × List String
            | 0,     ts => ([], ts)
            | m + 1, ts =>
                let (c, r1) := parseCondTokens fuel ts
                let (cs, r2) := go m r1
                (c :: cs, r2)
          let (cs, rem) := go (parseNat n) rest
          (Cond.atLeast (parseNat k) cs, rem)
      | rest => (Cond.always, rest)

private structure RawCase where
  numAgents  : Nat := 0
  parents    : List (Nat × Nat) := []
  opaques    : List Nat := []
  promises   : List (Promise Nat Nat Nat Nat) := []
  broken     : List (Nat × Nat) := []
  strata     : List (Nat × Nat) := []
  maxStratum : Nat := 0
  steps      : Nat := 1

private def insertSortedStr (x : String) : List String → List String
  | []      => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insertSortedStr x ys

private def dedupSortStr (xs : List String) : List String :=
  xs.foldl (fun acc x => insertSortedStr x acc) []

private def insertSortedNat (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insertSortedNat x ys

private def dedupSortNat (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertSortedNat x acc) []

private def fmtNode : SstNode Nat Nat → String
  | .agent   a => s!"t:{a}"
  | .promise p => s!"e:{p}"
  | .intent  p => s!"c:{p}"

private def fmtLink : LinkKind → String
  | .near        => "N"
  | .leadsTo     => "+L"
  | .follows     => "-L"
  | .contains    => "+C"
  | .containedBy => "-C"
  | .expresses   => "+E"
  | .expressedBy => "-E"

private def evalCase (rc : RawCase) : String :=
  let agents := List.range rc.numAgents
  let hierarchy : Hierarchy Nat :=
    { parent   := fun a => (rc.parents.find? (fun p => p.1 == a)).map Prod.snd
      isOpaque := fun a => rc.opaques.contains a }
  let sys : PromiseSystem Nat Nat Nat Nat Nat :=
    { agents    := agents
      promises  := rc.promises.reverse
      hierarchy := hierarchy
      algebra   := bitmaskAlgebra }
  let α : Assessment Nat Nat := fun obs pid => !(rc.broken.contains (obs, pid))
  let rank : Nat → Nat := fun pid => ((rc.strata.find? (fun p => p.1 == pid)).map Prod.snd).getD 0
  let qFun := evalStratified sys α rank rc.steps rc.maxStratum
  let quenched := dedupSortNat ((sys.promises.filter (fun pr => qFun pr.id)).map (fun pr => pr.id))
  let bindingsRaw := activeBindings sys α qFun
  let bindingsFmt := dedupSortStr (bindingsRaw.filterMap fun (oid, uid) =>
    match sys.find? oid, sys.find? uid with
    | some po, some pu =>
        match po.body, pu.body with
        | .offer ob, .use ub =>
            match bitmaskAlgebra.overlap ob ub with
            | some ov => some s!"{oid}:{uid}:{ov}"
            | none    => none
        | _, _ => none
    | _, _ => none)
  let sst := projectSst sys
  let sstFmt := dedupSortStr (sst.edges.map fun e =>
    s!"{fmtNode e.src}->{fmtLink e.kind}->{fmtNode e.dst}")
  let qLine := String.intercalate " " (quenched.map toString)
  let bLine := String.intercalate " " bindingsFmt
  let sLine := String.intercalate " " sstFmt
  s!"QUENCHED {qLine}\nBINDINGS {bLine}\nSST {sLine}\nEND_OUT\n"

private def processLines (lines : List String) : String :=
  let rec go (cur : RawCase) (out : String) : List String → String
    | [] => out
    | raw :: rest =>
        let line := raw.trimAscii.toString
        if line.isEmpty then
          go cur out rest
        else if line == "END_CASE" then
          go {} (out ++ evalCase cur) rest
        else
          let toks := (line.splitOn " ").filter (fun (s : String) => !s.isEmpty)
          match toks with
          | ["AGENTS", n] =>
              go { cur with numAgents := parseNat n } out rest
          | ["PARENT", c, p] =>
              go { cur with parents := (parseNat c, parseNat p) :: cur.parents } out rest
          | ["OPAQUE", a] =>
              go { cur with opaques := parseNat a :: cur.opaques } out rest
          | ["BROKEN", obs, pid] =>
              go { cur with broken := (parseNat obs, parseNat pid) :: cur.broken } out rest
          | ["STRATUM", pid, r] =>
              go { cur with strata := (parseNat pid, parseNat r) :: cur.strata } out rest
          | ["MAX_STRATUM", m] =>
              go { cur with maxStratum := parseNat m } out rest
          | ["STEPS", s] =>
              go { cur with steps := parseNat s } out rest
          | "PROMISE" :: idS :: promS :: polS :: tgtS :: scS :: bodyS :: condToks =>
              let bVal := parseNat bodyS
              let body := if polS == "O" then Body.offer bVal else Body.use bVal
              let (cond, _) := parseCondTokens (condToks.length + 1) condToks
              let pr : Promise Nat Nat Nat Nat :=
                { id       := parseNat idS
                  promiser := parseNat promS
                  target   := parseAgentSet tgtS
                  scope    := parseAgentSet scS
                  body     := body
                  cond     := cond }
              go { cur with promises := pr :: cur.promises } out rest
          | _ => go cur out rest
  go {} "" lines

end Baugr.Oracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let lines := input.splitOn "\n"
  IO.print (Baugr.Oracle.processLines lines)
