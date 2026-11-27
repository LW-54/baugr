/-
  Baugr.Projection — Canonical Functor Φ : PromiseSystem → Semantic Spacetime γ(3,4)
  Maps Agents ↦ Thing (t), Promises ↦ Event (e), Intents ↦ Concept (c).
-/
import Baugr.Spacetime
import Baugr.Promise

namespace Baugr

/-- Typed nodes in the canonical γ(3,4) Semantic Spacetime projection of a PromiseSystem. -/
inductive SstNode (A P : Type) where
  | agent   (a : A)
  | promise (p : P)
  | intent  (p : P)
  deriving DecidableEq, Repr

def sstNodeKind {A P : Type} : SstNode A P → NodeKind
  | .agent   _ => .thing
  | .promise _ => .event
  | .intent  _ => .concept

/-- Canonical functor Φ : PromiseSystem → SstGraph (SstNode A P).
    Every emitted edge obeys strict γ(3,4) typing by construction (`projectSst_wellFormed`),
    capturing both boolean quenching (`condDeps`) and value-derivation (`obsDeps`) causality. -/
def projectSst {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) : SstGraph (SstNode A P) :=
  let containmentEdges : List (SstEdge (SstNode A P)) :=
    sys.agents.filterMap fun a =>
      match sys.hierarchy.parent a with
      | some s => some { src := .agent s, kind := .contains, dst := .agent a } -- t +C t
      | none   => none
  let participationEdges : List (SstEdge (SstNode A P)) :=
    sys.promises.map fun pr =>
      { src := .promise pr.id, kind := .contains, dst := .agent pr.promiser } -- e +C t
  let expressionEdges : List (SstEdge (SstNode A P)) :=
    sys.promises.flatMap fun pr =>
      [ { src := .agent pr.promiser, kind := .expresses, dst := .intent pr.id }, -- t +E c
        { src := .promise pr.id,     kind := .expresses, dst := .intent pr.id }  -- e +E c
      ]
  let causalEdges : List (SstEdge (SstNode A P)) :=
    sys.promises.flatMap fun pr =>
      (promiseDeps sys pr).filterMap fun (dep, _) =>
        match sys.find? dep with
        | some _ => some { src := .promise dep, kind := .leadsTo, dst := .promise pr.id } -- e +L e
        | none   => none
  { kindOf := sstNodeKind
    edges  := containmentEdges ++ participationEdges ++ expressionEdges ++ causalEdges }

end Baugr
