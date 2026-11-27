/-
  Baugr.Thm.Superagent — Opaque Superagent Non-Piercing Encapsulation & Interior Isolation (T7)
-/
import Baugr.Thm.LightCone

namespace Baugr

/-- `noOpaqueWall` is symmetric in the two endpoints. -/
theorem noOpaqueWall_symm {A : Type} [DecidableEq A]
    (h : Hierarchy A) (agents : List A) (a b : A) :
    noOpaqueWall h agents a b = noOpaqueWall h agents b a := by
  simp only [noOpaqueWall]
  congr 1
  funext s
  cases h.isOpaque s with
  | false => rfl
  | true => simp [Bool.and_comm]

private theorem noOpaqueWall_false_of_crossing {A : Type} [DecidableEq A]
    (h : Hierarchy A) (agents : List A) (s a b : A)
    (hs_mem : s ∈ agents) (hs_op : h.isOpaque s = true)
    (hin  : isStrictAncAux h agents.length s a = true)
    (hout : b ≠ s ∧ isStrictAncAux h agents.length s b = false) :
    noOpaqueWall h agents a b = false := by
  simp only [noOpaqueWall, List.all_eq_false]
  refine ⟨s, hs_mem, ?_⟩
  simp [hs_op, hin, hout.1, hout.2]

/-- T7a (outward): An offer (fixed or derived) inside an opaque superagent cannot bind externally. -/
theorem opaque_non_piercing {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (s : A)
    (hs_mem : s ∈ sys.agents) (hs_op : sys.hierarchy.isOpaque s = true)
    (po pu : Promise A P O U M)
    (hin  : isStrictAncAux sys.hierarchy sys.agents.length s po.promiser = true)
    (hout : pu.promiser ≠ s ∧ isStrictAncAux sys.hierarchy sys.agents.length s pu.promiser = false) :
    mayBind sys po pu = false := by
  have hwall := noOpaqueWall_false_of_crossing sys.hierarchy sys.agents s
    po.promiser pu.promiser hs_mem hs_op hin hout
  simp [mayBind, structBindable, hwall]

/-- T7a (inward): An external offer (fixed or derived) cannot pierce into a strict sub-agent's Use. -/
theorem opaque_non_piercing_inward {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (s : A)
    (hs_mem : s ∈ sys.agents) (hs_op : sys.hierarchy.isOpaque s = true)
    (po pu : Promise A P O U M)
    (hout : po.promiser ≠ s ∧ isStrictAncAux sys.hierarchy sys.agents.length s po.promiser = false)
    (hin  : isStrictAncAux sys.hierarchy sys.agents.length s pu.promiser = true) :
    mayBind sys po pu = false := by
  have hwall : noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser = false := by
    rw [noOpaqueWall_symm]
    exact noOpaqueWall_false_of_crossing sys.hierarchy sys.agents s
      pu.promiser po.promiser hs_mem hs_op hin hout
  simp [mayBind, structBindable, hwall]

/-- T7b: Interior perturbations of an opaque superagent cannot affect external promises'
    resolved bodies when their reverse causal cone stays outside the superagent's interior. -/
theorem opaque_interior_perturbation_contained {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (rank : P → Nat) (steps maxS : Nat) (s : A) (ext : P)
    (hclosed : ∀ d, CausalReach (projectSst sys) (.promise d) (.promise ext) →
      ∀ pr, sys.find? d = some pr →
        isStrictAncAux sys.hierarchy sys.agents.length s pr.promiser = false)
    (hagree_ext : ∀ d, (∀ pr, sys.find? d = some pr →
        isStrictAncAux sys.hierarchy sys.agents.length s pr.promiser = false) →
      ∀ obs, α₁ obs d = α₂ obs d) :
    evalStratified sys α₁ rank steps maxS ext =
    evalStratified sys α₂ rank steps maxS ext := by
  apply perturbation_in_reverse_cone
  intro d hd obs
  exact hagree_ext d (hclosed d hd) obs

end Baugr
