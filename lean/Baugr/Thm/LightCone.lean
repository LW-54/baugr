/-
  Baugr.Thm.LightCone — Canonical Functor Φ Well-Formedness (T5d) &
  Crown-Jewel SST Reverse Causal Light Cone Perturbation Containment Theorem (T6)
-/
import Baugr.Projection
import Baugr.Thm.Quenching

namespace Baugr

/-- T5d: Canonical functor Φ : PromiseSystem → γ(3,4) always yields a well-formed SST graph. -/
theorem projectSst_wellFormed {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) :
    (projectSst sys).WellFormed := by
  intro e he
  simp only [projectSst, List.mem_append] at he
  rcases he with ((hc | hp) | hexp) | hcas
  · simp only [List.mem_filterMap] at hc
    obtain ⟨a, _, hsome⟩ := hc
    cases hpar : sys.hierarchy.parent a with
    | none => simp [hpar] at hsome
    | some s =>
      simp only [hpar, Option.some.injEq] at hsome
      subst hsome; rfl
  · simp only [List.mem_map] at hp
    obtain ⟨pr, _, rfl⟩ := hp; rfl
  · simp only [List.mem_flatMap] at hexp
    obtain ⟨pr, _, hmem⟩ := hexp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rfl
  · simp only [List.mem_flatMap, List.mem_filterMap] at hcas
    obtain ⟨pr, _, ⟨dep, neg⟩, _, hsome⟩ := hcas
    cases hfd : sys.find? dep with
    | none => simp [hfd] at hsome
    | some _ =>
      simp only [hfd, Option.some.injEq] at hsome
      subst hsome; rfl

/-- Every syntactic dependency of an existing promise projects to a `+LeadsTo` SST edge. -/
theorem dep_gives_leadsTo {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U)
    (hmem : pr ∈ sys.promises) (dep : P) (neg : Bool)
    (hdep : (dep, neg) ∈ condDeps sys false pr.cond)
    (hexists : ∃ x, sys.find? dep = some x) :
    SstEdge.mk (.promise dep) .leadsTo (.promise pr.id) ∈ (projectSst sys).edges := by
  obtain ⟨x, hx⟩ := hexists
  simp only [projectSst, List.mem_append]
  right
  simp only [List.mem_flatMap, List.mem_filterMap]
  exact ⟨pr, hmem, (dep, neg), hdep, by simp [hx]⟩

/-- Every normalized `+LeadsTo` edge in `projectSst sys` originates from a syntactic condition dependency. -/
theorem leadsTo_gives_dep {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) {x y : SstNode A P}
    (hedge : (projectSst sys).hasEdge x .leadsTo y) :
    ∃ (pr : Promise A P O U) (dep : P) (neg : Bool),
      pr ∈ sys.promises ∧ x = .promise dep ∧ y = .promise pr.id ∧
      (dep, neg) ∈ condDeps sys false pr.cond := by
  rcases hedge with hf | hb
  · simp only [projectSst, List.mem_append] at hf
    rcases hf with ((hc | hp) | hexp) | hcas
    · simp only [List.mem_filterMap] at hc
      obtain ⟨a, _, hsome⟩ := hc
      cases hpar : sys.hierarchy.parent a <;> simp [hpar] at hsome
    · simp only [List.mem_map] at hp
      obtain ⟨pr, _, h⟩ := hp; cases h
    · simp only [List.mem_flatMap] at hexp
      obtain ⟨pr, _, hmem⟩ := hexp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h <;> cases h
    · simp only [List.mem_flatMap, List.mem_filterMap] at hcas
      obtain ⟨pr, hmem, ⟨dep, neg⟩, hdep, hsome⟩ := hcas
      cases hfd : sys.find? dep with
      | none => simp [hfd] at hsome
      | some _ =>
        simp only [hfd, Option.some.injEq] at hsome
        cases hsome
        exact ⟨pr, dep, neg, hmem, rfl, rfl, hdep⟩
  · -- `projectSst` never emits negative `.follows` edges.
    simp only [LinkKind.inv, projectSst, List.mem_append] at hb
    rcases hb with ((hc | hp) | hexp) | hcas
    · simp only [List.mem_filterMap] at hc
      obtain ⟨a, _, hsome⟩ := hc
      cases hpar : sys.hierarchy.parent a <;> simp [hpar] at hsome
    · simp only [List.mem_map] at hp
      obtain ⟨pr, _, h⟩ := hp; cases h
    · simp only [List.mem_flatMap] at hexp
      obtain ⟨pr, _, hmem⟩ := hexp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h <;> cases h
    · simp only [List.mem_flatMap, List.mem_filterMap] at hcas
      obtain ⟨pr, _, ⟨dep, neg⟩, _, hsome⟩ := hcas
      cases hfd : sys.find? dep <;> simp [hfd] at hsome

/-- T6 (CROWN-JEWEL UNIFICATION THEOREM):
    Perturbation Containment in the Semantic Spacetime Reverse Light Cone!
    Changing observer-local assessments outside the SST reverse causal cone `J⁻_Φ(target)`
    can NEVER change the quenched truth value of `target` (even with stratified `Not` fallbacks!). -/
theorem perturbation_in_reverse_cone {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (rank : P → Nat) (steps : Nat) (maxS : Nat) (target : P)
    (hcone : ∀ d, CausalReach (projectSst sys) (.promise d) (.promise target) →
      ∀ obs, α₁ obs d = α₂ obs d) :
    evalStratified sys α₁ rank steps maxS target =
    evalStratified sys α₂ rank steps maxS target := by
  suffices ∀ s p, CausalReach (projectSst sys) (.promise p) (.promise target) →
      evalStratified sys α₁ rank steps s p = evalStratified sys α₂ rank steps s p by
    exact this maxS target (.refl _)
  have hstratum : ∀ s b₁ b₂,
      (∀ p, CausalReach (projectSst sys) (.promise p) (.promise target) → b₁ p = b₂ p) →
      ∀ n p, CausalReach (projectSst sys) (.promise p) (.promise target) →
        stratumIter sys α₁ rank s b₁ n p = stratumIter sys α₂ rank s b₂ n p := by
    intro s b₁ b₂ hb n
    induction n with
    | zero =>
      intro p hp
      simp only [stratumIter]; split; exact hb p hp; rfl
    | succ k ih =>
      intro p hp
      simp only [stratumIter, stratumStep]
      split
      · exact hb p hp
      · split
        · simp only [quenchStep]
          cases hfp : sys.find? p with
          | none => rfl
          | some pr =>
            have hmem : pr ∈ sys.promises := List.mem_of_find?_eq_some hfp
            have hid : pr.id = p := find?_id_eq hfp
            apply evalCond_local
            intro d neg hdep hex
            have hedge : SstEdge.mk (.promise d) .leadsTo (.promise p) ∈ (projectSst sys).edges := by
              rw [← hid]; exact dep_gives_leadsTo sys pr hmem d neg hdep hex
            have hd_reach : CausalReach (projectSst sys) (.promise d) (.promise target) :=
              .step (Or.inl hedge) hp
            exact ⟨ih d hd_reach, hcone d hd_reach pr.promiser⟩
        · rfl
  intro s
  induction s with
  | zero =>
    intro p hp
    exact hstratum 0 (fun _ => false) (fun _ => false) (fun _ _ => rfl) steps p hp
  | succ k ih =>
    intro p hp
    exact hstratum (k + 1) _ _ ih steps p hp

end Baugr
