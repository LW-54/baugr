/-
  Baugr.Thm.Superagent — Opaque Superagent Non-Piercing Encapsulation,
  Interior Isolation, and the Topological Event-Horizon Vertex-Cut Theorem (T7)
-/
import Baugr.Thm.LightCone

namespace Baugr

/-- `noOpaqueWall` is reflexive (`a` never crosses an opaque wall to reach itself). -/
theorem noOpaqueWall_refl {A : Type} [DecidableEq A]
    (h : Hierarchy A) (agents : List A) (a : A) :
    noOpaqueWall h agents a a = true := by
  simp only [noOpaqueWall, List.all_eq_true]
  intro s _
  cases h.isOpaque s with
  | false => rfl
  | true =>
    cases isStrictAncAux h agents.length s a <;> simp

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

private theorem noOpaqueWall_imp_in_of_strict {A : Type} [DecidableEq A]
    (h : Hierarchy A) (agents : List A) (s a b : A)
    (hs_mem : s ∈ agents) (hs_op : h.isOpaque s = true)
    (hin : isStrictAncAux h agents.length s a = true)
    (hwall : noOpaqueWall h agents a b = true) :
    b = s ∨ isStrictAncAux h agents.length s b = true := by
  simp only [noOpaqueWall, List.all_eq_true] at hwall
  have hs := hwall s hs_mem
  simp only [hs_op, ↓reduceIte, hin, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
  have h1 := hs.1
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
  exact h1

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

-- ----------------------------------------------------------------------------
-- T7c & T7d: Topological Event-Horizon Vertex-Cut Theorems (Strong Law II)
-- ----------------------------------------------------------------------------

private theorem mayBind_noOpaqueWall {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po pu : Promise A P O U M)
    (hmb : mayBind sys po pu = true) :
    noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser = true := by
  cases hsb : structBindable sys po pu with
  | false => simp [mayBind, hsb] at hmb
  | true =>
    simp only [structBindable, Bool.and_eq_true] at hsb
    exact hsb.2

mutual
private theorem condDeps_noOpaqueWall {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys) (me : A) :
    ∀ (neg : Bool) (c : Cond P) (d : P) (strict : Bool) (pd : Promise A P O U M),
      (d, strict) ∈ condDeps sys me neg c →
      sys.find? d = some pd →
      noOpaqueWall sys.hierarchy sys.agents pd.promiser me = true
  | neg, .selfPromise q, d, strict, pd, hmem, hfd => by
    simp only [condDeps] at hmem
    cases hfq : sys.find? q with
    | none => simp [hfq] at hmem
    | some pq =>
      simp only [hfq] at hmem
      split at hmem
      · next hpr =>
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, _⟩ := hmem
        rw [hfq] at hfd; cases hfd
        have hme : pd.promiser = me := eq_of_beq hpr
        rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
      · simp at hmem
  | neg, .interior q, d, strict, pd, hmem, hfd => by
    simp only [condDeps] at hmem
    cases hfq : sys.find? q with
    | none => simp [hfq] at hmem
    | some pq =>
      simp only [hfq] at hmem
      split at hmem
      · next hvi =>
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, _⟩ := hmem
        rw [hfq] at hfd; cases hfd
        simp only [visibleInterior, Bool.and_eq_true] at hvi
        rw [noOpaqueWall_symm]; exact hvi.2
      · simp at hmem
  | neg, .assisted u _, d, strict, pd, hmem, hfd => by
    simp only [condDeps] at hmem
    cases hfu : sys.find? u with
    | none => simp [hfu] at hmem
    | some pu =>
      simp only [hfu] at hmem
      split at hmem
      · next hown =>
        simp only [Bool.and_eq_true] at hown
        have hme : pu.promiser = me := eq_of_beq hown.1
        simp only [List.mem_cons, List.mem_map, List.mem_filter, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩ | ⟨po, ⟨hpo_mem, hmb⟩, rfl, _⟩
        · rw [hfu] at hfd; cases hfd
          rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
        · have hpo_eq : po = pd := huniq po hpo_mem pd (List.mem_of_find?_eq_some hfd) (find?_id_eq hfd).symm
          rw [← hpo_eq, ← hme]
          exact mayBind_noOpaqueWall sys po pu hmb
      · simp at hmem
  | neg, .accepted o _, d, strict, pd, hmem, hfd => by
    simp only [condDeps] at hmem
    cases hfo : sys.find? o with
    | none => simp [hfo] at hmem
    | some po =>
      simp only [hfo] at hmem
      split at hmem
      · next hown =>
        simp only [Bool.and_eq_true] at hown
        have hme : po.promiser = me := eq_of_beq hown.1
        simp only [List.mem_cons, List.mem_map, List.mem_filter, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩ | ⟨pu, ⟨hpu_mem, hmb_sc⟩, rfl, _⟩
        · rw [hfo] at hfd; cases hfd
          rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
        · simp only [Bool.and_eq_true] at hmb_sc
          have hpu_eq : pu = pd := huniq pu hpu_mem pd (List.mem_of_find?_eq_some hfd) (find?_id_eq hfd).symm
          rw [← hpu_eq, ← hme, noOpaqueWall_symm]
          exact mayBind_noOpaqueWall sys po pu hmb_sc.1
      · simp at hmem
  | neg, .atLeast _ cs, d, strict, pd, hmem, hfd =>
    listCondDeps_noOpaqueWall sys huniq me neg cs d strict pd hmem hfd
  | neg, .not c, d, strict, pd, hmem, hfd =>
    condDeps_noOpaqueWall sys huniq me (!neg) c d strict pd hmem hfd

private theorem listCondDeps_noOpaqueWall {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys) (me : A) :
    ∀ (neg : Bool) (cs : List (Cond P)) (d : P) (strict : Bool) (pd : Promise A P O U M),
      (d, strict) ∈ listCondDeps sys me neg cs →
      sys.find? d = some pd →
      noOpaqueWall sys.hierarchy sys.agents pd.promiser me = true
  | _, [], _, _, _, hmem, _ => by simp [listCondDeps] at hmem
  | neg, c :: rs, d, strict, pd, hmem, hfd => by
    simp only [listCondDeps, List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact condDeps_noOpaqueWall sys huniq me neg c d strict pd h1 hfd
    · exact listCondDeps_noOpaqueWall sys huniq me neg rs d strict pd h2 hfd
end

private theorem obsDeps_noOpaqueWall {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys) (me : A)
    (obs : List (Obs P)) (d : P) (strict : Bool) (pd : Promise A P O U M)
    (hmem : (d, strict) ∈ obsDeps sys me obs) (hfd : sys.find? d = some pd) :
    noOpaqueWall sys.hierarchy sys.agents pd.promiser me = true := by
  simp only [obsDeps, List.mem_flatMap] at hmem
  obtain ⟨o, _, ho⟩ := hmem
  cases o with
  | selfPromise q =>
    simp only [obsEntryDeps] at ho
    cases hfq : sys.find? q with
    | none => simp [hfq] at ho
    | some pq =>
      simp only [hfq] at ho
      split at ho
      · next hpr =>
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, _⟩ := ho
        rw [hfq] at hfd; cases hfd
        have hme : pd.promiser = me := eq_of_beq hpr
        rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
      · simp at ho
  | interior q =>
    simp only [obsEntryDeps] at ho
    cases hfq : sys.find? q with
    | none => simp [hfq] at ho
    | some pq =>
      simp only [hfq] at ho
      split at ho
      · next hvi =>
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, _⟩ := ho
        rw [hfq] at hfd; cases hfd
        simp only [visibleInterior, Bool.and_eq_true] at hvi
        rw [noOpaqueWall_symm]; exact hvi.2
      · simp at ho
  | assisted u =>
    simp only [obsEntryDeps] at ho
    cases hfu : sys.find? u with
    | none => simp [hfu] at ho
    | some pu =>
      simp only [hfu] at ho
      split at ho
      · next hown =>
        simp only [Bool.and_eq_true] at hown
        have hme : pu.promiser = me := eq_of_beq hown.1
        simp only [List.mem_cons, List.mem_map, List.mem_filter, Prod.mk.injEq] at ho
        rcases ho with ⟨rfl, _⟩ | ⟨po, ⟨hpo_mem, hmb⟩, rfl, _⟩
        · rw [hfu] at hfd; cases hfd
          rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
        · have hpo_eq : po = pd := huniq po hpo_mem pd (List.mem_of_find?_eq_some hfd) (find?_id_eq hfd).symm
          rw [← hpo_eq, ← hme]
          exact mayBind_noOpaqueWall sys po pu hmb
      · simp at ho
  | accepted oid =>
    simp only [obsEntryDeps] at ho
    cases hfo : sys.find? oid with
    | none => simp [hfo] at ho
    | some po =>
      simp only [hfo] at ho
      split at ho
      · next hown =>
        simp only [Bool.and_eq_true] at hown
        have hme : po.promiser = me := eq_of_beq hown.1
        simp only [List.mem_cons, List.mem_map, List.mem_filter, Prod.mk.injEq] at ho
        rcases ho with ⟨rfl, _⟩ | ⟨pu, ⟨hpu_mem, hmb_sc⟩, rfl, _⟩
        · rw [hfo] at hfd; cases hfd
          rw [hme]; exact noOpaqueWall_refl sys.hierarchy sys.agents me
        · simp only [Bool.and_eq_true] at hmb_sc
          have hpu_eq : pu = pd := huniq pu hpu_mem pd (List.mem_of_find?_eq_some hfd) (find?_id_eq hfd).symm
          rw [← hpu_eq, ← hme, noOpaqueWall_symm]
          exact mayBind_noOpaqueWall sys po pu hmb_sc.1
      · simp at ho

/-- T7c (STRONG LAW II — NO DIRECT CAUSAL CROSSING):
    Every `+LeadsTo` edge in the projected Semantic Spacetime graph `Φ(S)` respects
    `noOpaqueWall` between source and target promisers—even for nested opaque superagents! -/
theorem opaque_no_direct_causal_crossing {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys)
    (d p : P) (pd pp : Promise A P O U M)
    (hfd : sys.find? d = some pd) (hfp : sys.find? p = some pp)
    (hedge : (projectSst sys).hasEdge (.promise d) .leadsTo (.promise p)) :
    noOpaqueWall sys.hierarchy sys.agents pd.promiser pp.promiser = true := by
  obtain ⟨pr, dep, strict, hmem, hd_eq, hp_eq, hdep⟩ := leadsTo_gives_dep sys hedge
  cases hd_eq; cases hp_eq
  have hpr_eq : pr = pp := huniq pr hmem pp (List.mem_of_find?_eq_some hfp) (find?_id_eq hfp).symm
  subst hpr_eq
  simp only [promiseDeps, List.mem_append] at hdep
  rcases hdep with hc | ho
  · exact condDeps_noOpaqueWall sys huniq pr.promiser false pr.cond d strict pd hc hfd
  · exact obsDeps_noOpaqueWall sys huniq pr.promiser pr.obs d strict pd ho hfd

/-- T7d (TOPOLOGICAL EVENT-HORIZON VERTEX-CUT THEOREM):
    For any opaque superagent `s`, EVERY causal path in `Φ(S)` from any strict interior promise
    `p_in` (`s ≺⁺ p_in.promiser`) to any exterior promise `p_out` (`¬(s ⪯ p_out.promiser)`)—even
    an enclosing ancestor superagent!—MUST pass through an intermediate surface promise owned by `s`. -/
theorem opaque_event_horizon_cut {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys)
    (s : A) (hs_mem : s ∈ sys.agents) (hs_op : sys.hierarchy.isOpaque s = true) :
    ∀ {x y : SstNode A P}, CausalReach (projectSst sys) x y →
      ∀ (p_in p_out : P) (pin pout : Promise A P O U M),
        x = .promise p_in → y = .promise p_out →
        sys.find? p_in = some pin → sys.find? p_out = some pout →
        isStrictAncAux sys.hierarchy sys.agents.length s pin.promiser = true →
        pout.promiser ≠ s →
        isStrictAncAux sys.hierarchy sys.agents.length s pout.promiser = false →
        ∃ ps ∈ sys.promises, ps.promiser = s ∧
          CausalReach (projectSst sys) (.promise p_in) (.promise ps.id) ∧
          CausalReach (projectSst sys) (.promise ps.id) (.promise p_out) := by
  intro x y hreach
  induction hreach with
  | refl _ =>
    intro p_in p_out pin pout hx hy hfin hfout hin _ hout_anc
    rw [hx] at hy; cases hy
    rw [hfin] at hfout; cases hfout
    rw [hin] at hout_anc; cases hout_anc
  | @step a b c hedge hrest ih =>
    intro p_in p_out pin pout ha hc hfin hfout hin hout_ne hout_anc
    obtain ⟨pr_mid, dep, _, hmid_mem, ha', hb', _⟩ := leadsTo_gives_dep sys hedge
    rw [ha] at ha'; cases ha'
    have hmid_find : sys.find? pr_mid.id = some pr_mid :=
      find?_eq_some_of_unique sys huniq pr_mid hmid_mem
    have hedge' : (projectSst sys).hasEdge (.promise p_in) .leadsTo (.promise pr_mid.id) := by
      rw [← ha, ← hb']; exact hedge
    have hwall := opaque_no_direct_causal_crossing sys huniq p_in pr_mid.id pin pr_mid hfin hmid_find hedge'
    rcases noOpaqueWall_imp_in_of_strict sys.hierarchy sys.agents s pin.promiser pr_mid.promiser
        hs_mem hs_op hin hwall with hsurf | hstill_in
    · refine ⟨pr_mid, hmid_mem, hsurf, .step hedge' (.refl _), ?_⟩
      rw [← hb', ← hc]; exact hrest
    · obtain ⟨ps, hps_mem, hps_surf, h1, h2⟩ :=
        ih pr_mid.id p_out pr_mid pout hb' hc hmid_find hfout hstill_in hout_ne hout_anc
      exact ⟨ps, hps_mem, hps_surf, .step hedge' h1, h2⟩

end Baugr
