/-
  Baugr.Thm.Stratification — Stratum Monotonicity, Finite Fixed-Point Convergence &
  Apt–Blair–Walker Stratification Independence Theorem (T3b–T3d)

  Uses the Semantic Spacetime light cone (`CausalReach`) directly to prove that ANY two
  valid stratifications of a PromiseSystem produce the exact same resolved fixed point.
-/
import Baugr.Thm.LightCone

namespace Baugr

-- ----------------------------------------------------------------------------
-- Stratum monotonicity, invariants, and exact finite convergence (≤ |P| + 1 steps)
-- ----------------------------------------------------------------------------

/-- T3b: `stratumStep` is monotone on stratum `s` under arbitrary nested `Not` for any valid stratification. -/
theorem stratumStep_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (hv : ValidStratification sys rank)
    (s : Nat) (base Q₁ Q₂ : P → Bool)
    (hsub : SubSet Q₁ Q₂)
    (hlow : ∀ d, rank d < s → Q₁ d = Q₂ d) :
    SubSet (stratumStep sys α rank s base Q₁) (stratumStep sys α rank s base Q₂) := by
  intro pid h
  simp only [stratumStep] at h ⊢
  split at h
  · next hlt => simp [hlt, h]
  · next hge =>
    simp only [hge, ↓reduceIte]
    split at h
    · next heq =>
      simp only [heq, ↓reduceIte, quenchStep] at h ⊢
      cases hfind : sys.find? pid with
      | none => simp [hfind] at h
      | some pr =>
        simp only [hfind] at h ⊢
        have hmem : pr ∈ sys.promises := List.mem_of_find?_eq_some hfind
        have hid : pr.id = pid := find?_id_eq hfind
        have hrank_eq : rank pr.id = s := by rw [hid]; exact eq_of_beq heq
        exact evalCond_mono_pol sys α Q₁ Q₂ pr.promiser false pr.cond (fun d b hdep => by
          have hst := hv pr hmem d b hdep
          cases b with
          | false => exact hsub d
          | true =>
            simp only [↓reduceIte] at hst
            have hlt_s : rank d < s := by rw [← hrank_eq]; exact hst
            simp only [BoolLePol, ↓reduceIte]
            intro h2; rw [hlow d hlt_s]; exact h2) h
    · simp at h

theorem stratumIter_low {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : P → Bool) :
    ∀ n d, rank d < s → stratumIter sys α rank s base n d = base d
  | 0, d, hlt => by simp [stratumIter, hlt]
  | n + 1, d, hlt => by simp [stratumIter, stratumStep, hlt]

theorem stratumIter_high {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : P → Bool) :
    ∀ n d, s < rank d → stratumIter sys α rank s base n d = false
  | 0, d, hgt => by
    have hnot : ¬ rank d < s := by omega
    simp [stratumIter, hnot]
  | n + 1, d, hgt => by
    have hnot : ¬ rank d < s := by omega
    have hne : (rank d == s) = false := by simp [beq_eq_false_iff_ne]; omega
    simp [stratumIter, stratumStep, hnot, hne]

theorem stratumIter_chain {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (hv : ValidStratification sys rank)
    (s : Nat) (base : P → Bool) :
    ∀ n, SubSet (stratumIter sys α rank s base n) (stratumIter sys α rank s base (n + 1))
  | 0 => by
    intro d h
    simp only [stratumIter] at h ⊢
    split at h
    · next hlt => simp [stratumStep, hlt, h]
    · simp at h
  | n + 1 =>
    stratumStep_mono sys α rank hv s base _ _ (stratumIter_chain sys α rank hv s base n)
      (fun d hlt => by rw [stratumIter_low sys α rank s base n d hlt,
                           stratumIter_low sys α rank s base (n + 1) d hlt])

theorem stratumIter_le_any_prefixed {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (hv : ValidStratification sys rank)
    (s : Nat) (base F : P → Bool)
    (hlow : ∀ d, rank d < s → F d = base d)
    (hpre : SubSet (stratumStep sys α rank s base F) F) :
    ∀ n, SubSet (stratumIter sys α rank s base n) F
  | 0 => by
    intro d h
    simp only [stratumIter] at h
    split at h
    · next hlt => rw [hlow d hlt]; exact h
    · simp at h
  | n + 1 => by
    have ih := stratumIter_le_any_prefixed sys α rank hv s base F hlow hpre n
    intro d hd
    have hlow_eq : ∀ q, rank q < s → stratumIter sys α rank s base n q = F q := fun q hlt => by
      rw [stratumIter_low sys α rank s base n q hlt, hlow q hlt]
    exact hpre d (stratumStep_mono sys α rank hv s base _ F ih hlow_eq d hd)

private theorem nat_chain_stabilizes (f : Nat → Nat) (B : Nat)
    (hmono : ∀ n, f n ≤ f (n + 1)) (hbnd : ∀ n, f n ≤ B) :
    ∀ m k, B - f k ≤ m → ∃ j, j ≤ k + m ∧ f j = f (j + 1)
  | 0, k, hm =>
      ⟨k, Nat.le_refl k, by have := hmono k; have := hbnd (k + 1); omega⟩
  | m + 1, k, hm =>
      if heq : f k = f (k + 1) then
        ⟨k, by omega, heq⟩
      else
        have hlt : f k < f (k + 1) := by have := hmono k; omega
        let ⟨j, hj, hfeq⟩ := nat_chain_stabilizes f B hmono hbnd m (k + 1) (by omega)
        ⟨j, by omega, hfeq⟩

private theorem stratumStep_ext_promises {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base Q₁ Q₂ : P → Bool)
    (heq : ∀ pr ∈ sys.promises, Q₁ pr.id = Q₂ pr.id) :
    stratumStep sys α rank s base Q₁ = stratumStep sys α rank s base Q₂ := by
  have hq := quenchStep_ext_promises sys α Q₁ Q₂ heq
  funext pid
  simp only [stratumStep, hq]

private theorem stratumIter_stable_after {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (s : Nat) (base : P → Bool) (j : Nat)
    (hfix : stratumIter sys α rank s base (j + 1) = stratumIter sys α rank s base (j + 2)) :
    ∀ t, stratumIter sys α rank s base (j + 1 + t) = stratumIter sys α rank s base (j + 1)
  | 0 => rfl
  | t + 1 => by
    have ih := stratumIter_stable_after sys α rank s base j hfix t
    show stratumStep sys α rank s base (stratumIter sys α rank s base (j + 1 + t)) = _
    rw [ih]
    exact hfix.symm

/-- T3c: Exact finite convergence — every stratum reaches an exact fixed point within `|P| + 1` steps. -/
theorem stratumIter_fixed_point {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (hv : ValidStratification sys rank)
    (s : Nat) (base : P → Bool) (steps : Nat)
    (hsteps : sys.promises.length + 1 ≤ steps) :
    stratumStep sys α rank s base (stratumIter sys α rank s base steps) =
    stratumIter sys α rank s base steps := by
  let S := stratumIter sys α rank s base
  let f : Nat → Nat := fun n => countP (fun pr => S n pr.id) sys.promises
  have hmono : ∀ n, f n ≤ f (n + 1) := fun n =>
    countP_mono _ _ sys.promises fun pr _ hp => stratumIter_chain sys α rank hv s base n pr.id hp
  have hbnd : ∀ n, f n ≤ sys.promises.length := fun n => countP_le_length _ sys.promises
  obtain ⟨j, hj_le, hfeq⟩ := nat_chain_stabilizes f sys.promises.length hmono hbnd sys.promises.length 0 (by omega)
  have hagree : ∀ pr ∈ sys.promises, S j pr.id = S (j + 1) pr.id :=
    countP_eq_imp_all_eq _ _ sys.promises
      (fun pr _ hp => stratumIter_chain sys α rank hv s base j pr.id hp) hfeq
  have hstep_eq : S (j + 1) = S (j + 2) :=
    stratumStep_ext_promises sys α rank s base (S j) (S (j + 1)) hagree
  have hst := stratumIter_stable_after sys α rank s base j hstep_eq
  have hsteps_eq : steps = j + 1 + (steps - (j + 1)) := by omega
  have hs1 : S steps = S (j + 1) := by rw [hsteps_eq]; exact hst (steps - (j + 1))
  have hs2 : S (steps + 1) = S (j + 1) := by
    have h2 : steps + 1 = j + 1 + (steps - j) := by omega
    rw [h2]; exact hst (steps - j)
  show S (steps + 1) = S steps
  rw [hs1, hs2]

-- ----------------------------------------------------------------------------
-- Global fixed-point property of `evalStratified`
-- ----------------------------------------------------------------------------

theorem evalStratified_none_eq_false {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (steps : Nat) (p : P) (hnone : sys.find? p = none) :
    ∀ s, evalStratified sys α rank steps s p = false := by
  have hiter : ∀ s base, base p = false → ∀ n, stratumIter sys α rank s base n p = false := by
    intro s base hb n
    induction n with
    | zero => simp only [stratumIter]; split; exact hb; rfl
    | succ k _ =>
      simp only [stratumIter, stratumStep]
      split
      · exact hb
      · split
        · simp [quenchStep, hnone]
        · rfl
  intro s
  induction s with
  | zero => exact hiter 0 (fun _ => false) rfl steps
  | succ k ih => exact hiter (k + 1) _ ih steps

theorem evalStratified_low {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (steps : Nat) :
    ∀ s₁ s₂, s₁ ≤ s₂ → ∀ p, rank p ≤ s₁ →
      evalStratified sys α rank steps s₂ p = evalStratified sys α rank steps s₁ p := by
  intro s₁ s₂ hle
  induction hle with
  | refl => intro _ _; rfl
  | @step m hle' ih =>
    intro p hp
    show stratumIter sys α rank (m + 1) (evalStratified sys α rank steps m) steps p = _
    rw [stratumIter_low sys α rank (m + 1) _ steps p (Nat.lt_succ_of_le (Nat.le_trans hp hle'))]
    exact ih p hp

theorem evalStratified_fixed_below {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (hv : ValidStratification sys rank)
    (steps : Nat) (hsteps : sys.promises.length + 1 ≤ steps) :
    ∀ s p, rank p ≤ s →
      evalStratified sys α rank steps s p =
      quenchStep sys α (evalStratified sys α rank steps s) p := by
  intro s
  induction s with
  | zero =>
    intro p hp
    have h0 : rank p = 0 := by omega
    have hfix := stratumIter_fixed_point sys α rank hv 0 (fun _ => false) steps hsteps
    have hp_fix := congrFun hfix p
    simp only [evalStratified] at hp_fix ⊢
    simp only [stratumStep, Nat.not_lt_zero, ↓reduceIte, h0, beq_self_eq_true] at hp_fix
    exact hp_fix.symm
  | succ k ih =>
    intro p hp
    by_cases hlt : rank p < k + 1
    · have hle_k : rank p ≤ k := by omega
      have hcur : evalStratified sys α rank steps (k + 1) p =
                  evalStratified sys α rank steps k p :=
        evalStratified_low sys α rank steps k (k + 1) (Nat.le_succ k) p hle_k
      rw [hcur, ih p hle_k]
      simp only [quenchStep]
      cases hfind : sys.find? p with
      | none => rfl
      | some pr =>
        have hmem : pr ∈ sys.promises := List.mem_of_find?_eq_some hfind
        have hid : pr.id = p := find?_id_eq hfind
        apply evalCond_local
        intro d neg hdep _
        have hst := hv pr hmem d neg hdep
        rw [hid] at hst
        have hd_le : rank d ≤ k := by
          cases neg <;> simp at hst <;> omega
        exact ⟨(evalStratified_low sys α rank steps k (k + 1) (Nat.le_succ k) d hd_le).symm, rfl⟩
    · have heq : rank p = k + 1 := by omega
      have hfix := stratumIter_fixed_point sys α rank hv (k + 1)
        (evalStratified sys α rank steps k) steps hsteps
      have hp_fix := congrFun hfix p
      simp only [evalStratified] at hp_fix ⊢
      simp only [stratumStep, heq, Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true] at hp_fix
      exact hp_fix.symm

/-- T3c: Global fixed-point soundness — `evalStratified` produces an exact fixed point of `quenchStep`. -/
theorem evalStratified_fixed_point {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank : P → Nat) (M : Nat)
    (hv : ValidStratification sys rank)
    (hb : ∀ pr ∈ sys.promises, rank pr.id ≤ M)
    (steps : Nat) (hsteps : sys.promises.length + 1 ≤ steps) :
    quenchStep sys α (evalStratified sys α rank steps M) =
    evalStratified sys α rank steps M := by
  funext p
  cases hfind : sys.find? p with
  | none =>
    simp only [quenchStep, hfind]
    exact (evalStratified_none_eq_false sys α rank steps p hfind M).symm
  | some pr =>
    have hmem : pr ∈ sys.promises := List.mem_of_find?_eq_some hfind
    have hid : pr.id = p := find?_id_eq hfind
    have hle : rank p ≤ M := by rw [← hid]; exact hb pr hmem
    exact (evalStratified_fixed_below sys α rank hv steps hsteps M p hle).symm

-- ----------------------------------------------------------------------------
-- T3d: Apt–Blair–Walker Stratification Independence via SST Light Cones
-- ----------------------------------------------------------------------------

/-- Valid stratifications are monotone along Semantic Spacetime causal paths `CausalReach`. -/
theorem causalReach_rank_le {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (rank : P → Nat) (hv : ValidStratification sys rank) :
    ∀ {x y : SstNode A P}, CausalReach (projectSst sys) x y →
      ∀ d p, x = .promise d → y = .promise p → rank d ≤ rank p := by
  intro x y hreach
  induction hreach with
  | refl _ =>
    intro d p h1 h2
    rw [h1] at h2; cases h2; exact Nat.le_refl _
  | @step a b c hedge _ ih =>
    intro d p ha hc
    obtain ⟨pr, dep, neg, hmem, ha', hb', hdep⟩ := leadsTo_gives_dep sys hedge
    rw [ha] at ha'; cases ha'
    have hst := hv pr hmem d neg hdep
    have hstep_le : rank d ≤ rank pr.id := by
      cases neg <;> simp at hst <;> omega
    exact Nat.le_trans hstep_le (ih pr.id p hb' hc)

private theorem evalStratified_le_of_cone {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank₁ : P → Nat) (M₁ : Nat)
    (hv₁ : ValidStratification sys rank₁)
    (hb₁ : ∀ pr ∈ sys.promises, rank₁ pr.id ≤ M₁)
    (steps : Nat)
    (F₂ : P → Bool) (hfix₂ : quenchStep sys α F₂ = F₂) (p : P)
    (hcone_lt : ∀ d, CausalReach (projectSst sys) (.promise d) (.promise p) →
      rank₁ d < rank₁ p → evalStratified sys α rank₁ steps M₁ d = F₂ d) :
    evalStratified sys α rank₁ steps M₁ p = true → F₂ p = true := by
  classical
  cases hfp : sys.find? p with
  | none =>
    intro h
    rw [evalStratified_none_eq_false sys α rank₁ steps p hfp M₁] at h
    cases h
  | some pr =>
    have hmem_p : pr ∈ sys.promises := List.mem_of_find?_eq_some hfp
    have hid_p : pr.id = p := find?_id_eq hfp
    have hp_le : rank₁ p ≤ M₁ := by rw [← hid_p]; exact hb₁ pr hmem_p
    let s := rank₁ p
    let F₁ := evalStratified sys α rank₁ steps M₁
    let base : P → Bool :=
      match s with
      | 0     => fun _ => false
      | k + 1 => evalStratified sys α rank₁ steps k
    have hbase_eq : ∀ d, rank₁ d < s → base d = F₁ d := by
      intro d hlt
      cases hs : s with
      | zero => omega
      | succ k =>
        simp only [base, hs]
        exact (evalStratified_low sys α rank₁ steps k M₁ (by omega) d (by omega)).symm
    have hFs : evalStratified sys α rank₁ steps s = stratumIter sys α rank₁ s base steps := by
      cases hs : s <;> simp [base, hs, evalStratified]
    let G : P → Bool := fun x =>
      if rank₁ x < s then base x
      else if rank₁ x = s then
        (if CausalReach (projectSst sys) (.promise x) (.promise p) then F₂ x else true)
      else false
    have hG_low : ∀ d, rank₁ d < s → G d = base d := fun d hlt => by simp [G, hlt]
    have hG_pre : SubSet (stratumStep sys α rank₁ s base G) G := by
      intro x hx
      simp only [stratumStep] at hx
      split at hx
      · next hlt => simp [G, hlt, hx]
      · split at hx
        · next heq =>
          have hxs : rank₁ x = s := eq_of_beq heq
          simp only [G, hxs, Nat.lt_irrefl, ↓reduceIte]
          split
          · next hreach =>
            simp only [quenchStep] at hx
            cases hfx : sys.find? x with
            | none => simp [hfx] at hx
            | some prx =>
              simp only [hfx] at hx
              have hmem_x : prx ∈ sys.promises := List.mem_of_find?_eq_some hfx
              have hid_x : prx.id = x := find?_id_eq hfx
              have hev : evalCond sys α G prx.promiser prx.cond =
                         evalCond sys α F₂ prx.promiser prx.cond := by
                apply evalCond_local
                intro d neg hdep hex
                have hedge : SstEdge.mk (.promise d) .leadsTo (.promise x) ∈ (projectSst sys).edges := by
                  rw [← hid_x]; exact dep_gives_leadsTo sys prx hmem_x d neg hdep hex
                have hd_reach : CausalReach (projectSst sys) (.promise d) (.promise p) :=
                  .step hedge hreach
                have hst := hv₁ prx hmem_x d neg hdep
                rw [hid_x] at hst
                have hd_le : rank₁ d ≤ s := by
                  cases neg <;> simp at hst <;> omega
                by_cases hd_lt : rank₁ d < s
                · refine ⟨?_, rfl⟩
                  rw [hG_low d hd_lt, hbase_eq d hd_lt]
                  exact hcone_lt d hd_reach hd_lt
                · have hd_eq : rank₁ d = s := by omega
                  simp [G, hd_eq, hd_reach]
              rw [hev] at hx
              have hq2 : quenchStep sys α F₂ x = true := by simp [quenchStep, hfx, hx]
              rwa [hfix₂] at hq2
          · rfl
        · simp at hx
    intro hp1
    have hp_s : evalStratified sys α rank₁ steps s p = true := by
      rwa [evalStratified_low sys α rank₁ steps s M₁ hp_le p (Nat.le_refl s)] at hp1
    rw [hFs] at hp_s
    have hGp := stratumIter_le_any_prefixed sys α rank₁ hv₁ s base G hG_low hG_pre steps p hp_s
    have hrefl : CausalReach (projectSst sys) (.promise p) (.promise p) := .refl _
    simp only [G, s, Nat.lt_irrefl, ↓reduceIte, hrefl] at hGp
    exact hGp

/-- T3d (APT–BLAIR–WALKER STRATIFICATION INDEPENDENCE THEOREM):
    ANY two valid stratifications `rank₁` and `rank₂` of a PromiseSystem produce the
    EXACT SAME resolved fixed point (canonical independence of Kosaraju rank choices). -/
theorem stratification_independent {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (rank₁ rank₂ : P → Nat) (M₁ M₂ : Nat)
    (hv₁ : ValidStratification sys rank₁) (hv₂ : ValidStratification sys rank₂)
    (hb₁ : ∀ pr ∈ sys.promises, rank₁ pr.id ≤ M₁)
    (hb₂ : ∀ pr ∈ sys.promises, rank₂ pr.id ≤ M₂)
    (steps : Nat) (hsteps : sys.promises.length + 1 ≤ steps) :
    evalStratified sys α rank₁ steps M₁ = evalStratified sys α rank₂ steps M₂ := by
  have hfix₁ := evalStratified_fixed_point sys α rank₁ M₁ hv₁ hb₁ steps hsteps
  have hfix₂ := evalStratified_fixed_point sys α rank₂ M₂ hv₂ hb₂ steps hsteps
  suffices ∀ k p, rank₁ p + rank₂ p ≤ k →
      evalStratified sys α rank₁ steps M₁ p = evalStratified sys α rank₂ steps M₂ p by
    funext p; exact this (rank₁ p + rank₂ p) p (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro p hk
    have h12 := evalStratified_le_of_cone sys α rank₁ M₁ hv₁ hb₁ steps _ hfix₂ p
      (fun _ _ hlt => by omega)
    have h21 := evalStratified_le_of_cone sys α rank₂ M₂ hv₂ hb₂ steps _ hfix₁ p
      (fun _ _ hlt => by omega)
    cases h1 : evalStratified sys α rank₁ steps M₁ p <;>
      cases h2 : evalStratified sys α rank₂ steps M₂ p
    · rfl
    · have := h21 h2; rw [h1] at this; cases this
    · have := h12 h1; rw [h2] at this; cases this
    · rfl
  | succ k ih =>
    intro p hk
    have h12 := evalStratified_le_of_cone sys α rank₁ M₁ hv₁ hb₁ steps _ hfix₂ p
      (fun d hreach hlt => by
        have hr2 := causalReach_rank_le sys rank₂ hv₂ hreach d p rfl rfl
        exact ih d (by omega))
    have h21 := evalStratified_le_of_cone sys α rank₂ M₂ hv₂ hb₂ steps _ hfix₁ p
      (fun d hreach hlt => by
        have hr1 := causalReach_rank_le sys rank₁ hv₁ hreach d p rfl rfl
        exact (ih d (by omega)).symm)
    cases h1 : evalStratified sys α rank₁ steps M₁ p <;>
      cases h2 : evalStratified sys α rank₂ steps M₂ p
    · rfl
    · have := h21 h2; rw [h1] at this; cases this
    · have := h12 h1; rw [h2] at this; cases this
    · rfl

end Baugr
