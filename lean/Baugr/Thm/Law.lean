/-
  Baugr.Thm.Law — Generalized Monoidal Valency, Composable ScopeLaws &
  Universal Static Upper-Bound Discharge (T8a–T8f)
-/
import Baugr.Law
import Baugr.Thm.Quenching

namespace Baugr

theorem valency_filter_le {α R : Type} [ResourceMonoid R]
    (weight : α → R) (p : α → Bool) (xs : List α) :
    ResourceMonoid.le (sumResource weight (xs.filter p)) (sumResource weight xs) := by
  induction xs with
  | nil => exact ResourceMonoid.le_refl _
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases p x with
    | true =>
      simp only [sumResource]
      exact ResourceMonoid.add_le_add _ _ _ _ (ResourceMonoid.le_refl _) ih
    | false =>
      simp only [sumResource]
      have h0 : ResourceMonoid.le
          (ResourceMonoid.add ResourceMonoid.zero (sumResource weight (xs.filter p)))
          (ResourceMonoid.add (weight x) (sumResource weight xs)) :=
        ResourceMonoid.add_le_add _ _ _ _ (ResourceMonoid.zero_le _) ih
      rwa [ResourceMonoid.zero_add] at h0

/-- T8a: Valency downward closure (withdrawal safety over any Ordered Commutative Monoid). -/
theorem valency_withdrawal_safe {α R : Type} [ResourceMonoid R]
    (weight : α → R) (cap : R) (p : α → Bool) (xs : List α)
    (hok : ResourceMonoid.le (sumResource weight xs) cap) :
    ResourceMonoid.le (sumResource weight (xs.filter p)) cap :=
  ResourceMonoid.le_trans _ _ _ (valency_filter_le weight p xs) hok

/-- T8b: Composable ScopeLaw conjunction soundness. -/
theorem allLaws_cons {V : Type} (L : ScopeLaw V) (ls : List (ScopeLaw V)) (v : V) :
    allLaws (L :: ls) v ↔ (L v ∧ allLaws ls v) := by
  simp [allLaws]

/-- T8c: Every runtime active binding under ANY observer-local assessment `α` and state `S`
    belongs to the static upper-bound binding set `staticMaxBindings sys`. -/
theorem activeBindings_subset_staticMax {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (S : State P O U)
    (b : P × P) (hb : b ∈ activeBindings sys α S) :
    b ∈ staticMaxBindings sys := by
  simp only [activeBindings, List.mem_flatMap] at hb
  obtain ⟨po, hpo_mem, hpo_in⟩ := hb
  simp only [staticMaxBindings, List.mem_flatMap]
  refine ⟨po, hpo_mem, ?_⟩
  cases hpo_off : po.isOffer with
  | false => simp [hpo_off] at hpo_in
  | true =>
    simp only [hpo_off, ↓reduceIte, List.mem_filterMap] at hpo_in ⊢
    obtain ⟨pu, hpu_mem, hpu_some⟩ := hpo_in
    refine ⟨pu, hpu_mem, ?_⟩
    split at hpu_some
    · next hcond =>
      simp only [Bool.and_eq_true] at hcond
      have hmb := runtimeOverlap_isSome_imp_mayBind sys S po pu hcond.1.1.2
      simp only [hcond.1.1.1, hmb, Bool.and_self, ↓reduceIte]
      exact hpu_some
    · cases hpu_some

/-- A collective law over binding lists is downward-closed (anti-monotone) if holding on a
    superset of bindings guarantees holding on every subset. -/
def DownwardClosed {α : Type} (L : ScopeLaw (List α)) : Prop :=
  ∀ (B₁ B₂ : List α), (∀ x ∈ B₁, x ∈ B₂) → L B₂ → L B₁

/-- T8d: Universal Static Upper-Bound Discharge — ANY downward-closed ScopeLaw that holds on
    `staticMaxBindings sys` holds universally across ALL runtime assessments `α` and
    stratified evaluations (catching hidden failover negations that optimistic α misses!). -/
theorem static_discharge_universal {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (L : ScopeLaw (List (P × P)))
    (hdown : DownwardClosed L) (hstatic : L (staticMaxBindings sys)) :
    ∀ (α : Assessment A P) (rank : P → Nat) (steps maxS : Nat),
      L (activeBindings sys α (evalStratified sys α rank steps maxS)) := by
  intro α rank steps maxS
  exact hdown _ _ (activeBindings_subset_staticMax sys α _) hstatic

/-- T8e: Pairwise key disjointness (`DisjointBy`) is downward-closed. -/
theorem disjoint_downward_closed {α K : Type} (key : α → Option K) :
    DownwardClosed (fun (B : List α) =>
      ∀ x ∈ B, ∀ y ∈ B, ∀ k, key x = some k → key y = some k → x = y) := by
  intro B₁ B₂ hsub hL x hx y hy k hkx hky
  exact hL x (hsub x hx) y (hsub y hy) k hkx hky

/-- T8f: Burgess grouped coordination agreement `C(b)` (`AgreementBy`) is downward-closed. -/
theorem agreement_downward_closed {α G V : Type} (extract : α → Option (G × V)) :
    DownwardClosed (fun (B : List α) =>
      ∀ x ∈ B, ∀ y ∈ B, ∀ g v₁ v₂,
        extract x = some (g, v₁) → extract y = some (g, v₂) → v₁ = v₂) := by
  intro B₁ B₂ hsub hL x hx y hy g v₁ v₂ h1 h2
  exact hL x (hsub x hx) y (hsub y hy) g v₁ v₂ h1 h2

end Baugr
