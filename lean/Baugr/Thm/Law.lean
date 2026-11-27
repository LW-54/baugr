/-
  Baugr.Thm.Law — Generalized Monoidal Valency, Grouped Cross-Offer Budgets,
  Composable ScopeLaws & Universal Static Upper-Bound Discharge (T8a–T8g)
-/
import Baugr.Law
import Baugr.Thm.Quenching

namespace Baugr

theorem sumResource_sublist_le {α R : Type} [ResourceMonoid R]
    (weight : α → R) {xs ys : List α} (hsub : List.Sublist xs ys) :
    ResourceMonoid.le (sumResource weight xs) (sumResource weight ys) := by
  induction hsub with
  | slnil => exact ResourceMonoid.le_refl _
  | cons a _ ih =>
    simp only [sumResource]
    have h0 := ResourceMonoid.add_le_add _ _ _ _ (ResourceMonoid.zero_le (weight a)) ih
    rwa [ResourceMonoid.zero_add] at h0
  | cons_cons a _ ih =>
    simp only [sumResource]
    exact ResourceMonoid.add_le_add _ _ _ _ (ResourceMonoid.le_refl _) ih

/-- T8a: Valency downward closure (withdrawal safety over any Ordered Commutative Monoid,
    including `Nat`, `Cap R`, and multi-dimensional products `R₁ × R₂`). -/
theorem valency_withdrawal_safe {α R : Type} [ResourceMonoid R]
    (weight : α → R) (cap : R) (p : α → Bool) (xs : List α)
    (hok : ResourceMonoid.le (sumResource weight xs) cap) :
    ResourceMonoid.le (sumResource weight (xs.filter p)) cap :=
  ResourceMonoid.le_trans _ _ _ (sumResource_sublist_le weight (List.filter_sublist)) hok

/-- T8b: Composable ScopeLaw conjunction soundness. -/
theorem allLaws_cons {V : Type} (L : ScopeLaw V) (ls : List (ScopeLaw V)) (v : V) :
    allLaws (L :: ls) v ↔ (L v ∧ allLaws ls v) := by
  simp [allLaws]

private theorem sublist_filterMap {α β : Type} (f g : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, ∀ y, f x = some y → g x = some y) :
    List.Sublist (xs.filterMap f) (xs.filterMap g) := by
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    have hxs := ih (fun z hz => h z (List.mem_cons_of_mem x hz))
    cases hfx : f x with
    | none =>
      cases g x with
      | none => exact hxs
      | some _ => exact .cons _ hxs
    | some y =>
      rw [h x List.mem_cons_self y hfx]
      exact .cons_cons y hxs

private theorem sublist_flatMap {α β : Type} (f g : α → List β) (xs : List α)
    (h : ∀ x ∈ xs, List.Sublist (f x) (g x)) :
    List.Sublist (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x List.mem_cons_self).append (ih (fun z hz => h z (List.mem_cons_of_mem x hz)))

/-- T8c: Under ANY observer-local assessment `α` and state `S`, the runtime active bindings
    list is a `List.Sublist` of `staticMaxBindings sys` (preserving multiplicity for monoidal budgets!). -/
theorem activeBindings_sublist_staticMax {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (S : State P O U) :
    List.Sublist (activeBindings sys α S) (staticMaxBindings sys) := by
  simp only [activeBindings, staticMaxBindings]
  apply sublist_flatMap
  intro po _
  cases po.isOffer with
  | false => exact .slnil
  | true =>
    simp only [↓reduceIte]
    apply sublist_filterMap
    intro pu _ pair hpair
    split at hpair
    · next hcond =>
      simp only [Bool.and_eq_true] at hcond
      have hmb := runtimeOverlap_isSome_imp_mayBind sys S po pu hcond.1.1.2
      simp only [hcond.1.1.1, hmb, Bool.and_self, ↓reduceIte]
      exact hpair
    · cases hpair

/-- A collective law over binding lists is downward-closed (anti-monotone) if holding on a
    superlist `B₂` guarantees holding on every sublist `B₁`. -/
def DownwardClosed {α : Type} (L : ScopeLaw (List α)) : Prop :=
  ∀ (B₁ B₂ : List α), List.Sublist B₁ B₂ → L B₂ → L B₁

/-- T8d: Universal Static Upper-Bound Discharge — ANY downward-closed ScopeLaw that holds on
    `staticMaxBindings sys` holds universally across ALL runtime assessments `α` and
    stratified evaluations (catching hidden failover negations that optimistic α misses!). -/
theorem static_discharge_universal {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (L : ScopeLaw (List (P × P)))
    (hdown : DownwardClosed L) (hstatic : L (staticMaxBindings sys)) :
    ∀ (α : Assessment A P) (rank : P → Nat) (steps maxS : Nat),
      L (activeBindings sys α (evalStratified sys α rank steps maxS)) := by
  intro α rank steps maxS
  exact hdown _ _ (activeBindings_sublist_staticMax sys α _) hstatic

/-- T8e: Grouped cross-offer monoidal budgets (`BudgetBy`, subsuming single-offer valency and `Cap R`)
    are downward-closed and universally statically dischargeable. -/
theorem budget_downward_closed {α G R : Type} [DecidableEq G] [ResourceMonoid R]
    (extract : α → Option (G × R)) (cap : G → R) :
    DownwardClosed (fun (B : List α) =>
      ∀ g, ResourceMonoid.le (sumResource (fun x =>
        match extract x with
        | some (g', w) => if g' == g then w else ResourceMonoid.zero
        | none         => ResourceMonoid.zero) B) (cap g)) := by
  intro B₁ B₂ hsub hL g
  exact ResourceMonoid.le_trans _ _ _ (sumResource_sublist_le _ hsub) (hL g)

/-- T8f: Pairwise key disjointness (`DisjointBy`) is downward-closed. -/
theorem disjoint_downward_closed {α K : Type} (key : α → Option K) :
    DownwardClosed (fun (B : List α) =>
      ∀ x ∈ B, ∀ y ∈ B, ∀ k, key x = some k → key y = some k → x = y) := by
  intro B₁ B₂ hsub hL x hx y hy k hkx hky
  exact hL x (hsub.subset hx) y (hsub.subset hy) k hkx hky

/-- T8g: Burgess grouped coordination agreement `C(b)` (`AgreementBy`) is downward-closed. -/
theorem agreement_downward_closed {α G V : Type} (extract : α → Option (G × V)) :
    DownwardClosed (fun (B : List α) =>
      ∀ x ∈ B, ∀ y ∈ B, ∀ g v₁ v₂,
        extract x = some (g, v₁) → extract y = some (g, v₂) → v₁ = v₂) := by
  intro B₁ B₂ hsub hL x hx y hy g v₁ v₂ h1 h2
  exact hL x (hsub.subset hx) y (hsub.subset hy) g v₁ v₂ h1 h2

end Baugr
