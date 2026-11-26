/-
  Baugr.Thm.Law — Generalized Monoidal Valency & Composable ScopeLaw Soundness (T8)
-/
import Baugr.Law

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

end Baugr
