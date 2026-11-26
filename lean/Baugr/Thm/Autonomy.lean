/-
  Baugr.Thm.Autonomy — Promise Theory Axiom of Autonomy (T4)
  Adding an unaccepted offer/imposition cannot alter any existing promise's condition evaluation.
-/
import Baugr.Thm.Quenching

namespace Baugr

private theorem find?_append_of_ne {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U) (q : P) (hne : q ≠ extra.id) :
    ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? q =
    sys.find? q := by
  simp only [PromiseSystem.find?, List.find?_append]
  cases sys.promises.find? (fun x => x.id == q) with
  | some _ => simp
  | none =>
    have hb : (extra.id == q) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
    simp [hb]

mutual
theorem evalCond_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U)
    (α : Assessment A P) (Q : P → Bool) (me : A)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, staticBindable sys extra pu = false) :
    ∀ (c : Cond P),
      (∀ d n, (d, n) ∈ condDeps sys false c → d ≠ extra.id) →
      evalCond { sys with promises := sys.promises ++ [extra] } α Q me c =
      evalCond sys α Q me c
  | .selfPromise q, hf => by
    have hfind := find?_append_of_ne sys extra q (hf q false (by simp [condDeps]))
    simp [evalCond, hfind]
  | .interior q, hf => by
    have hfind := find?_append_of_ne sys extra q (hf q false (by simp [condDeps]))
    simp [evalCond, hfind]
  | .assisted u minP, hf => by
    have hne : u ≠ extra.id := by
      apply hf u false; simp only [condDeps]; cases sys.find? u <;> simp
    have hfind := find?_append_of_ne sys extra u hne
    simp only [evalCond, hfind]
    cases hfu : sys.find? u with
    | none => rfl
    | some pu =>
      have hpu_mem : pu ∈ sys.promises := List.mem_of_find?_eq_some hfu
      have hsb : ∀ po, staticBindable { sys with promises := sys.promises ++ [extra] } po pu =
                       staticBindable sys po pu := fun _ => rfl
      simp only [hsb, countP_append_singleton]
      have hx : (staticBindable sys extra pu && Q extra.id && α me extra.id) = false := by
        simp [hunacc pu hpu_mem]
      simp [hx]
  | .accepted o minA, hf => by
    have hne : o ≠ extra.id := by
      apply hf o false; simp only [condDeps]; cases sys.find? o <;> simp
    have hfind := find?_append_of_ne sys extra o hne
    simp only [evalCond, hfind]
    cases hfo : sys.find? o with
    | none => rfl
    | some po =>
      have hsb : ∀ pu, staticBindable { sys with promises := sys.promises ++ [extra] } po pu =
                       staticBindable sys po pu := fun _ => rfl
      simp only [hsb, countP_append_singleton]
      have hx : staticBindable sys po extra = false := by
        cases hbody : extra.body with
        | offer _ => cases po.body <;> simp [staticBindable, hbody]
        | use _   => simp [Promise.isOffer, hbody] at hoff
      simp [hx]
  | .atLeast k cs, hf => by
    simp only [evalCond]
    rw [countSat_unaccepted_offer_inert sys extra α Q me hoff hunacc cs hf]
  | .not c, hf => by
    simp only [evalCond]
    have hf' : ∀ d n, (d, n) ∈ condDeps sys false c → d ≠ extra.id := by
      intro d n hdn
      obtain ⟨m, hm⟩ := (condDeps_neg_flip sys false d c).mp ⟨n, hdn⟩
      exact hf d m hm
    rw [evalCond_unaccepted_offer_inert sys extra α Q me hoff hunacc c hf']

theorem countSat_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U)
    (α : Assessment A P) (Q : P → Bool) (me : A)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, staticBindable sys extra pu = false) :
    ∀ (cs : List (Cond P)),
      (∀ d n, (d, n) ∈ listCondDeps sys false cs → d ≠ extra.id) →
      countSat { sys with promises := sys.promises ++ [extra] } α Q me cs =
      countSat sys α Q me cs
  | [], _ => rfl
  | c :: rs, hf => by
    simp only [countSat]
    have h1 := evalCond_unaccepted_offer_inert sys extra α Q me hoff hunacc c
      (fun d n hdn => hf d n (List.mem_append_left _ hdn))
    have h2 := countSat_unaccepted_offer_inert sys extra α Q me hoff hunacc rs
      (fun d n hdn => hf d n (List.mem_append_right _ hdn))
    rw [h1, h2]
end

/-- T4: Axiom of Autonomy — an unaccepted offer/imposition cannot alter any existing promise's condition. -/
theorem autonomy_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U)
    (α : Assessment A P) (Q : P → Bool)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, staticBindable sys extra pu = false)
    (pr : Promise A P O U)
    (hno_ref : ∀ d n, (d, n) ∈ condDeps sys false pr.cond → d ≠ extra.id) :
    evalCond { sys with promises := sys.promises ++ [extra] } α Q pr.promiser pr.cond =
    evalCond sys α Q pr.promiser pr.cond :=
  evalCond_unaccepted_offer_inert sys extra α Q pr.promiser hoff hunacc pr.cond hno_ref

end Baugr
