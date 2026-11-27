/-
  Baugr.Thm.Autonomy — Promise Theory Axiom of Autonomy (T4)
  Adding an unaccepted offer/imposition from an external agent cannot alter any
  existing promise's condition evaluation, local observation view, or derived body —
  unconditionally, with ZERO syntactic side-conditions!
-/
import Baugr.Thm.Quenching

namespace Baugr

private theorem find?_append_of_ne {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M) (q : P) (hne : q ≠ extra.id) :
    ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? q =
    sys.find? q := by
  simp only [PromiseSystem.find?, List.find?_append]
  cases sys.promises.find? (fun x => x.id == q) with
  | some _ => simp
  | none =>
    have hb : (extra.id == q) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
    simp [hb]

private theorem find?_append_self_of_fresh {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (hfresh : sys.find? extra.id = none) :
    ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? extra.id =
    some extra := by
  simp only [PromiseSystem.find?, List.find?_append]
  have hnone : sys.promises.find? (fun x => x.id == extra.id) = none := hfresh
  simp [hnone]

private theorem runtimeOverlap_append_eq {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M) (S : State P O U)
    (po pu : Promise A P O U M) :
    runtimeOverlap { sys with promises := sys.promises ++ [extra] } S po pu =
    runtimeOverlap sys S po pu := rfl

private theorem isUse_false_of_isOffer {A P O U M : Type}
    (extra : Promise A P O U M) (hoff : extra.isOffer = true) :
    extra.isUse = false := by
  cases h : extra.body <;> simp_all [Promise.isOffer, Promise.isUse]

private theorem mayBind_to_offer_false {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po extra : Promise A P O U M)
    (hoff : extra.isOffer = true) :
    mayBind sys po extra = false := by
  have hnotuse := isUse_false_of_isOffer extra hoff
  simp [mayBind, structBindable, hnotuse]

mutual
theorem evalCond_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A)
    (hoff     : extra.isOffer = true)
    (hfresh   : sys.find? extra.id = none)
    (hext     : extra.promiser ≠ me)
    (hnot_int : visibleInterior sys.hierarchy sys.agents me extra.promiser = false)
    (hunacc   : ∀ pu ∈ sys.promises, mayBind sys extra pu = false) :
    ∀ (c : Cond P),
      evalCond { sys with promises := sys.promises ++ [extra] } α S me c =
      evalCond sys α S me c
  | .selfPromise q => by
    by_cases hq : q = extra.id
    · subst hq
      rw [evalCond, evalCond, find?_append_self_of_fresh sys extra hfresh, hfresh]
      have hne : (extra.promiser == me) = false := by simp [beq_eq_false_iff_ne, hext]
      simp [hne]
    · simp [evalCond, find?_append_of_ne sys extra q hq]
  | .interior q => by
    by_cases hq : q = extra.id
    · subst hq
      rw [evalCond, evalCond, find?_append_self_of_fresh sys extra hfresh, hfresh]
      simp [hnot_int]
    · simp [evalCond, find?_append_of_ne sys extra q hq]
  | .assisted u minP => by
    by_cases hu : u = extra.id
    · subst hu
      rw [evalCond, evalCond, find?_append_self_of_fresh sys extra hfresh, hfresh]
      simp [isUse_false_of_isOffer extra hoff]
    · simp only [evalCond, find?_append_of_ne sys extra u hu]
      cases hfu : sys.find? u with
      | none => rfl
      | some pu =>
        have hpu_mem : pu ∈ sys.promises := List.mem_of_find?_eq_some hfu
        simp only [runtimeOverlap_append_eq, countP_append_singleton]
        have hx : runtimeOverlap sys S extra pu = none := by
          simp [runtimeOverlap, hunacc pu hpu_mem]
        simp [hx]
  | .accepted o minA => by
    by_cases ho : o = extra.id
    · subst ho
      rw [evalCond, evalCond, find?_append_self_of_fresh sys extra hfresh, hfresh]
      have hne : (extra.promiser == me) = false := by simp [beq_eq_false_iff_ne, hext]
      simp [hne]
    · simp only [evalCond, find?_append_of_ne sys extra o ho]
      cases hfo : sys.find? o with
      | none => rfl
      | some po =>
        simp only [runtimeOverlap_append_eq, countP_append_singleton]
        have hx : runtimeOverlap sys S po extra = none := by
          simp [runtimeOverlap, mayBind_to_offer_false sys po extra hoff]
        simp [hx]
  | .atLeast k cs => by
    simp only [evalCond]
    rw [countSat_unaccepted_offer_inert sys extra α S me hoff hfresh hext hnot_int hunacc cs]
  | .not c => by
    simp only [evalCond]
    rw [evalCond_unaccepted_offer_inert sys extra α S me hoff hfresh hext hnot_int hunacc c]

theorem countSat_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A)
    (hoff     : extra.isOffer = true)
    (hfresh   : sys.find? extra.id = none)
    (hext     : extra.promiser ≠ me)
    (hnot_int : visibleInterior sys.hierarchy sys.agents me extra.promiser = false)
    (hunacc   : ∀ pu ∈ sys.promises, mayBind sys extra pu = false) :
    ∀ (cs : List (Cond P)),
      countSat { sys with promises := sys.promises ++ [extra] } α S me cs =
      countSat sys α S me cs
  | [] => rfl
  | c :: rs => by
    simp only [countSat]
    rw [evalCond_unaccepted_offer_inert sys extra α S me hoff hfresh hext hnot_int hunacc c,
        countSat_unaccepted_offer_inert sys extra α S me hoff hfresh hext hnot_int hunacc rs]
end

theorem buildLocalObs_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A) (obs : List (Obs P))
    (hoff     : extra.isOffer = true)
    (hfresh   : sys.find? extra.id = none)
    (hext     : extra.promiser ≠ me)
    (hnot_int : visibleInterior sys.hierarchy sys.agents me extra.promiser = false)
    (hunacc   : ∀ pu ∈ sys.promises, mayBind sys extra pu = false) :
    buildLocalObs { sys with promises := sys.promises ++ [extra] } α S me obs =
    buildLocalObs sys α S me obs := by
  have hne_beq : (extra.promiser == me) = false := by simp [beq_eq_false_iff_ne, hext]
  have hnotuse : extra.isUse = false := isUse_false_of_isOffer extra hoff
  simp only [buildLocalObs]
  congr 1
  · apply list_filterMap_congr
    intro o _
    cases o with
    | selfPromise q =>
      by_cases hq : q = extra.id
      · subst hq
        dsimp only
        rw [find?_append_self_of_fresh sys extra hfresh, hfresh]
        cases S extra.id <;> simp [hne_beq]
      · simp [find?_append_of_ne sys extra q hq]
    | _ => rfl
  · apply list_flatMap_congr
    intro o _
    cases o with
    | assisted u =>
      by_cases hu : u = extra.id
      · subst hu
        dsimp only
        rw [find?_append_self_of_fresh sys extra hfresh, hfresh]
        cases S extra.id with
        | none => rfl
        | some b => cases b <;> simp [hnotuse]
      · simp only [find?_append_of_ne sys extra u hu]
        cases hfu : sys.find? u with
        | none => simp
        | some pu =>
          have hpu_mem : pu ∈ sys.promises := List.mem_of_find?_eq_some hfu
          cases S u with
          | none => simp
          | some bu =>
            cases bu with
            | offer _ => simp
            | use ub =>
              dsimp only
              split
              · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                           runtimeOverlap_append_eq]
                have hx : runtimeOverlap sys S extra pu = none := by
                  simp [runtimeOverlap, hunacc pu hpu_mem]
                simp [hx]
              · rfl
    | _ => rfl
  · apply list_flatMap_congr
    intro o _
    cases o with
    | accepted oid =>
      by_cases ho : oid = extra.id
      · subst ho
        dsimp only
        rw [find?_append_self_of_fresh sys extra hfresh, hfresh]
        cases S extra.id with
        | none => rfl
        | some b => cases b <;> simp [hne_beq]
      · simp only [find?_append_of_ne sys extra oid ho]
        cases hfo : sys.find? oid with
        | none => simp
        | some po =>
          cases S oid with
          | none => simp
          | some bo =>
            cases bo with
            | use _ => simp
            | offer ob =>
              dsimp only
              split
              · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                           runtimeOverlap_append_eq]
                have hx : runtimeOverlap sys S po extra = none := by
                  simp [runtimeOverlap, mayBind_to_offer_false sys po extra hoff]
                simp [hx]
              · rfl
    | _ => rfl
  · apply list_filterMap_congr
    intro o _
    cases o with
    | interior q =>
      by_cases hq : q = extra.id
      · subst hq
        dsimp only
        rw [find?_append_self_of_fresh sys extra hfresh, hfresh]
        cases S extra.id <;> simp [hnot_int]
      · simp [find?_append_of_ne sys extra q hq]
    | _ => rfl

/-- T4: Axiom of Autonomy — a fresh unaccepted offer/imposition from an external agent
    (not `pr.promiser` and not a directly visible interior sub-agent of `pr.promiser`)
    is 100% unconditionally inert on `quenchStep` (both conditions and value-derived bodies). -/
theorem autonomy_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U)
    (hoff     : extra.isOffer = true)
    (hfresh   : sys.find? extra.id = none)
    (hunacc   : ∀ pu ∈ sys.promises, mayBind sys extra pu = false)
    (pr : Promise A P O U M)
    (hfind    : sys.find? pr.id = some pr)
    (hext     : extra.promiser ≠ pr.promiser)
    (hnot_int : visibleInterior sys.hierarchy sys.agents pr.promiser extra.promiser = false) :
    quenchStep { sys with promises := sys.promises ++ [extra] } α S pr.id =
    quenchStep sys α S pr.id := by
  have hne : pr.id ≠ extra.id := by
    intro heq
    rw [heq] at hfind
    rw [hfresh] at hfind
    cases hfind
  have hfind' := find?_append_of_ne sys extra pr.id hne
  simp only [quenchStep, hfind', hfind]
  rw [evalCond_unaccepted_offer_inert sys extra α S pr.promiser hoff hfresh hext hnot_int hunacc pr.cond]
  cases hsp : pr.body with
  | offer sp =>
    cases sp with
    | fixed o => simp [evalRule, hsp]
    | derived obs produce =>
      simp only [evalRule, hsp]
      rw [buildLocalObs_unaccepted_offer_inert sys extra α S pr.promiser obs hoff hfresh hext hnot_int hunacc]
  | use sp =>
    cases sp with
    | fixed u => simp [evalRule, hsp]
    | derived obs produce =>
      simp only [evalRule, hsp]
      rw [buildLocalObs_unaccepted_offer_inert sys extra α S pr.promiser obs hoff hfresh hext hnot_int hunacc]

end Baugr
