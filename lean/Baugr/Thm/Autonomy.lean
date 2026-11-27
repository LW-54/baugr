/-
  Baugr.Thm.Autonomy — Promise Theory Axiom of Autonomy (T4)
  Adding an unaccepted offer/imposition cannot alter any existing promise's
  condition evaluation, local observation view, or derived body value.
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

private theorem mayBind_append_eq {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (extra po pu : Promise A P O U M) :
    mayBind { sys with promises := sys.promises ++ [extra] } po pu = mayBind sys po pu := rfl

private theorem runtimeOverlap_append_eq {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M) (S : State P O U)
    (po pu : Promise A P O U M) :
    runtimeOverlap { sys with promises := sys.promises ++ [extra] } S po pu =
    runtimeOverlap sys S po pu := rfl

private theorem mayBind_to_offer_false {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (po extra : Promise A P O U M)
    (hoff : extra.isOffer = true) :
    mayBind sys po extra = false := by
  have hnotuse : extra.isUse = false := by
    cases h : extra.spec <;> simp_all [Promise.isOffer, Promise.isUse, BodySpec.isOffer, BodySpec.isUse]
  simp [mayBind, structBindable, hnotuse]

mutual
theorem evalCond_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, mayBind sys extra pu = false) :
    ∀ (c : Cond P),
      (∀ d n, (d, n) ∈ condDeps sys false c → d ≠ extra.id) →
      evalCond { sys with promises := sys.promises ++ [extra] } α S me c =
      evalCond sys α S me c
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
      simp only [runtimeOverlap_append_eq, countP_append_singleton]
      have hx : runtimeOverlap sys S extra pu = none := by
        simp [runtimeOverlap, hunacc pu hpu_mem]
      simp [hx]
  | .accepted o minA, hf => by
    have hne : o ≠ extra.id := by
      apply hf o false; simp only [condDeps]; cases sys.find? o <;> simp
    have hfind := find?_append_of_ne sys extra o hne
    simp only [evalCond, hfind]
    cases hfo : sys.find? o with
    | none => rfl
    | some po =>
      simp only [runtimeOverlap_append_eq, countP_append_singleton]
      have hx : runtimeOverlap sys S po extra = none := by
        simp [runtimeOverlap, mayBind_to_offer_false sys po extra hoff]
      simp [hx]
  | .atLeast k cs, hf => by
    simp only [evalCond]
    rw [countSat_unaccepted_offer_inert sys extra α S me hoff hunacc cs hf]
  | .not c, hf => by
    simp only [evalCond]
    have hf' : ∀ d n, (d, n) ∈ condDeps sys false c → d ≠ extra.id := by
      intro d n hdn
      obtain ⟨m, hm⟩ := (condDeps_neg_flip sys false d c).mp ⟨n, hdn⟩
      exact hf d m hm
    rw [evalCond_unaccepted_offer_inert sys extra α S me hoff hunacc c hf']

theorem countSat_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, mayBind sys extra pu = false) :
    ∀ (cs : List (Cond P)),
      (∀ d n, (d, n) ∈ listCondDeps sys false cs → d ≠ extra.id) →
      countSat { sys with promises := sys.promises ++ [extra] } α S me cs =
      countSat sys α S me cs
  | [], _ => rfl
  | c :: rs, hf => by
    simp only [countSat]
    have h1 := evalCond_unaccepted_offer_inert sys extra α S me hoff hunacc c
      (fun d n hdn => hf d n (List.mem_append_left _ hdn))
    have h2 := countSat_unaccepted_offer_inert sys extra α S me hoff hunacc rs
      (fun d n hdn => hf d n (List.mem_append_right _ hdn))
    rw [h1, h2]
end

theorem buildLocalObs_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U) (me : A) (obs : List (Obs P))
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, mayBind sys extra pu = false)
    (hno_ref : ∀ d n, (d, n) ∈ obsDeps sys obs → d ≠ extra.id) :
    buildLocalObs { sys with promises := sys.promises ++ [extra] } α S me obs =
    buildLocalObs sys α S me obs := by
  have hmem : ∀ o ∈ obs, ∀ d n, (d, n) ∈ obsEntryDeps sys o → d ≠ extra.id := by
    intro o ho d n hdn
    exact hno_ref d n (List.mem_flatMap.mpr ⟨o, ho, hdn⟩)
  simp only [buildLocalObs]
  congr 1
  · apply list_filterMap_congr
    intro o ho
    cases o with
    | selfPromise q =>
      have hfind := find?_append_of_ne sys extra q (hmem _ ho q true (by simp [obsEntryDeps]))
      simp [hfind]
    | _ => rfl
  · apply list_flatMap_congr
    intro o ho
    cases o with
    | assisted u =>
      have hne : u ≠ extra.id := by
        apply hmem _ ho u true; simp only [obsEntryDeps]; cases sys.find? u <;> simp
      have hfind := find?_append_of_ne sys extra u hne
      simp only [hfind]
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
    intro o ho
    cases o with
    | accepted oid =>
      have hne : oid ≠ extra.id := by
        apply hmem _ ho oid true; simp only [obsEntryDeps]; cases sys.find? oid <;> simp
      have hfind := find?_append_of_ne sys extra oid hne
      simp only [hfind]
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
    intro o ho
    cases o with
    | interior q =>
      have hfind := find?_append_of_ne sys extra q (hmem _ ho q true (by simp [obsEntryDeps]))
      simp [hfind]
    | _ => rfl

/-- T4: Axiom of Autonomy — an unaccepted offer/imposition cannot alter any existing promise's
    quenching condition OR value-derived body (`quenchStep` invariance). -/
theorem autonomy_unaccepted_offer_inert {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (extra : Promise A P O U M)
    (α : Assessment A P) (S : State P O U)
    (hoff   : extra.isOffer = true)
    (hunacc : ∀ pu ∈ sys.promises, mayBind sys extra pu = false)
    (pr : Promise A P O U M)
    (hfind  : sys.find? pr.id = some pr)
    (hne    : pr.id ≠ extra.id)
    (hno_ref : ∀ d n, (d, n) ∈ promiseDeps sys pr → d ≠ extra.id) :
    quenchStep { sys with promises := sys.promises ++ [extra] } α S pr.id =
    quenchStep sys α S pr.id := by
  have hfind' := find?_append_of_ne sys extra pr.id hne
  simp only [quenchStep, hfind', hfind]
  have hcond := evalCond_unaccepted_offer_inert sys extra α S pr.promiser hoff hunacc pr.cond
    (fun d n hdn => hno_ref d n (List.mem_append_left _ hdn))
  rw [hcond]
  have hobs_ref : ∀ d n, (d, n) ∈ obsDeps sys pr.spec.obs → d ≠ extra.id :=
    fun d n hdn => hno_ref d n (List.mem_append_right _ hdn)
  cases hsp : pr.spec with
  | fixedOffer o => simp [evalRule, hsp]
  | fixedUse u   => simp [evalRule, hsp]
  | derivedOffer obs produce =>
    simp only [evalRule, hsp]
    simp only [hsp, BodySpec.obs] at hobs_ref
    rw [buildLocalObs_unaccepted_offer_inert sys extra α S pr.promiser obs hoff hunacc hobs_ref]
  | derivedUse obs produce =>
    simp only [evalRule, hsp]
    simp only [hsp, BodySpec.obs] at hobs_ref
    rw [buildLocalObs_unaccepted_offer_inert sys extra α S pr.promiser obs hoff hunacc hobs_ref]

end Baugr
