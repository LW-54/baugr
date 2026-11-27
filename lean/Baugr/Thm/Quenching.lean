/-
  Baugr.Thm.Quenching — Knaster-Tarski Quenching, Cycle Rejection, Locality & Polarity Monotonicity
  Generalized to value-carrying promise states `State P O U = P → Option (Body O U)` (Baugr v0.4).
-/
import Baugr.Promise

namespace Baugr

-- ----------------------------------------------------------------------------
-- Counting, list congruence & lookup utilities
-- ----------------------------------------------------------------------------

theorem countP_mono {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    countP p xs ≤ countP q xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [countP]
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx : (if p x then 1 else 0) ≤ (if q x then 1 else 0) := by
      cases hp : p x with
      | false => simp
      | true => simp [h x List.mem_cons_self hp]
    exact Nat.add_le_add hx hxs

theorem countP_congr {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = q x) : countP p xs = countP q xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countP, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem countP_append_singleton {α : Type} (p : α → Bool) (xs : List α) (extra : α) :
    countP p (xs ++ [extra]) = countP p xs + (if p extra then 1 else 0) := by
  induction xs with
  | nil => simp [countP]
  | cons x xs ih => simp [countP, ih, Nat.add_assoc]

theorem countP_le_length {α : Type} (p : α → Bool) (xs : List α) :
    countP p xs ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [countP, List.length_cons]
    cases p x <;> simp <;> omega

theorem countP_eq_imp_all_eq {α : Type} (p q : α → Bool) (xs : List α)
    (hle : ∀ x ∈ xs, p x = true → q x = true)
    (heq : countP p xs = countP q xs) :
    ∀ x ∈ xs, p x = q x := by
  induction xs with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    simp only [countP] at heq
    have hxs_le := countP_mono p q xs (fun y hy => hle y (List.mem_cons_of_mem x hy))
    have hx_le : (if p x then 1 else 0) ≤ (if q x then 1 else 0) := by
      cases hp : p x with
      | false => simp
      | true => simp [hle x List.mem_cons_self hp]
    have hx_eq : (if p x then 1 else 0) = (if q x then 1 else 0) := by omega
    have hxs_eq : countP p xs = countP q xs := by omega
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · cases hp : p y <;> cases hq : q y <;> simp_all
    · exact ih (fun z hz => hle z (List.mem_cons_of_mem x hz)) hxs_eq y hmem

theorem list_filterMap_congr {α β : Type} (f g : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases g x <;> simp [hxs]

theorem list_flatMap_congr {α β : Type} (f g : α → List β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self,
               ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem mem_dedupList {α : Type} [DecidableEq α] {x : α} :
    ∀ {xs : List α}, x ∈ dedupList xs → x ∈ xs
  | [], h => by simp [dedupList] at h
  | y :: ys, h => by
    simp only [dedupList, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨hmem, _⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem y (mem_dedupList hmem)

theorem find?_id_eq {A P O U M : Type} [DecidableEq P]
    {sys : PromiseSystem A P O U M} {pid : P} {pr : Promise A P O U M}
    (h : sys.find? pid = some pr) : pr.id = pid := by
  have h' : sys.promises.find? (fun y => y.id == pid) = some pr := h
  have hbeq := List.find?_some h'
  exact eq_of_beq hbeq

theorem find?_isSome_of_mem {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U M) (hmem : pr ∈ sys.promises) :
    ∃ x, sys.find? pr.id = some x := by
  cases h : sys.promises.find? (fun y => y.id == pr.id) with
  | some x => exact ⟨x, h⟩
  | none =>
    have hfalse := List.find?_eq_none.mp h pr hmem
    simp at hfalse

theorem find?_eq_some_of_unique {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (huniq : UniqueIds sys)
    (pr : Promise A P O U M) (hmem : pr ∈ sys.promises) :
    sys.find? pr.id = some pr := by
  obtain ⟨x, hx⟩ := find?_isSome_of_mem sys pr hmem
  have hx_mem : x ∈ sys.promises := List.mem_of_find?_eq_some hx
  have hx_id : x.id = pr.id := find?_id_eq hx
  have hEq : x = pr := huniq x hx_mem pr hmem hx_id
  subst hEq
  exact hx

-- ----------------------------------------------------------------------------
-- Flat state order & runtimeOverlap helpers
-- ----------------------------------------------------------------------------

theorem StateLe_isSome {P O U : Type} {S₁ S₂ : State P O U}
    (hle : StateLe S₁ S₂) (p : P) (h : (S₁ p).isSome = true) :
    (S₂ p).isSome = true := by
  cases h1 : S₁ p with
  | none => simp [h1] at h
  | some b =>
    have h2 := hle p b h1
    simp [h2]

theorem StateLe_eq_of_isSome_eq {P O U : Type} {S₁ S₂ : State P O U}
    (hle : StateLe S₁ S₂) (p : P) (heq : (S₁ p).isSome = (S₂ p).isSome) :
    S₁ p = S₂ p := by
  cases h1 : S₁ p with
  | none =>
    cases h2 : S₂ p with
    | none => rfl
    | some _ => simp [h1, h2] at heq
  | some b =>
    exact (hle p b h1).symm

theorem runtimeOverlap_isSome_imp_mayBind {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (S : State P O U) (po pu : Promise A P O U M)
    (h : (runtimeOverlap sys S po pu).isSome = true) :
    mayBind sys po pu = true := by
  simp only [runtimeOverlap] at h
  cases hmb : mayBind sys po pu with
  | false => simp [hmb] at h
  | true => rfl

theorem runtimeOverlap_some_imp_mayBind {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (S : State P O U) (po pu : Promise A P O U M) (m : M)
    (h : runtimeOverlap sys S po pu = some m) :
    mayBind sys po pu = true :=
  runtimeOverlap_isSome_imp_mayBind sys S po pu (by simp [h])

theorem runtimeOverlap_eq_of_eq {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (S₁ S₂ : State P O U) (po pu : Promise A P O U M)
    (ho : S₁ po.id = S₂ po.id) (hu : S₁ pu.id = S₂ pu.id) :
    runtimeOverlap sys S₁ po pu = runtimeOverlap sys S₂ po pu := by
  simp [runtimeOverlap, ho, hu]

-- ----------------------------------------------------------------------------
-- Polarity-indexed dependency lemmas & local evaluation congruence
-- ----------------------------------------------------------------------------

mutual
theorem condDeps_neg_flip {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) (b : Bool) (d : P) :
    ∀ (c : Cond P),
    (∃ n, (d, n) ∈ condDeps sys me b c) ↔ (∃ n, (d, n) ∈ condDeps sys me (!b) c)
  | .selfPromise q => by
    simp only [condDeps]
    cases sys.find? q with
    | none => simp
    | some pq =>
      cases h : (pq.promiser == me) with
      | false => simp [h]
      | true =>
        simp only [h, ↓reduceIte]
        constructor <;> (rintro ⟨n, hm⟩; refine ⟨!n, ?_⟩; simp_all)
  | .assisted u _  => by
    simp only [condDeps]
    cases sys.find? u with
    | none => simp
    | some pu =>
      cases h : (pu.promiser == me && pu.isUse) with
      | false => simp [h]
      | true =>
        simp only [h, ↓reduceIte]
        constructor <;> (rintro ⟨n, hm⟩; refine ⟨!n, ?_⟩; simp_all)
  | .accepted o _  => by
    simp only [condDeps]
    cases sys.find? o with
    | none => simp
    | some po =>
      cases h : (po.promiser == me && po.isOffer) with
      | false => simp [h]
      | true =>
        simp only [h, ↓reduceIte]
        constructor <;> (rintro ⟨n, hm⟩; refine ⟨!n, ?_⟩; simp_all)
  | .interior q    => by
    simp only [condDeps]
    cases sys.find? q with
    | none => simp
    | some pq =>
      cases h : visibleInterior sys.hierarchy sys.agents me pq.promiser with
      | false => simp [h]
      | true =>
        simp only [h, ↓reduceIte]
        constructor <;> (rintro ⟨n, hm⟩; refine ⟨!n, ?_⟩; simp_all)
  | .atLeast _ cs  => listCondDeps_neg_flip sys me b d cs
  | .not c         => by
    simp only [condDeps, Bool.not_not]
    exact (condDeps_neg_flip sys me b d c).symm

theorem listCondDeps_neg_flip {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) (b : Bool) (d : P) :
    ∀ (cs : List (Cond P)),
    (∃ n, (d, n) ∈ listCondDeps sys me b cs) ↔ (∃ n, (d, n) ∈ listCondDeps sys me (!b) cs)
  | [] => by simp [listCondDeps]
  | c :: rs => by
    simp only [listCondDeps, List.mem_append]
    constructor
    · rintro ⟨n, h1 | h2⟩
      · obtain ⟨m, hm⟩ := (condDeps_neg_flip sys me b d c).mp ⟨n, h1⟩; exact ⟨m, Or.inl hm⟩
      · obtain ⟨m, hm⟩ := (listCondDeps_neg_flip sys me b d rs).mp ⟨n, h2⟩; exact ⟨m, Or.inr hm⟩
    · rintro ⟨n, h1 | h2⟩
      · obtain ⟨m, hm⟩ := (condDeps_neg_flip sys me b d c).mpr ⟨n, h1⟩; exact ⟨m, Or.inl hm⟩
      · obtain ⟨m, hm⟩ := (listCondDeps_neg_flip sys me b d rs).mpr ⟨n, h2⟩; exact ⟨m, Or.inr hm⟩
end

mutual
theorem evalCond_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) :
    ∀ (c : Cond P),
      (∀ d n, (d, n) ∈ condDeps sys me false c → (∃ x, sys.find? d = some x) →
        S₁ d = S₂ d ∧ α₁ me d = α₂ me d) →
      evalCond sys α₁ S₁ me c = evalCond sys α₂ S₂ me c
  | .selfPromise q, hagree => by
    simp only [evalCond]
    cases hfq : sys.find? q with
    | none => rfl
    | some pq =>
      cases hpr : (pq.promiser == me) with
      | false => simp [hpr]
      | true =>
        have hq := hagree q false (by simp [condDeps, hfq, hpr]) ⟨pq, hfq⟩
        simp [hpr, hq.1, hq.2]
  | .interior q, hagree => by
    simp only [evalCond]
    cases hfq : sys.find? q with
    | none => rfl
    | some pq =>
      cases hvi : visibleInterior sys.hierarchy sys.agents me pq.promiser with
      | false => simp [hvi]
      | true =>
        have hq := hagree q false (by simp [condDeps, hfq, hvi]) ⟨pq, hfq⟩
        simp [hvi, hq.1, hq.2]
  | .assisted u minP, hagree => by
    simp only [evalCond]
    cases hfu : sys.find? u with
    | none => rfl
    | some pu =>
      cases hown : (pu.promiser == me && pu.isUse) with
      | false =>
        have h1 : (pu.promiser == me && pu.isUse && (S₁ u).isSome && α₁ me u) = false := by
          simp [hown]
        have h2 : (pu.promiser == me && pu.isUse && (S₂ u).isSome && α₂ me u) = false := by
          simp [hown]
        simp [h1, h2]
      | true =>
        have hu := hagree u false (by simp [condDeps, hfu, hown]) ⟨pu, hfu⟩
        have huid : pu.id = u := find?_id_eq hfu
        simp only [hu.1, hu.2]
        split
        · suffices countP (fun po => (runtimeOverlap sys S₁ po pu).isSome && α₁ me po.id) sys.promises =
                   countP (fun po => (runtimeOverlap sys S₂ po pu).isSome && α₂ me po.id) sys.promises by
            rw [this]
          apply countP_congr
          intro po hpo_mem
          cases hmb : mayBind sys po pu with
          | false => simp [runtimeOverlap, hmb]
          | true =>
            have hdep : (po.id, false) ∈ condDeps sys me false (.assisted u minP) := by
              simp only [condDeps, hfu, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
              right; exact ⟨po, ⟨hpo_mem, hmb⟩, rfl⟩
            have hpo := hagree po.id false hdep (find?_isSome_of_mem sys po hpo_mem)
            have hru : runtimeOverlap sys S₁ po pu = runtimeOverlap sys S₂ po pu :=
              runtimeOverlap_eq_of_eq sys S₁ S₂ po pu hpo.1 (by rw [huid]; exact hu.1)
            simp [hru, hpo.2]
        · rfl
  | .accepted o minA, hagree => by
    simp only [evalCond]
    cases hfo : sys.find? o with
    | none => rfl
    | some po =>
      cases hown : (po.promiser == me && po.isOffer) with
      | false =>
        have h1 : (po.promiser == me && po.isOffer && (S₁ o).isSome && α₁ me o) = false := by
          simp [hown]
        have h2 : (po.promiser == me && po.isOffer && (S₂ o).isSome && α₂ me o) = false := by
          simp [hown]
        simp [h1, h2]
      | true =>
        have ho := hagree o false (by simp [condDeps, hfo, hown]) ⟨po, hfo⟩
        have hoid : po.id = o := find?_id_eq hfo
        simp only [ho.1, ho.2]
        split
        · suffices countP (fun pu => (runtimeOverlap sys S₁ po pu).isSome && inScope pu me && α₁ me pu.id) sys.promises =
                   countP (fun pu => (runtimeOverlap sys S₂ po pu).isSome && inScope pu me && α₂ me pu.id) sys.promises by
            rw [this]
          apply countP_congr
          intro pu hpu_mem
          cases hmb : mayBind sys po pu with
          | false => simp [runtimeOverlap, hmb]
          | true =>
            cases hsc : inScope pu me with
            | false => simp
            | true =>
              have hdep : (pu.id, false) ∈ condDeps sys me false (.accepted o minA) := by
                simp only [condDeps, hfo, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
                right; exact ⟨pu, ⟨hpu_mem, by simp [hmb, hsc]⟩, rfl⟩
              have hpu := hagree pu.id false hdep (find?_isSome_of_mem sys pu hpu_mem)
              have hru : runtimeOverlap sys S₁ po pu = runtimeOverlap sys S₂ po pu :=
                runtimeOverlap_eq_of_eq sys S₁ S₂ po pu (by rw [hoid]; exact ho.1) hpu.1
              simp [hru, hpu.2]
        · rfl
  | .atLeast k cs, hagree => by
    simp only [evalCond]
    rw [countSat_local sys α₁ α₂ S₁ S₂ me cs hagree]
  | .not c, hagree => by
    simp only [evalCond]
    have hsub : ∀ d n, (d, n) ∈ condDeps sys me false c → (∃ x, sys.find? d = some x) →
        S₁ d = S₂ d ∧ α₁ me d = α₂ me d := by
      intro d n hdn hex
      obtain ⟨m, hm⟩ := (condDeps_neg_flip sys me false d c).mp ⟨n, hdn⟩
      exact hagree d m hm hex
    rw [evalCond_local sys α₁ α₂ S₁ S₂ me c hsub]

theorem countSat_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) :
    ∀ (cs : List (Cond P)),
      (∀ d n, (d, n) ∈ listCondDeps sys me false cs → (∃ x, sys.find? d = some x) →
        S₁ d = S₂ d ∧ α₁ me d = α₂ me d) →
      countSat sys α₁ S₁ me cs = countSat sys α₂ S₂ me cs
  | [], _ => rfl
  | c :: rs, hagree => by
    simp only [countSat]
    have h1 := evalCond_local sys α₁ α₂ S₁ S₂ me c
      (fun d n hdn hex => hagree d n (List.mem_append_left _ hdn) hex)
    have h2 := countSat_local sys α₁ α₂ S₁ S₂ me rs
      (fun d n hdn hex => hagree d n (List.mem_append_right _ hdn) hex)
    rw [h1, h2]
end

theorem buildLocalObs_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) (obs : List (Obs P))
    (hagree : ∀ d n, (d, n) ∈ obsDeps sys me obs → (∃ x, sys.find? d = some x) →
      S₁ d = S₂ d ∧ α₁ me d = α₂ me d) :
    buildLocalObs sys α₁ S₁ me obs = buildLocalObs sys α₂ S₂ me obs := by
  have hmem_obs : ∀ o ∈ dedupList obs, ∀ d n, (d, n) ∈ obsEntryDeps sys me o →
      (∃ x, sys.find? d = some x) → S₁ d = S₂ d ∧ α₁ me d = α₂ me d := by
    intro o ho d n hdn hex
    exact hagree d n (List.mem_flatMap.mpr ⟨o, mem_dedupList ho, hdn⟩) hex
  simp only [buildLocalObs]
  congr 1
  · apply list_filterMap_congr
    intro o ho
    cases o with
    | selfPromise q =>
      cases hfq : sys.find? q with
      | none => simp [hfq]
      | some pq =>
        cases hpr : (pq.promiser == me) with
        | false =>
          cases h1 : S₁ q <;> cases h2 : S₂ q <;> simp [hfq, h1, h2, hpr]
        | true =>
          have hq := hmem_obs _ ho q true (by simp [obsEntryDeps, hfq, hpr]) ⟨pq, hfq⟩
          simp [hfq, hq.1, hq.2]
    | _ => rfl
  · apply list_flatMap_congr
    intro o ho
    cases o with
    | assisted u =>
      cases hfu : sys.find? u with
      | none => simp [hfu]
      | some pu =>
        cases hown : (pu.promiser == me && pu.isUse) with
        | false =>
          simp only [hfu]
          cases S₁ u with
          | none =>
            cases S₂ u with
            | none => rfl
            | some bu => cases bu <;> simp [hown]
          | some bu1 =>
            cases bu1 with
            | offer _ =>
              cases S₂ u with
              | none => rfl
              | some bu2 => cases bu2 <;> simp [hown]
            | use _ =>
              cases S₂ u with
              | none => simp [hown]
              | some bu2 => cases bu2 <;> simp [hown]
        | true =>
          have hu := hmem_obs _ ho u true (by simp [obsEntryDeps, hfu, hown]) ⟨pu, hfu⟩
          have huid : pu.id = u := find?_id_eq hfu
          simp only [hfu, hu.1, hu.2]
          cases hsu : S₂ u with
          | none => simp
          | some bu =>
            cases bu with
            | offer _ => simp
            | use ub =>
              dsimp only
              split
              · apply list_filterMap_congr
                intro po hpo_mem
                cases hmb : mayBind sys po pu with
                | false => simp [runtimeOverlap, hmb]
                | true =>
                  have hdep : (po.id, true) ∈ obsEntryDeps sys me (.assisted u) := by
                    simp only [obsEntryDeps, hfu, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
                    right; exact ⟨po, ⟨hpo_mem, hmb⟩, rfl⟩
                  have hpo := hmem_obs _ ho po.id true hdep (find?_isSome_of_mem sys po hpo_mem)
                  have hru : runtimeOverlap sys S₁ po pu = runtimeOverlap sys S₂ po pu :=
                    runtimeOverlap_eq_of_eq sys S₁ S₂ po pu hpo.1 (by rw [huid]; exact hu.1)
                  simp [hru, hpo.1, hpo.2]
              · rfl
    | _ => rfl
  · apply list_flatMap_congr
    intro o ho
    cases o with
    | accepted oid =>
      cases hfo : sys.find? oid with
      | none => simp [hfo]
      | some po =>
        cases hown : (po.promiser == me && po.isOffer) with
        | false =>
          simp only [hfo]
          cases S₁ oid with
          | none =>
            cases S₂ oid with
            | none => rfl
            | some bo => cases bo <;> simp [hown]
          | some bo1 =>
            cases bo1 with
            | use _ =>
              cases S₂ oid with
              | none => rfl
              | some bo2 => cases bo2 <;> simp [hown]
            | offer _ =>
              cases S₂ oid with
              | none => simp [hown]
              | some bo2 => cases bo2 <;> simp [hown]
        | true =>
          have ho_eq := hmem_obs _ ho oid true (by simp [obsEntryDeps, hfo, hown]) ⟨po, hfo⟩
          have hoid : po.id = oid := find?_id_eq hfo
          simp only [hfo, ho_eq.1, ho_eq.2]
          cases hso : S₂ oid with
          | none => simp
          | some bo =>
            cases bo with
            | use _ => simp
            | offer ob =>
              dsimp only
              split
              · apply list_filterMap_congr
                intro pu hpu_mem
                cases hmb : mayBind sys po pu with
                | false => simp [runtimeOverlap, hmb]
                | true =>
                  cases hsc : inScope pu me with
                  | false =>
                    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                    split <;> split <;> rfl
                  | true =>
                    have hdep : (pu.id, true) ∈ obsEntryDeps sys me (.accepted oid) := by
                      simp only [obsEntryDeps, hfo, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
                      right; exact ⟨pu, ⟨hpu_mem, by simp [hmb, hsc]⟩, rfl⟩
                    have hpu := hmem_obs _ ho pu.id true hdep (find?_isSome_of_mem sys pu hpu_mem)
                    have hru : runtimeOverlap sys S₁ po pu = runtimeOverlap sys S₂ po pu :=
                      runtimeOverlap_eq_of_eq sys S₁ S₂ po pu (by rw [hoid]; exact ho_eq.1) hpu.1
                    simp [hru, hpu.1, hpu.2]
              · rfl
    | _ => rfl
  · apply list_filterMap_congr
    intro o ho
    cases o with
    | interior q =>
      cases hfq : sys.find? q with
      | none => simp [hfq]
      | some pq =>
        cases hvi : visibleInterior sys.hierarchy sys.agents me pq.promiser with
        | false =>
          cases h1 : S₁ q <;> cases h2 : S₂ q <;> simp [hfq, h1, h2, hvi]
        | true =>
          have hq := hmem_obs _ ho q true (by simp [obsEntryDeps, hfq, hvi]) ⟨pq, hfq⟩
          simp [hfq, hq.1, hq.2]
    | _ => rfl

theorem evalRule_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (S₁ S₂ : State P O U) (pr : Promise A P O U M)
    (hagree : ∀ d n, (d, n) ∈ obsDeps sys pr.promiser pr.obs → (∃ x, sys.find? d = some x) →
      S₁ d = S₂ d ∧ α₁ pr.promiser d = α₂ pr.promiser d) :
    evalRule sys α₁ S₁ pr = evalRule sys α₂ S₂ pr := by
  cases hsp : pr.body with
  | offer sp =>
    cases sp with
    | fixed o => simp [evalRule, hsp]
    | derived obs produce =>
      simp only [evalRule, hsp]
      simp only [hsp, Promise.obs, Spec.obs] at hagree
      rw [buildLocalObs_local sys α₁ α₂ S₁ S₂ pr.promiser obs hagree]
  | use sp =>
    cases sp with
    | fixed u => simp [evalRule, hsp]
    | derived obs produce =>
      simp only [evalRule, hsp]
      simp only [hsp, Promise.obs, Spec.obs] at hagree
      rw [buildLocalObs_local sys α₁ α₂ S₁ S₂ pr.promiser obs hagree]

theorem quenchStep_ext_promises {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (S₁ S₂ : State P O U)
    (heq : ∀ pr ∈ sys.promises, S₁ pr.id = S₂ pr.id) :
    quenchStep sys α S₁ = quenchStep sys α S₂ := by
  funext pid
  simp only [quenchStep]
  cases hfind : sys.find? pid with
  | none => rfl
  | some pr =>
    have hagree_all : ∀ d, (∃ x, sys.find? d = some x) → S₁ d = S₂ d := by
      intro d ⟨x, hx⟩
      have hx_mem : x ∈ sys.promises := List.mem_of_find?_eq_some hx
      have hx_id : x.id = d := find?_id_eq hx
      rw [← hx_id]
      exact heq x hx_mem
    have hc := evalCond_local sys α α S₁ S₂ pr.promiser pr.cond
      (fun d _ _ hex => ⟨hagree_all d hex, rfl⟩)
    have hr := evalRule_local sys α α S₁ S₂ pr
      (fun d _ _ hex => ⟨hagree_all d hex, rfl⟩)
    simp only [hc, hr]

-- ----------------------------------------------------------------------------
-- Polarity-indexed monotonicity (handles arbitrary nested `Not` within strata!)
-- ----------------------------------------------------------------------------

/-- Order on `Option (Body O U)` indexed by negation parity (`false` = monotone, `true` = antitone). -/
def StateLePol {O U : Type} (neg : Bool) (a b : Option (Body O U)) : Prop :=
  if neg then (∀ x, b = some x → a = some x) else (∀ x, a = some x → b = some x)

theorem StateLePol_isSome {O U : Type} {neg : Bool} {a b : Option (Body O U)}
    (h : StateLePol neg a b) :
    if neg then (b.isSome = true → a.isSome = true) else (a.isSome = true → b.isSome = true) := by
  cases neg with
  | false =>
    simp only [StateLePol, Bool.false_eq_true, ↓reduceIte] at h ⊢
    intro ha
    cases ha_eq : a with
    | none => simp [ha_eq] at ha
    | some x => simp [h x ha_eq]
  | true =>
    simp only [StateLePol, ↓reduceIte] at h ⊢
    intro hb
    cases hb_eq : b with
    | none => simp [hb_eq] at hb
    | some x => simp [h x hb_eq]

/-- Order on Bool indexed by negation parity. -/
def BoolLePol (neg : Bool) (a b : Bool) : Prop :=
  if neg then (b = true → a = true) else (a = true → b = true)

theorem BoolLePol_not (neg a b : Bool) (h : BoolLePol (!neg) a b) :
    BoolLePol neg (!a) (!b) := by
  cases neg <;> cases a <;> cases b <;> simp_all [BoolLePol]

mutual
/-- Polarity-indexed monotonicity of `evalCond` under arbitrary nested `Not` over value states. -/
theorem evalCond_mono_pol {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) :
    ∀ (neg : Bool) (c : Cond P),
      (∀ d b, (d, b) ∈ condDeps sys me neg c → StateLePol b (S₁ d) (S₂ d)) →
      BoolLePol neg (evalCond sys α S₁ me c) (evalCond sys α S₂ me c)
  | neg, .selfPromise q, hdep => by
    cases hfind : sys.find? q with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfind]
    | some pq =>
      cases hpr : (pq.promiser == me) with
      | false => cases neg <;> simp [BoolLePol, evalCond, hfind, hpr]
      | true =>
        have hq := StateLePol_isSome (hdep q neg (by simp [condDeps, hfind, hpr]))
        cases neg <;> simp only [BoolLePol, evalCond, hfind, hpr, Bool.true_and] at hq ⊢
        · simp only [Bool.and_eq_true]; intro h; exact ⟨hq h.1, h.2⟩
        · simp only [Bool.and_eq_true]; intro h; exact ⟨hq h.1, h.2⟩
  | neg, .interior q, hdep => by
    cases hfind : sys.find? q with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfind]
    | some pq =>
      cases hvi : visibleInterior sys.hierarchy sys.agents me pq.promiser with
      | false => cases neg <;> simp [BoolLePol, evalCond, hfind, hvi]
      | true =>
        have hq := StateLePol_isSome (hdep q neg (by simp [condDeps, hfind, hvi]))
        cases neg <;> simp only [BoolLePol, evalCond, hfind, hvi, Bool.true_and] at hq ⊢
        · simp only [Bool.and_eq_true]; intro h; exact ⟨hq h.1, h.2⟩
        · simp only [Bool.and_eq_true]; intro h; exact ⟨hq h.1, h.2⟩
  | neg, .assisted u minP, hdep => by
    cases hfu : sys.find? u with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfu]
    | some pu =>
      cases hown : (pu.promiser == me && pu.isUse) with
      | false =>
        have h1 : (pu.promiser == me && pu.isUse && (S₁ u).isSome && α me u) = false := by simp [hown]
        have h2 : (pu.promiser == me && pu.isUse && (S₂ u).isSome && α me u) = false := by simp [hown]
        cases neg <;> simp [BoolLePol, evalCond, hfu, h1, h2]
      | true =>
        have hu := hdep u neg (by simp [condDeps, hfu, hown])
        have hu_some := StateLePol_isSome hu
        have huid : pu.id = u := find?_id_eq hfu
        have hpo : ∀ po ∈ sys.promises, mayBind sys po pu = true →
            StateLePol neg (S₁ po.id) (S₂ po.id) := by
          intro po hmem hmb
          apply hdep po.id neg
          simp only [condDeps, hfu, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
          right; exact ⟨po, ⟨hmem, hmb⟩, rfl⟩
        cases neg <;> simp only [BoolLePol, evalCond, hfu] at hu hu_some ⊢
        · intro h
          split at h
          · next hcond =>
            simp only [Bool.and_eq_true] at hcond
            have hcond2 : (pu.promiser == me && pu.isUse && (S₂ u).isSome && α me u) = true := by
              simp [hcond.1.1.1, hcond.1.1.2, hu_some hcond.1.2, hcond.2]
            simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
            exact Nat.le_trans h (countP_mono _ _ sys.promises fun po hmem hp => by
              simp only [Bool.and_eq_true] at hp ⊢
              refine ⟨?_, hp.2⟩
              have hmb := runtimeOverlap_isSome_imp_mayBind sys S₁ po pu hp.1
              have hpol := hpo po hmem hmb
              simp only [StateLePol, Bool.false_eq_true, ↓reduceIte] at hpol hu
              simp only [runtimeOverlap, hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp ⊢
              cases hso : S₁ po.id with
              | none => simp [hso] at hp
              | some bo =>
                cases bo with
                | use _ => simp [hso] at hp
                | offer ob =>
                  cases hsu : S₁ pu.id with
                  | none => simp [hso, hsu] at hp
                  | some bu =>
                    cases bu with
                    | offer _ => simp [hso, hsu] at hp
                    | use ub =>
                      have hso2 := hpol _ hso
                      have hsu2 : S₂ pu.id = some (.use ub) := by
                        rw [huid] at hsu ⊢; exact hu _ hsu
                      simp only [hso, hsu] at hp
                      simp [hso2, hsu2, hp.1])
          · simp at h
        · intro h
          split at h
          · next hcond =>
            simp only [Bool.and_eq_true] at hcond
            have hcond1 : (pu.promiser == me && pu.isUse && (S₁ u).isSome && α me u) = true := by
              simp [hcond.1.1.1, hcond.1.1.2, hu_some hcond.1.2, hcond.2]
            simp only [hcond1, ↓reduceIte, decide_eq_true_eq] at h ⊢
            exact Nat.le_trans h (countP_mono _ _ sys.promises fun po hmem hp => by
              simp only [Bool.and_eq_true] at hp ⊢
              refine ⟨?_, hp.2⟩
              have hmb := runtimeOverlap_isSome_imp_mayBind sys S₂ po pu hp.1
              have hpol := hpo po hmem hmb
              simp only [StateLePol, ↓reduceIte] at hpol hu
              simp only [runtimeOverlap, hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp ⊢
              cases hso : S₂ po.id with
              | none => simp [hso] at hp
              | some bo =>
                cases bo with
                | use _ => simp [hso] at hp
                | offer ob =>
                  cases hsu : S₂ pu.id with
                  | none => simp [hso, hsu] at hp
                  | some bu =>
                    cases bu with
                    | offer _ => simp [hso, hsu] at hp
                    | use ub =>
                      have hso1 := hpol _ hso
                      have hsu1 : S₁ pu.id = some (.use ub) := by
                        rw [huid] at hsu ⊢; exact hu _ hsu
                      simp only [hso, hsu] at hp
                      simp [hso1, hsu1, hp.1])
          · simp at h
  | neg, .accepted o minA, hdep => by
    cases hfo : sys.find? o with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfo]
    | some po =>
      cases hown : (po.promiser == me && po.isOffer) with
      | false =>
        have h1 : (po.promiser == me && po.isOffer && (S₁ o).isSome && α me o) = false := by simp [hown]
        have h2 : (po.promiser == me && po.isOffer && (S₂ o).isSome && α me o) = false := by simp [hown]
        cases neg <;> simp [BoolLePol, evalCond, hfo, h1, h2]
      | true =>
        have ho := hdep o neg (by simp [condDeps, hfo, hown])
        have ho_some := StateLePol_isSome ho
        have hoid : po.id = o := find?_id_eq hfo
        have hpu : ∀ pu ∈ sys.promises, mayBind sys po pu = true →
            inScope pu me = true → StateLePol neg (S₁ pu.id) (S₂ pu.id) := by
          intro pu hmem hmb hsc
          apply hdep pu.id neg
          simp only [condDeps, hfo, hown, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter]
          right; exact ⟨pu, ⟨hmem, by simp [hmb, hsc]⟩, rfl⟩
        cases neg <;> simp only [BoolLePol, evalCond, hfo] at ho ho_some ⊢
        · intro h
          split at h
          · next hcond =>
            simp only [Bool.and_eq_true] at hcond
            have hcond2 : (po.promiser == me && po.isOffer && (S₂ o).isSome && α me o) = true := by
              simp [hcond.1.1.1, hcond.1.1.2, ho_some hcond.1.2, hcond.2]
            simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
            exact Nat.le_trans h (countP_mono _ _ sys.promises fun pu hmem hp => by
              simp only [Bool.and_eq_true] at hp ⊢
              refine ⟨⟨?_, hp.1.2⟩, hp.2⟩
              have hmb := runtimeOverlap_isSome_imp_mayBind sys S₁ po pu hp.1.1
              have hpol := hpu pu hmem hmb hp.1.2
              simp only [StateLePol, Bool.false_eq_true, ↓reduceIte] at hpol ho
              simp only [runtimeOverlap, hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp ⊢
              cases hso : S₁ po.id with
              | none => simp [hso] at hp
              | some bo =>
                cases bo with
                | use _ => simp [hso] at hp
                | offer ob =>
                  cases hsu : S₁ pu.id with
                  | none => simp [hso, hsu] at hp
                  | some bu =>
                    cases bu with
                    | offer _ => simp [hso, hsu] at hp
                    | use ub =>
                      have hso2 : S₂ po.id = some (.offer ob) := by
                        rw [hoid] at hso ⊢; exact ho _ hso
                      have hsu2 := hpol _ hsu
                      simp only [hso, hsu] at hp
                      simp [hso2, hsu2, hp.1.1])
          · simp at h
        · intro h
          split at h
          · next hcond =>
            simp only [Bool.and_eq_true] at hcond
            have hcond1 : (po.promiser == me && po.isOffer && (S₁ o).isSome && α me o) = true := by
              simp [hcond.1.1.1, hcond.1.1.2, ho_some hcond.1.2, hcond.2]
            simp only [hcond1, ↓reduceIte, decide_eq_true_eq] at h ⊢
            exact Nat.le_trans h (countP_mono _ _ sys.promises fun pu hmem hp => by
              simp only [Bool.and_eq_true] at hp ⊢
              refine ⟨⟨?_, hp.1.2⟩, hp.2⟩
              have hmb := runtimeOverlap_isSome_imp_mayBind sys S₂ po pu hp.1.1
              have hpol := hpu pu hmem hmb hp.1.2
              simp only [StateLePol, ↓reduceIte] at hpol ho
              simp only [runtimeOverlap, hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp ⊢
              cases hso : S₂ po.id with
              | none => simp [hso] at hp
              | some bo =>
                cases bo with
                | use _ => simp [hso] at hp
                | offer ob =>
                  cases hsu : S₂ pu.id with
                  | none => simp [hso, hsu] at hp
                  | some bu =>
                    cases bu with
                    | offer _ => simp [hso, hsu] at hp
                    | use ub =>
                      have hso1 : S₁ po.id = some (.offer ob) := by
                        rw [hoid] at hso ⊢; exact ho _ hso
                      have hsu1 := hpol _ hsu
                      simp only [hso, hsu] at hp
                      simp [hso1, hsu1, hp.1.1])
          · simp at h
  | neg, .atLeast k cs, hdep => by
    have hcs := countSat_mono_pol sys α S₁ S₂ me neg cs hdep
    cases neg <;> simp only [BoolLePol, evalCond, decide_eq_true_eq] at hcs ⊢ <;>
      exact fun h => Nat.le_trans h hcs
  | neg, .not c, hdep => by
    simp only [evalCond]
    exact BoolLePol_not neg _ _ (evalCond_mono_pol sys α S₁ S₂ me (!neg) c hdep)

theorem countSat_mono_pol {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) :
    ∀ (neg : Bool) (cs : List (Cond P)),
      (∀ d b, (d, b) ∈ listCondDeps sys me neg cs → StateLePol b (S₁ d) (S₂ d)) →
      (if neg then countSat sys α S₂ me cs ≤ countSat sys α S₁ me cs
              else countSat sys α S₁ me cs ≤ countSat sys α S₂ me cs)
  | neg, [], _ => by cases neg <;> exact Nat.le_refl 0
  | neg, c :: rs, hdep => by
    have hc := evalCond_mono_pol sys α S₁ S₂ me neg c
      (fun d b h => hdep d b (List.mem_append_left _ h))
    have hrs := countSat_mono_pol sys α S₁ S₂ me neg rs
      (fun d b h => hdep d b (List.mem_append_right _ h))
    cases neg <;> simp only [BoolLePol, countSat] at hc hrs ⊢
    · have h1 : (if evalCond sys α S₁ me c then 1 else 0) ≤
                (if evalCond sys α S₂ me c then 1 else 0) := by
        cases h : evalCond sys α S₁ me c with
        | false => simp
        | true => simp [hc h]
      exact Nat.add_le_add h1 hrs
    · have h1 : (if evalCond sys α S₂ me c then 1 else 0) ≤
                (if evalCond sys α S₁ me c then 1 else 0) := by
        cases h : evalCond sys α S₂ me c with
        | false => simp
        | true => simp [hc h]
      exact Nat.add_le_add h1 hrs
end

-- ----------------------------------------------------------------------------
-- T1–T3: Positive Knaster-Tarski Quenching & Cycle Rejection
-- ----------------------------------------------------------------------------

mutual
theorem condDeps_positive_only {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) :
    ∀ (c : Cond P), c.isPositive → ∀ d b, (d, b) ∈ condDeps sys me false c → b = false
  | .selfPromise q, _, _, _, h => by
    simp only [condDeps] at h
    cases hfq : sys.find? q with
    | none => simp [hfq] at h
    | some pq =>
      simp only [hfq] at h
      split at h
      · simp at h; exact h.2
      · simp at h
  | .interior q, _, _, _, h => by
    simp only [condDeps] at h
    cases hfq : sys.find? q with
    | none => simp [hfq] at h
    | some pq =>
      simp only [hfq] at h
      split at h
      · simp at h; exact h.2
      · simp at h
  | .assisted u _, _, _, _, h => by
    simp only [condDeps] at h
    cases hfu : sys.find? u with
    | none => simp [hfu] at h
    | some pu =>
      simp only [hfu] at h
      split at h
      · simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at h
        rcases h with ⟨_, hb⟩ | ⟨po, _, _, hb⟩ <;> simp_all
      · simp at h
  | .accepted o _, _, _, _, h => by
    simp only [condDeps] at h
    cases hfo : sys.find? o with
    | none => simp [hfo] at h
    | some po =>
      simp only [hfo] at h
      split at h
      · simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at h
        rcases h with ⟨_, hb⟩ | ⟨pu, _, _, hb⟩ <;> simp_all
      · simp at h
  | .atLeast _ cs, hpos, d, b, h => listCondDeps_positive_only sys me cs hpos d b h
  | .not _,        hpos, _, _, _ => False.elim hpos

theorem listCondDeps_positive_only {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (me : A) :
    ∀ (cs : List (Cond P)), Cond.listPositive cs →
      ∀ d b, (d, b) ∈ listCondDeps sys me false cs → b = false
  | [], _, _, _, h => by simp [listCondDeps] at h
  | c :: rs, ⟨hc, hrs⟩, d, b, h => by
    simp only [listCondDeps, List.mem_append] at h
    rcases h with h1 | h2
    · exact condDeps_positive_only sys me c hc d b h1
    · exact listCondDeps_positive_only sys me rs hrs d b h2
end

/-- T1a: Monotonicity of positive condition evaluation in state `S`. -/
theorem evalCond_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (S₁ S₂ : State P O U) (me : A) (c : Cond P)
    (hpos : c.isPositive) (hsub : StateLe S₁ S₂) :
    evalCond sys α S₁ me c = true → evalCond sys α S₂ me c = true :=
  evalCond_mono_pol sys α S₁ S₂ me false c fun d b h => by
    have hb := condDeps_positive_only sys me c hpos d b h
    subst hb
    exact hsub d

/-- T1a: Monotonicity of one-step quenching operator T(S) on positive systems. -/
theorem quenchStep_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (S₁ S₂ : State P O U) (hsub : StateLe S₁ S₂) :
    StateLe (quenchStep sys α S₁) (quenchStep sys α S₂) := by
  intro pid b h
  simp only [quenchStep] at h ⊢
  cases hfind : sys.find? pid with
  | none => simp [hfind] at h
  | some pr =>
    simp only [hfind] at h ⊢
    have hpr := hpos pr (List.mem_of_find?_eq_some hfind)
    split at h
    · next hc1 =>
      have hc2 := evalCond_mono sys α S₁ S₂ pr.promiser pr.cond hpr.1 hsub hc1
      simp only [hc2, ↓reduceIte]
      have hr : evalRule sys α S₁ pr = evalRule sys α S₂ pr :=
        evalRule_local sys α α S₁ S₂ pr (fun d n hd _ => by simp [obsDeps, hpr.2] at hd)
      rwa [← hr]
    · cases h

/-- T1b: Knaster-Tarski leastness — every iterate is bounded by any pre-fixed point. -/
theorem quenchIter_le_any_prefixed {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (F : State P O U) (hpre : StateLe (quenchStep sys α F) F) (n : Nat) :
    StateLe (quenchIter sys α n) F := by
  induction n with
  | zero => intro _ _ h; simp [quenchIter] at h
  | succ k ih =>
    intro p b hp
    exact hpre p b (quenchStep_mono sys α hpos _ _ ih p b hp)

/-- T1c: Ascending chain property: `quenchIter n ≤ quenchIter (n + 1)`. -/
theorem quenchIter_chain {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys) (n : Nat) :
    StateLe (quenchIter sys α n) (quenchIter sys α (n + 1)) := by
  induction n with
  | zero => intro _ _ h; simp [quenchIter] at h
  | succ k ih => exact quenchStep_mono sys α hpos _ _ ih

/-- T2: Cyclic self-dependent conditionals NEVER quench in the least fixed point. -/
theorem cyclic_conditional_never_quenches {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (C : P → Bool)
    (hclosed : ∀ p, C p = true →
      quenchStep sys α (fun q =>
        if C q then none else match sys.find? q with
          | some pr => evalRule sys α (fun _ => none) pr
          | none    => none) p = none) :
    ∀ n p, C p = true → quenchIter sys α n p = none := by
  let F : State P O U := fun q =>
    if C q then none else match sys.find? q with
      | some pr => evalRule sys α (fun _ => none) pr
      | none    => none
  have hpre : StateLe (quenchStep sys α F) F := by
    intro p b hp
    cases hc : C p with
    | true =>
      have hf := hclosed p hc
      rw [hf] at hp
      cases hp
    | false =>
      simp only [F, hc, Bool.false_eq_true, ↓reduceIte]
      simp only [quenchStep] at hp
      cases hfind : sys.find? p with
      | none => simp [hfind] at hp
      | some pr =>
        simp only [hfind] at hp ⊢
        have hpr := hpos pr (List.mem_of_find?_eq_some hfind)
        split at hp
        · have hr : evalRule sys α F pr = evalRule sys α (fun _ => none) pr :=
            evalRule_local sys α α F (fun _ => none) pr (fun d n hd _ => by simp [obsDeps, hpr.2] at hd)
          rwa [← hr]
        · cases hp
  intro n p hcp
  cases hq : quenchIter sys α n p with
  | none => rfl
  | some b =>
    have hle := quenchIter_le_any_prefixed sys α hpos F hpre n p b hq
    simp [F, hcp] at hle

/-- T3a: On a single stratum `rank _ = 0`, stratified evaluation is IDENTICAL to Knaster-Tarski `quenchIter`. -/
theorem stratified_agrees_with_positive {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (steps : Nat) :
    evalStratified sys α (fun _ => 0) steps 0 = quenchIter sys α steps := by
  funext pid
  induction steps generalizing pid with
  | zero => simp [evalStratified, stratumIter, quenchIter]
  | succ n ih =>
    simp only [evalStratified, stratumIter, stratumStep, quenchIter,
               Nat.not_lt_zero, ↓reduceIte, beq_self_eq_true]
    have heq : stratumIter sys α (fun _ => 0) 0 (fun _ => none) n = quenchIter sys α n := by
      funext q; exact ih q
    rw [heq]

end Baugr
