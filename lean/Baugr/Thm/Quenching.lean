/-
  Baugr.Thm.Quenching — Knaster-Tarski Quenching, Cycle Rejection, Locality & Stratum Monotonicity (T1–T3)
-/
import Baugr.Promise

namespace Baugr

-- ----------------------------------------------------------------------------
-- Counting & lookup utilities
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

theorem find?_id_eq {A P O U M : Type} [DecidableEq P]
    {sys : PromiseSystem A P O U M} {pid : P} {pr : Promise A P O U}
    (h : sys.find? pid = some pr) : pr.id = pid := by
  have h' : sys.promises.find? (fun y => y.id == pid) = some pr := h
  have hbeq := List.find?_some h'
  exact eq_of_beq hbeq

theorem find?_isSome_of_mem {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U) (hmem : pr ∈ sys.promises) :
    ∃ x, sys.find? pr.id = some x := by
  cases h : sys.promises.find? (fun y => y.id == pr.id) with
  | some x => exact ⟨x, h⟩
  | none =>
    have hfalse := List.find?_eq_none.mp h pr hmem
    simp at hfalse

-- ----------------------------------------------------------------------------
-- Polarity-indexed dependency lemmas & local evaluation congruence
-- ----------------------------------------------------------------------------

mutual
theorem condDeps_neg_flip {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (b : Bool) (d : P) :
    ∀ (c : Cond P),
    (∃ n, (d, n) ∈ condDeps sys b c) ↔ (∃ n, (d, n) ∈ condDeps sys (!b) c)
  | .selfPromise _ => by simp [condDeps]
  | .assisted u _  => by
    simp only [condDeps]
    cases sys.find? u with
    | none => simp
    | some pu =>
      constructor <;> (rintro ⟨n, h⟩; refine ⟨!n, ?_⟩; simp_all)
  | .accepted o _  => by
    simp only [condDeps]
    cases sys.find? o with
    | none => simp
    | some po =>
      constructor <;> (rintro ⟨n, h⟩; refine ⟨!n, ?_⟩; simp_all)
  | .interior _    => by simp [condDeps]
  | .atLeast _ cs  => listCondDeps_neg_flip sys b d cs
  | .not c         => by
    simp only [condDeps, Bool.not_not]
    exact (condDeps_neg_flip sys b d c).symm

theorem listCondDeps_neg_flip {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (b : Bool) (d : P) :
    ∀ (cs : List (Cond P)),
    (∃ n, (d, n) ∈ listCondDeps sys b cs) ↔ (∃ n, (d, n) ∈ listCondDeps sys (!b) cs)
  | [] => by simp [listCondDeps]
  | c :: rs => by
    simp only [listCondDeps, List.mem_append]
    constructor
    · rintro ⟨n, h1 | h2⟩
      · obtain ⟨m, hm⟩ := (condDeps_neg_flip sys b d c).mp ⟨n, h1⟩; exact ⟨m, Or.inl hm⟩
      · obtain ⟨m, hm⟩ := (listCondDeps_neg_flip sys b d rs).mp ⟨n, h2⟩; exact ⟨m, Or.inr hm⟩
    · rintro ⟨n, h1 | h2⟩
      · obtain ⟨m, hm⟩ := (condDeps_neg_flip sys b d c).mpr ⟨n, h1⟩; exact ⟨m, Or.inl hm⟩
      · obtain ⟨m, hm⟩ := (listCondDeps_neg_flip sys b d rs).mpr ⟨n, h2⟩; exact ⟨m, Or.inr hm⟩
end

mutual
theorem evalCond_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (c : Cond P),
      (∀ d n, (d, n) ∈ condDeps sys false c → (∃ x, sys.find? d = some x) →
        Q₁ d = Q₂ d ∧ α₁ me d = α₂ me d) →
      evalCond sys α₁ Q₁ me c = evalCond sys α₂ Q₂ me c
  | .selfPromise q, hagree => by
    simp only [evalCond]
    cases hfq : sys.find? q with
    | none => rfl
    | some pq =>
      have hq := hagree q false (by simp [condDeps]) ⟨pq, hfq⟩
      simp [hq.1, hq.2]
  | .interior q, hagree => by
    simp only [evalCond]
    cases hfq : sys.find? q with
    | none => rfl
    | some pq =>
      have hq := hagree q false (by simp [condDeps]) ⟨pq, hfq⟩
      simp [hq.1, hq.2]
  | .assisted u minP, hagree => by
    simp only [evalCond]
    cases hfu : sys.find? u with
    | none => rfl
    | some pu =>
      have hu : Q₁ u = Q₂ u :=
        (hagree u false (by simp [condDeps, hfu]) ⟨pu, hfu⟩).1
      simp only [hu]
      split
      · suffices countP (fun po => staticBindable sys po pu && Q₁ po.id && α₁ me po.id) sys.promises =
                 countP (fun po => staticBindable sys po pu && Q₂ po.id && α₂ me po.id) sys.promises by
          rw [this]
        apply countP_congr
        intro po hpo_mem
        cases hsb : staticBindable sys po pu with
        | false => simp
        | true =>
          have hdep : (po.id, false) ∈ condDeps sys false (.assisted u minP) := by
            simp only [condDeps, hfu, List.mem_cons, List.mem_map, List.mem_filter]
            right; exact ⟨po, ⟨hpo_mem, hsb⟩, rfl⟩
          have hpo := hagree po.id false hdep (find?_isSome_of_mem sys po hpo_mem)
          simp [hpo.1, hpo.2]
      · rfl
  | .accepted o minA, hagree => by
    simp only [evalCond]
    cases hfo : sys.find? o with
    | none => rfl
    | some po =>
      have ho : Q₁ o = Q₂ o :=
        (hagree o false (by simp [condDeps, hfo]) ⟨po, hfo⟩).1
      simp only [ho]
      split
      · next hcond =>
        simp only [Bool.and_eq_true] at hcond
        have hme : po.promiser = me := eq_of_beq hcond.1.1
        suffices countP (fun pu => staticBindable sys po pu && inScope pu me && Q₁ pu.id && α₁ me pu.id) sys.promises =
                 countP (fun pu => staticBindable sys po pu && inScope pu me && Q₂ pu.id && α₂ me pu.id) sys.promises by
          rw [this]
        apply countP_congr
        intro pu hpu_mem
        cases hsb : staticBindable sys po pu with
        | false => simp
        | true =>
          cases hsc : inScope pu me with
          | false => simp
          | true =>
            have hdep : (pu.id, false) ∈ condDeps sys false (.accepted o minA) := by
              simp only [condDeps, hfo, List.mem_cons, List.mem_map, List.mem_filter]
              right; exact ⟨pu, ⟨hpu_mem, by simp [hsb, hme, hsc]⟩, rfl⟩
            have hpu := hagree pu.id false hdep (find?_isSome_of_mem sys pu hpu_mem)
            simp [hpu.1, hpu.2]
      · rfl
  | .atLeast k cs, hagree => by
    simp only [evalCond]
    rw [countSat_local sys α₁ α₂ Q₁ Q₂ me cs hagree]
  | .not c, hagree => by
    simp only [evalCond]
    have hsub : ∀ d n, (d, n) ∈ condDeps sys false c → (∃ x, sys.find? d = some x) →
        Q₁ d = Q₂ d ∧ α₁ me d = α₂ me d := by
      intro d n hdn hex
      obtain ⟨m, hm⟩ := (condDeps_neg_flip sys false d c).mp ⟨n, hdn⟩
      exact hagree d m hm hex
    rw [evalCond_local sys α₁ α₂ Q₁ Q₂ me c hsub]

theorem countSat_local {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (cs : List (Cond P)),
      (∀ d n, (d, n) ∈ listCondDeps sys false cs → (∃ x, sys.find? d = some x) →
        Q₁ d = Q₂ d ∧ α₁ me d = α₂ me d) →
      countSat sys α₁ Q₁ me cs = countSat sys α₂ Q₂ me cs
  | [], _ => rfl
  | c :: rs, hagree => by
    simp only [countSat]
    have h1 := evalCond_local sys α₁ α₂ Q₁ Q₂ me c
      (fun d n hdn hex => hagree d n (List.mem_append_left _ hdn) hex)
    have h2 := countSat_local sys α₁ α₂ Q₁ Q₂ me rs
      (fun d n hdn hex => hagree d n (List.mem_append_right _ hdn) hex)
    rw [h1, h2]
end

theorem quenchStep_ext_promises {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (Q₁ Q₂ : P → Bool)
    (heq : ∀ pr ∈ sys.promises, Q₁ pr.id = Q₂ pr.id) :
    quenchStep sys α Q₁ = quenchStep sys α Q₂ := by
  funext pid
  simp only [quenchStep]
  cases hfind : sys.find? pid with
  | none => rfl
  | some pr =>
    apply evalCond_local
    intro d _ _ ⟨x, hx⟩
    have hx_mem : x ∈ sys.promises := List.mem_of_find?_eq_some hx
    have hx_id : x.id = d := find?_id_eq hx
    rw [← hx_id]
    exact ⟨heq x hx_mem, rfl⟩

-- ----------------------------------------------------------------------------
-- Polarity-indexed monotonicity (handles arbitrary nested `Not` within strata!)
-- ----------------------------------------------------------------------------

/-- Order on Bool indexed by negation parity (`false` = monotone, `true` = antitone). -/
def BoolLePol (neg : Bool) (a b : Bool) : Prop :=
  if neg then (b = true → a = true) else (a = true → b = true)

theorem BoolLePol_not (neg a b : Bool) (h : BoolLePol (!neg) a b) :
    BoolLePol neg (!a) (!b) := by
  cases neg <;> cases a <;> cases b <;> simp_all [BoolLePol]

mutual
/-- Polarity-indexed monotonicity of `evalCond` under arbitrary nested `Not`:
    requires `Q₁ ≤ Q₂` on positive dependencies and `Q₂ ≤ Q₁` on negative dependencies. -/
theorem evalCond_mono_pol {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (neg : Bool) (c : Cond P),
      (∀ d b, (d, b) ∈ condDeps sys neg c → BoolLePol b (Q₁ d) (Q₂ d)) →
      BoolLePol neg (evalCond sys α Q₁ me c) (evalCond sys α Q₂ me c)
  | neg, .selfPromise q, hdep => by
    have hq := hdep q neg (by simp [condDeps])
    cases neg <;> simp only [BoolLePol, evalCond] at hq ⊢
    · cases hfind : sys.find? q with
      | none => intro h; simp at h
      | some pq =>
        simp only [Bool.and_eq_true]
        intro h; exact ⟨⟨h.1.1, hq h.1.2⟩, h.2⟩
    · cases hfind : sys.find? q with
      | none => intro h; simp at h
      | some pq =>
        simp only [Bool.and_eq_true]
        intro h; exact ⟨⟨h.1.1, hq h.1.2⟩, h.2⟩
  | neg, .interior q, hdep => by
    have hq := hdep q neg (by simp [condDeps])
    cases neg <;> simp only [BoolLePol, evalCond] at hq ⊢
    · cases hfind : sys.find? q with
      | none => intro h; simp at h
      | some pq =>
        simp only [Bool.and_eq_true]
        intro h; exact ⟨⟨h.1.1, hq h.1.2⟩, h.2⟩
    · cases hfind : sys.find? q with
      | none => intro h; simp at h
      | some pq =>
        simp only [Bool.and_eq_true]
        intro h; exact ⟨⟨h.1.1, hq h.1.2⟩, h.2⟩
  | neg, .assisted u minP, hdep => by
    cases hfu : sys.find? u with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfu]
    | some pu =>
      have hu := hdep u neg (by simp [condDeps, hfu])
      have hpo : ∀ po ∈ sys.promises, staticBindable sys po pu = true →
          BoolLePol neg (Q₁ po.id) (Q₂ po.id) := by
        intro po hmem hsb
        apply hdep po.id neg
        simp only [condDeps, hfu, List.mem_cons, List.mem_map, List.mem_filter]
        right; exact ⟨po, ⟨hmem, hsb⟩, rfl⟩
      cases neg <;> simp only [BoolLePol, evalCond, hfu] at hu ⊢
      · intro h
        split at h
        · next hcond =>
          simp only [Bool.and_eq_true] at hcond
          have hcond2 : (pu.promiser == me && pu.isUse && Q₂ u) = true := by
            simp [hcond.1.1, hcond.1.2, hu hcond.2]
          simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
          exact Nat.le_trans h (countP_mono _ _ sys.promises fun po hmem hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            exact ⟨⟨hp.1.1, hpo po hmem hp.1.1 hp.1.2⟩, hp.2⟩)
        · simp at h
      · intro h
        split at h
        · next hcond =>
          simp only [Bool.and_eq_true] at hcond
          have hcond1 : (pu.promiser == me && pu.isUse && Q₁ u) = true := by
            simp [hcond.1.1, hcond.1.2, hu hcond.2]
          simp only [hcond1, ↓reduceIte, decide_eq_true_eq] at h ⊢
          exact Nat.le_trans h (countP_mono _ _ sys.promises fun po hmem hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            exact ⟨⟨hp.1.1, hpo po hmem hp.1.1 hp.1.2⟩, hp.2⟩)
        · simp at h
  | neg, .accepted o minA, hdep => by
    cases hfo : sys.find? o with
    | none => cases neg <;> simp [BoolLePol, evalCond, hfo]
    | some po =>
      have ho := hdep o neg (by simp [condDeps, hfo])
      have hpu : ∀ pu ∈ sys.promises, staticBindable sys po pu = true →
          inScope pu po.promiser = true → BoolLePol neg (Q₁ pu.id) (Q₂ pu.id) := by
        intro pu hmem hsb hsc
        apply hdep pu.id neg
        simp only [condDeps, hfo, List.mem_cons, List.mem_map, List.mem_filter]
        right; exact ⟨pu, ⟨hmem, by simp [hsb, hsc]⟩, rfl⟩
      cases neg <;> simp only [BoolLePol, evalCond, hfo] at ho ⊢
      · intro h
        split at h
        · next hcond =>
          simp only [Bool.and_eq_true] at hcond
          have hme : po.promiser = me := eq_of_beq hcond.1.1
          have hcond2 : (po.promiser == me && po.isOffer && Q₂ o) = true := by
            simp [hcond.1.1, hcond.1.2, ho hcond.2]
          simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
          exact Nat.le_trans h (countP_mono _ _ sys.promises fun pu hmem hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            have hsc : inScope pu po.promiser = true := by rw [hme]; exact hp.1.1.2
            exact ⟨⟨⟨hp.1.1.1, hp.1.1.2⟩, hpu pu hmem hp.1.1.1 hsc hp.1.2⟩, hp.2⟩)
        · simp at h
      · intro h
        split at h
        · next hcond =>
          simp only [Bool.and_eq_true] at hcond
          have hme : po.promiser = me := eq_of_beq hcond.1.1
          have hcond1 : (po.promiser == me && po.isOffer && Q₁ o) = true := by
            simp [hcond.1.1, hcond.1.2, ho hcond.2]
          simp only [hcond1, ↓reduceIte, decide_eq_true_eq] at h ⊢
          exact Nat.le_trans h (countP_mono _ _ sys.promises fun pu hmem hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            have hsc : inScope pu po.promiser = true := by rw [hme]; exact hp.1.1.2
            exact ⟨⟨⟨hp.1.1.1, hp.1.1.2⟩, hpu pu hmem hp.1.1.1 hsc hp.1.2⟩, hp.2⟩)
        · simp at h
  | neg, .atLeast k cs, hdep => by
    have hcs := countSat_mono_pol sys α Q₁ Q₂ me neg cs hdep
    cases neg <;> simp only [BoolLePol, evalCond, decide_eq_true_eq] at hcs ⊢ <;>
      exact fun h => Nat.le_trans h hcs
  | neg, .not c, hdep => by
    simp only [evalCond]
    exact BoolLePol_not neg _ _ (evalCond_mono_pol sys α Q₁ Q₂ me (!neg) c hdep)

theorem countSat_mono_pol {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (neg : Bool) (cs : List (Cond P)),
      (∀ d b, (d, b) ∈ listCondDeps sys neg cs → BoolLePol b (Q₁ d) (Q₂ d)) →
      (if neg then countSat sys α Q₂ me cs ≤ countSat sys α Q₁ me cs
              else countSat sys α Q₁ me cs ≤ countSat sys α Q₂ me cs)
  | neg, [], _ => by cases neg <;> exact Nat.le_refl 0
  | neg, c :: rs, hdep => by
    have hc := evalCond_mono_pol sys α Q₁ Q₂ me neg c
      (fun d b h => hdep d b (List.mem_append_left _ h))
    have hrs := countSat_mono_pol sys α Q₁ Q₂ me neg rs
      (fun d b h => hdep d b (List.mem_append_right _ h))
    cases neg <;> simp only [BoolLePol, countSat] at hc hrs ⊢
    · have h1 : (if evalCond sys α Q₁ me c then 1 else 0) ≤
                (if evalCond sys α Q₂ me c then 1 else 0) := by
        cases h : evalCond sys α Q₁ me c with
        | false => simp
        | true => simp [hc h]
      exact Nat.add_le_add h1 hrs
    · have h1 : (if evalCond sys α Q₂ me c then 1 else 0) ≤
                (if evalCond sys α Q₁ me c then 1 else 0) := by
        cases h : evalCond sys α Q₂ me c with
        | false => simp
        | true => simp [hc h]
      exact Nat.add_le_add h1 hrs
end

-- ----------------------------------------------------------------------------
-- T1–T3: Positive Knaster-Tarski Quenching & Cycle Rejection
-- ----------------------------------------------------------------------------

mutual
theorem condDeps_positive_only {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) :
    ∀ (c : Cond P), c.isPositive → ∀ d b, (d, b) ∈ condDeps sys false c → b = false
  | .selfPromise _, _, _, _, h => by simp [condDeps] at h; exact h.2
  | .interior _,    _, _, _, h => by simp [condDeps] at h; exact h.2
  | .assisted u _,  _, _, _, h => by
    simp only [condDeps] at h
    cases hfu : sys.find? u with
    | none => simp [hfu] at h; exact h.2
    | some pu =>
      simp only [hfu, List.mem_cons, List.mem_map, Prod.mk.injEq] at h
      rcases h with ⟨_, hb⟩ | ⟨po, _, _, hb⟩ <;> simp_all
  | .accepted o _,  _, _, _, h => by
    simp only [condDeps] at h
    cases hfo : sys.find? o with
    | none => simp [hfo] at h; exact h.2
    | some po =>
      simp only [hfo, List.mem_cons, List.mem_map, Prod.mk.injEq] at h
      rcases h with ⟨_, hb⟩ | ⟨pu, _, _, hb⟩ <;> simp_all
  | .atLeast _ cs, hpos, d, b, h => listCondDeps_positive_only sys cs hpos d b h
  | .not _,        hpos, _, _, _ => False.elim hpos

theorem listCondDeps_positive_only {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) :
    ∀ (cs : List (Cond P)), Cond.listPositive cs →
      ∀ d b, (d, b) ∈ listCondDeps sys false cs → b = false
  | [], _, _, _, h => by simp [listCondDeps] at h
  | c :: rs, ⟨hc, hrs⟩, d, b, h => by
    simp only [listCondDeps, List.mem_append] at h
    rcases h with h1 | h2
    · exact condDeps_positive_only sys c hc d b h1
    · exact listCondDeps_positive_only sys rs hrs d b h2
end

/-- T1a: Monotonicity of positive condition evaluation in Q. -/
theorem evalCond_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) (c : Cond P)
    (hpos : c.isPositive) (hsub : SubSet Q₁ Q₂) :
    evalCond sys α Q₁ me c = true → evalCond sys α Q₂ me c = true :=
  evalCond_mono_pol sys α Q₁ Q₂ me false c fun d b h => by
    have hb := condDeps_positive_only sys c hpos d b h
    subst hb
    exact hsub d

/-- T1a: Monotonicity of one-step quenching operator T(Q) on positive systems. -/
theorem quenchStep_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (Q₁ Q₂ : P → Bool) (hsub : SubSet Q₁ Q₂) :
    SubSet (quenchStep sys α Q₁) (quenchStep sys α Q₂) := by
  intro pid h
  simp only [quenchStep] at h ⊢
  cases hfind : sys.find? pid with
  | none => simp [hfind] at h
  | some pr =>
    simp only [hfind] at h ⊢
    exact evalCond_mono sys α Q₁ Q₂ pr.promiser pr.cond
      (hpos pr (List.mem_of_find?_eq_some hfind)) hsub h

/-- T1b: Knaster-Tarski leastness — every iterate is bounded by any pre-fixed point. -/
theorem quenchIter_le_any_prefixed {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (F : P → Bool) (hpre : SubSet (quenchStep sys α F) F) (n : Nat) :
    SubSet (quenchIter sys α n) F := by
  induction n with
  | zero => intro _ h; simp [quenchIter] at h
  | succ k ih =>
    intro p hp
    exact hpre p (quenchStep_mono sys α hpos _ _ ih p hp)

/-- T1c: Ascending chain property: `quenchIter n ⊆ quenchIter (n + 1)`. -/
theorem quenchIter_chain {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys) (n : Nat) :
    SubSet (quenchIter sys α n) (quenchIter sys α (n + 1)) := by
  induction n with
  | zero => intro _ h; simp [quenchIter] at h
  | succ k ih => exact quenchStep_mono sys α hpos _ _ ih

/-- T2: Cyclic self-dependent conditionals NEVER quench in the least fixed point. -/
theorem cyclic_conditional_never_quenches {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (hpos : PositiveSystem sys)
    (C : P → Bool)
    (hclosed : ∀ p, C p = true → quenchStep sys α (fun q => !C q) p = false) :
    ∀ n p, C p = true → quenchIter sys α n p = false := by
  have hpre : SubSet (quenchStep sys α (fun q => !C q)) (fun q => !C q) := by
    intro p hp
    cases hc : C p with
    | false => simp [hc]
    | true =>
      have hf := hclosed p hc
      rw [hf] at hp
      cases hp
  intro n p hcp
  cases hq : quenchIter sys α n p with
  | false => rfl
  | true =>
    have hle := quenchIter_le_any_prefixed sys α hpos (fun q => !C q) hpre n p hq
    simp [hcp] at hle

/-- T3a: On a positive system with single stratum `rank _ = 0`,
    stratified evaluation is IDENTICAL to Knaster-Tarski `quenchIter`. -/
theorem stratified_agrees_with_positive {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P) (steps : Nat) :
    evalStratified sys α (fun _ => 0) steps 0 = quenchIter sys α steps := by
  funext pid
  induction steps generalizing pid with
  | zero => simp [evalStratified, stratumIter, quenchIter]
  | succ n ih =>
    simp only [evalStratified, stratumIter, stratumStep, quenchIter,
               Nat.not_lt_zero, ↓reduceIte, beq_self_eq_true]
    have heq : stratumIter sys α (fun _ => 0) 0 (fun _ => false) n = quenchIter sys α n := by
      funext q; exact ih q
    rw [heq]

end Baugr
