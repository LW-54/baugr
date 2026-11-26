/-
  Baugr.Theorems — Machine-Checked Formal Proofs (0 sorryAx, zero Mathlib)
  Covers all 8 mathematical theorem families T1–T8 from ADR-0018 & RES-0027.
-/
import Baugr.Spacetime
import Baugr.Promise
import Baugr.Projection
import Baugr.Law

namespace Baugr

-- ============================================================================
-- T5a–T5c: Exact γ(3,4) Semantic Spacetime Type Algebra (arXiv:2506.07756v2)
-- ============================================================================

/-- Link inversion is an exact involution: `(r⁻¹)⁻¹ = r`. -/
theorem LinkKind.inv_inv (r : LinkKind) : r.inv.inv = r := by
  cases r <;> rfl

/-- Exact antisymmetry of the strict γ(3,4) transition matrix Â. -/
theorem allowed_antisym (u : NodeKind) (r : LinkKind) (v : NodeKind) :
    allowed u r v = allowed v r.inv u := by
  cases u <;> cases r <;> cases v <;> rfl

/-- All 4 axes are closed under homogeneous transitive composition. -/
theorem allowed_pos_trans (u v w : NodeKind) (r : LinkKind)
    (h1 : allowed u r v = true) (h2 : allowed v r w = true) :
    allowed u r w = true := by
  cases u <;> cases r <;> cases v <;> cases w <;> simp_all [allowed, allowedPos, LinkKind.inv]

/-- Couch/Burgess Inference Closure: `Contains ; Expresses ⊆ Expresses` (2506.07756v2 L1286). -/
theorem inference_contains_expresses (u v w : NodeKind)
    (h1 : allowed u .contains v = true) (h2 : allowed v .expresses w = true) :
    allowed u .expresses w = true := by
  cases u <;> cases v <;> cases w <;> simp_all [allowed, allowedPos]

/-- Couch/Burgess Inference Closure: `Near ; Expresses ⊆ Expresses` (2506.07756v2 L1290). -/
theorem inference_near_expresses (u v w : NodeKind)
    (h1 : allowed u .near v = true) (h2 : allowed v .expresses w = true) :
    allowed u .expresses w = true := by
  cases u <;> cases v <;> cases w <;> simp_all [allowed, allowedPos]

/-- Quotient coarse-graining G preserves γ(3,4) well-formedness whenever each grain is kind-homogeneous. -/
theorem coarseGrain_wellFormed {N M : Type} [DecidableEq M]
    (g : SstGraph N) (f : N → M) (qKind : M → NodeKind)
    (hwf : g.WellFormed)
    (hhom : ∀ n, qKind (f n) = g.kindOf n) :
    (g.coarseGrain f qKind).WellFormed := by
  intro e he
  simp only [SstGraph.coarseGrain, List.mem_filterMap] at he
  obtain ⟨orig, horig, hmap⟩ := he
  split at hmap
  · cases hmap
  · simp only [Option.some.injEq] at hmap
    subst hmap
    simp only [SstGraph.coarseGrain, hhom]
    exact hwf orig horig

-- ============================================================================
-- T1–T2: Knaster-Tarski Positive Quenching & Circular Rejection
-- ============================================================================

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

mutual
/-- T1a: Monotonicity of positive condition evaluation in Q. -/
theorem evalCond_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (c : Cond P), c.isPositive → SubSet Q₁ Q₂ →
    evalCond sys α Q₁ me c = true → evalCond sys α Q₂ me c = true
  | .selfPromise q, _, hsub, h => by
    simp only [evalCond] at h ⊢
    cases hfind : sys.find? q with
    | none => simp [hfind] at h
    | some pq =>
      simp only [hfind, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, hsub q h.1.2⟩, h.2⟩
  | .assisted u minP, _, hsub, h => by
    simp only [evalCond] at h ⊢
    cases hfind : sys.find? u with
    | none => simp [hfind] at h
    | some pu =>
      simp only [hfind] at h ⊢
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true] at hcond
        have hcond2 : (pu.promiser == me && pu.isUse && Q₂ u) = true := by
          simp [hcond.1.1, hcond.1.2, hsub u hcond.2]
        simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
        have hle := countP_mono
          (fun po => staticBindable sys po pu && Q₁ po.id && α me po.id)
          (fun po => staticBindable sys po pu && Q₂ po.id && α me po.id)
          sys.promises (fun po _ hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            exact ⟨⟨hp.1.1, hsub po.id hp.1.2⟩, hp.2⟩)
        exact Nat.le_trans h hle
      · simp at h
  | .accepted o minA, _, hsub, h => by
    simp only [evalCond] at h ⊢
    cases hfind : sys.find? o with
    | none => simp [hfind] at h
    | some po =>
      simp only [hfind] at h ⊢
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true] at hcond
        have hcond2 : (po.promiser == me && po.isOffer && Q₂ o) = true := by
          simp [hcond.1.1, hcond.1.2, hsub o hcond.2]
        simp only [hcond2, ↓reduceIte, decide_eq_true_eq] at h ⊢
        have hle := countP_mono
          (fun pu => staticBindable sys po pu && inScope pu me && Q₁ pu.id && α me pu.id)
          (fun pu => staticBindable sys po pu && inScope pu me && Q₂ pu.id && α me pu.id)
          sys.promises (fun pu _ hp => by
            simp only [Bool.and_eq_true] at hp ⊢
            exact ⟨⟨⟨hp.1.1.1, hp.1.1.2⟩, hsub pu.id hp.1.2⟩, hp.2⟩)
        exact Nat.le_trans h hle
      · simp at h
  | .interior q, _, hsub, h => by
    simp only [evalCond] at h ⊢
    cases hfind : sys.find? q with
    | none => simp [hfind] at h
    | some pq =>
      simp only [hfind, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, hsub q h.1.2⟩, h.2⟩
  | .atLeast k cs, hpos, hsub, h => by
    simp only [evalCond, decide_eq_true_eq] at h ⊢
    exact Nat.le_trans h (countSat_mono sys α Q₁ Q₂ me cs hpos hsub)
  | .not _, hpos, _, _ => False.elim hpos

theorem countSat_mono {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α : Assessment A P)
    (Q₁ Q₂ : P → Bool) (me : A) :
    ∀ (cs : List (Cond P)), Cond.listPositive cs → SubSet Q₁ Q₂ →
    countSat sys α Q₁ me cs ≤ countSat sys α Q₂ me cs
  | [], _, _ => Nat.le_refl 0
  | c :: rs, ⟨hc, hrs⟩, hsub => by
    simp only [countSat]
    have h1 : (if evalCond sys α Q₁ me c then 1 else 0) ≤
              (if evalCond sys α Q₂ me c then 1 else 0) := by
      cases he : evalCond sys α Q₁ me c with
      | false => simp
      | true => simp [evalCond_mono sys α Q₁ Q₂ me c hc hsub he]
    exact Nat.add_le_add h1 (countSat_mono sys α Q₁ Q₂ me rs hrs hsub)
end

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
    exact evalCond_mono sys α Q₁ Q₂ pr.promiser pr.cond (hpos pr (List.mem_of_find?_eq_some hfind)) hsub h

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

-- ============================================================================
-- T3: Stratified Evaluation Agreement
-- ============================================================================

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

/-- T3: On a positive system with single stratum `rank _ = 0`,
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

-- ============================================================================
-- T4: Axiom of Autonomy — Unaccepted Offer / Imposition Is Inert
-- ============================================================================

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
    have hne : q ≠ extra.id := hf q false (by simp [condDeps])
    have hfind : ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? q = sys.find? q := by
      simp only [PromiseSystem.find?, List.find?_append]
      cases sys.promises.find? (fun x => x.id == q) with
      | some x => simp
      | none =>
        have hb : (extra.id == q) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
        simp [hb]
    simp [evalCond, hfind]
  | .interior q, hf => by
    have hne : q ≠ extra.id := hf q false (by simp [condDeps])
    have hfind : ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? q = sys.find? q := by
      simp only [PromiseSystem.find?, List.find?_append]
      cases sys.promises.find? (fun x => x.id == q) with
      | some x => simp
      | none =>
        have hb : (extra.id == q) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
        simp [hb]
    simp [evalCond, hfind]
  | .assisted u minP, hf => by
    have hne : u ≠ extra.id := by
      apply hf u false; simp only [condDeps]; cases sys.find? u <;> simp
    have hfind : ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? u = sys.find? u := by
      simp only [PromiseSystem.find?, List.find?_append]
      cases sys.promises.find? (fun x => x.id == u) with
      | some x => simp
      | none =>
        have hb : (extra.id == u) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
        simp [hb]
    simp only [evalCond, hfind]
    cases hfu : sys.find? u with
    | none => rfl
    | some pu =>
      have hpu_mem : pu ∈ sys.promises := List.mem_of_find?_eq_some hfu
      have hsb : ∀ po, staticBindable { sys with promises := sys.promises ++ [extra] } po pu = staticBindable sys po pu := fun _ => rfl
      simp only [hsb, countP_append_singleton]
      have hx : (staticBindable sys extra pu && Q extra.id && α me extra.id) = false := by
        simp [hunacc pu hpu_mem]
      simp [hx]
  | .accepted o minA, hf => by
    have hne : o ≠ extra.id := by
      apply hf o false; simp only [condDeps]; cases sys.find? o <;> simp
    have hfind : ({ sys with promises := sys.promises ++ [extra] } : PromiseSystem A P O U M).find? o = sys.find? o := by
      simp only [PromiseSystem.find?, List.find?_append]
      cases sys.promises.find? (fun x => x.id == o) with
      | some x => simp
      | none =>
        have hb : (extra.id == o) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
        simp [hb]
    simp only [evalCond, hfind]
    cases hfo : sys.find? o with
    | none => rfl
    | some po =>
      have hsb : ∀ pu, staticBindable { sys with promises := sys.promises ++ [extra] } po pu = staticBindable sys po pu := fun _ => rfl
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

-- ============================================================================
-- T5d & T6: Projection Well-Formedness & Reverse Light Cone Perturbation Theorem
-- ============================================================================

/-- T5d: Canonical functor Φ : PromiseSystem → γ(3,4) always yields a well-formed SST graph. -/
theorem projectSst_wellFormed {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) :
    (projectSst sys).WellFormed := by
  intro e he
  simp only [projectSst, List.mem_append] at he
  rcases he with ((hc | hp) | hexp) | hcas
  · simp only [List.mem_filterMap] at hc
    obtain ⟨a, _, hsome⟩ := hc
    cases hpar : sys.hierarchy.parent a with
    | none => simp [hpar] at hsome
    | some s =>
      simp only [hpar, Option.some.injEq] at hsome
      subst hsome; rfl
  · simp only [List.mem_map] at hp
    obtain ⟨pr, _, rfl⟩ := hp; rfl
  · simp only [List.mem_flatMap] at hexp
    obtain ⟨pr, _, hmem⟩ := hexp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rfl
  · simp only [List.mem_flatMap, List.mem_filterMap] at hcas
    obtain ⟨pr, _, ⟨dep, neg⟩, _, hsome⟩ := hcas
    cases hfd : sys.find? dep with
    | none => simp [hfd] at hsome
    | some _ =>
      simp only [hfd, Option.some.injEq] at hsome
      subst hsome; rfl

theorem find?_isSome_of_mem {A P O U M : Type} [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U) (hmem : pr ∈ sys.promises) :
    ∃ x, sys.find? pr.id = some x := by
  cases h : sys.promises.find? (fun y => y.id == pr.id) with
  | some x => exact ⟨x, h⟩
  | none =>
    have hfalse := List.find?_eq_none.mp h pr hmem
    simp at hfalse

theorem dep_gives_leadsTo {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (pr : Promise A P O U)
    (hmem : pr ∈ sys.promises) (dep : P) (neg : Bool)
    (hdep : (dep, neg) ∈ condDeps sys false pr.cond)
    (hexists : ∃ x, sys.find? dep = some x) :
    SstEdge.mk (.promise dep) .leadsTo (.promise pr.id) ∈ (projectSst sys).edges := by
  obtain ⟨x, hx⟩ := hexists
  simp only [projectSst, List.mem_append]
  right
  simp only [List.mem_flatMap, List.mem_filterMap]
  exact ⟨pr, hmem, (dep, neg), hdep, by simp [hx]⟩

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

/-- T6 (CROWN-JEWEL UNIFICATION THEOREM):
    Perturbation Containment in the Semantic Spacetime Reverse Light Cone!
    Changing observer-local assessments outside the SST reverse causal cone `J⁻_Φ(target)`
    can NEVER change the quenched truth value of `target` (even with stratified `Not` fallbacks!). -/
theorem perturbation_in_reverse_cone {A P O U M : Type} [DecidableEq A] [DecidableEq P]
    (sys : PromiseSystem A P O U M) (α₁ α₂ : Assessment A P)
    (rank : P → Nat) (steps : Nat) (maxS : Nat) (target : P)
    (hcone : ∀ d, CausalReach (projectSst sys) (.promise d) (.promise target) →
      ∀ obs, α₁ obs d = α₂ obs d) :
    evalStratified sys α₁ rank steps maxS target =
    evalStratified sys α₂ rank steps maxS target := by
  suffices ∀ s p, CausalReach (projectSst sys) (.promise p) (.promise target) →
      evalStratified sys α₁ rank steps s p = evalStratified sys α₂ rank steps s p by
    exact this maxS target (.refl _)
  have hstratum : ∀ s b₁ b₂,
      (∀ p, CausalReach (projectSst sys) (.promise p) (.promise target) → b₁ p = b₂ p) →
      ∀ n p, CausalReach (projectSst sys) (.promise p) (.promise target) →
        stratumIter sys α₁ rank s b₁ n p = stratumIter sys α₂ rank s b₂ n p := by
    intro s b₁ b₂ hb n
    induction n with
    | zero =>
      intro p hp
      simp only [stratumIter]; split; exact hb p hp; rfl
    | succ k ih =>
      intro p hp
      simp only [stratumIter, stratumStep]
      split
      · exact hb p hp
      · split
        · simp only [quenchStep]
          cases hfp : sys.find? p with
          | none => rfl
          | some pr =>
            have hfp' : sys.promises.find? (fun pr => pr.id == p) = some pr := hfp
            have hmem : pr ∈ sys.promises := List.mem_of_find?_eq_some hfp'
            have hbeq := List.find?_some hfp'
            have hid : pr.id = p := eq_of_beq hbeq
            apply evalCond_local
            intro d neg hdep hex
            have hedge : SstEdge.mk (.promise d) .leadsTo (.promise p) ∈ (projectSst sys).edges := by
              rw [← hid]; exact dep_gives_leadsTo sys pr hmem d neg hdep hex
            have hd_reach : CausalReach (projectSst sys) (.promise d) (.promise target) :=
              .step hedge hp
            exact ⟨ih d hd_reach, hcone d hd_reach pr.promiser⟩
        · rfl
  intro s
  induction s with
  | zero =>
    intro p hp
    exact hstratum 0 (fun _ => false) (fun _ => false) (fun _ _ => rfl) steps p hp
  | succ k ih =>
    intro p hp
    exact hstratum (k + 1) _ _ ih steps p hp

-- ============================================================================
-- T7: Superagent Opaque Encapsulation & Interior Isolation
-- ============================================================================

/-- T7a: Non-piercing encapsulation (outward): an offer inside an opaque superagent cannot bind externally. -/
theorem opaque_non_piercing {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (s : A)
    (hs_mem : s ∈ sys.agents) (hs_op : sys.hierarchy.isOpaque s = true)
    (po pu : Promise A P O U)
    (hin  : isStrictAncAux sys.hierarchy sys.agents.length s po.promiser = true)
    (hout : pu.promiser ≠ s ∧ isStrictAncAux sys.hierarchy sys.agents.length s pu.promiser = false) :
    staticBindable sys po pu = false := by
  have hwall : noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser = false := by
    simp only [noOpaqueWall, List.all_eq_false]
    refine ⟨s, hs_mem, ?_⟩
    simp [hs_op, hin, hout.1, hout.2]
  cases hpo : po.body <;> cases hpu : pu.body <;> simp [staticBindable, hwall, hpo, hpu]

/-- T7a (inward): an external offer cannot pierce into a strict sub-agent's Use. -/
theorem opaque_non_piercing_inward {A P O U M : Type} [DecidableEq A]
    (sys : PromiseSystem A P O U M) (s : A)
    (hs_mem : s ∈ sys.agents) (hs_op : sys.hierarchy.isOpaque s = true)
    (po pu : Promise A P O U)
    (hout : po.promiser ≠ s ∧ isStrictAncAux sys.hierarchy sys.agents.length s po.promiser = false)
    (hin  : isStrictAncAux sys.hierarchy sys.agents.length s pu.promiser = true) :
    staticBindable sys po pu = false := by
  have hwall : noOpaqueWall sys.hierarchy sys.agents po.promiser pu.promiser = false := by
    simp only [noOpaqueWall, List.all_eq_false]
    refine ⟨s, hs_mem, ?_⟩
    simp [hs_op, hin, hout.1, hout.2]
  cases hpo : po.body <;> cases hpu : pu.body <;> simp [staticBindable, hwall, hpo, hpu]

/-- T7b: Interior perturbations of an opaque superagent cannot affect external promises
    whose causal cone stays outside the superagent's interior. -/
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

-- ============================================================================
-- T8: Generalized Monoidal Valency & Composable ScopeLaw Soundness
-- ============================================================================

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
      have h0 : ResourceMonoid.le (ResourceMonoid.add ResourceMonoid.zero (sumResource weight (xs.filter p)))
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
