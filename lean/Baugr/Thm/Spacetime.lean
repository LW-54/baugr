/-
  Baugr.Thm.Spacetime — Exact γ(3,4) Semantic Spacetime Type Algebra & Coarse-Graining (T5a–T5c)
  Derived from Mark Burgess (2025, arXiv:2506.07756v2 §§3–5) & (2015, arXiv:1505.01716v1 §3.5).
-/
import Baugr.Spacetime

namespace Baugr

/-- T5a: Link inversion is an exact involution: `(r⁻¹)⁻¹ = r`. -/
theorem LinkKind.inv_inv (r : LinkKind) : r.inv.inv = r := by
  cases r <;> rfl

/-- T5a: Exact antisymmetry of the strict γ(3,4) transition matrix Â. -/
theorem allowed_antisym (u : NodeKind) (r : LinkKind) (v : NodeKind) :
    allowed u r v = allowed v r.inv u := by
  cases u <;> cases r <;> cases v <;> rfl

/-- T5a: Normalized edge relation is exact with respect to link inversion (`u --r--> v ↔ v --r⁻¹--> u`). -/
theorem hasEdge_inv {N : Type} (g : SstGraph N) (u : N) (r : LinkKind) (v : N) :
    g.hasEdge u r v ↔ g.hasEdge v r.inv u := by
  simp only [SstGraph.hasEdge, LinkKind.inv_inv]
  exact Or.comm

/-- T5a: Every normalized edge in a well-formed graph obeys strict γ(3,4) admissibility. -/
theorem hasEdge_wellFormed {N : Type} (g : SstGraph N) (hwf : g.WellFormed)
    {u v : N} {r : LinkKind} (he : g.hasEdge u r v) :
    allowed (g.kindOf u) r (g.kindOf v) = true := by
  rcases he with h | h
  · exact hwf _ h
  · rw [allowed_antisym]
    exact hwf _ h

/-- T5b: All 4 axes are closed under homogeneous transitive composition. -/
theorem allowed_pos_trans (u v w : NodeKind) (r : LinkKind)
    (h1 : allowed u r v = true) (h2 : allowed v r w = true) :
    allowed u r w = true := by
  cases u <;> cases r <;> cases v <;> cases w <;> simp_all [allowed, allowedPos, LinkKind.inv]

/-- T5c: Couch/Burgess inference closure: `Contains ; Expresses ⊆ Expresses` (2506.07756v2 L1286). -/
theorem inference_contains_expresses (u v w : NodeKind)
    (h1 : allowed u .contains v = true) (h2 : allowed v .expresses w = true) :
    allowed u .expresses w = true := by
  cases u <;> cases v <;> cases w <;> simp_all [allowed, allowedPos]

/-- T5c: Couch/Burgess inference closure: `Near ; Expresses ⊆ Expresses` (2506.07756v2 L1290). -/
theorem inference_near_expresses (u v w : NodeKind)
    (h1 : allowed u .near v = true) (h2 : allowed v .expresses w = true) :
    allowed u .expresses w = true := by
  cases u <;> cases v <;> cases w <;> simp_all [allowed, allowedPos]

/-- T5c: Quotient coarse-graining G preserves γ(3,4) well-formedness under kind-homogeneous grains. -/
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

end Baugr
