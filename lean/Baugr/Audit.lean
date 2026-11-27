/-
  Baugr.Audit — Mechanical Axiom Verification Gate (Zero sorryAx!)
-/
import Baugr

-- T5a–T5c: Strict γ(3,4) Semantic Spacetime & Coarse-Graining
#print axioms Baugr.LinkKind.inv_inv
#print axioms Baugr.allowed_antisym
#print axioms Baugr.hasEdge_inv
#print axioms Baugr.hasEdge_wellFormed
#print axioms Baugr.allowed_pos_trans
#print axioms Baugr.inference_contains_expresses
#print axioms Baugr.inference_near_expresses
#print axioms Baugr.coarseGrain_wellFormed

-- T1–T3: Value-Carrying Knaster-Tarski Quenching, Cycle Rejection, Convergence & Stratification Independence
#print axioms Baugr.evalCond_mono
#print axioms Baugr.evalCond_mono_pol
#print axioms Baugr.quenchStep_mono
#print axioms Baugr.quenchIter_le_any_prefixed
#print axioms Baugr.quenchIter_chain
#print axioms Baugr.cyclic_conditional_never_quenches
#print axioms Baugr.stratified_agrees_with_positive
#print axioms Baugr.checkValidStratification_sound
#print axioms Baugr.stratumStep_mono
#print axioms Baugr.stratumIter_fixed_point
#print axioms Baugr.evalStratified_fixed_point
#print axioms Baugr.stratification_independent

-- T4: Axiom of Autonomy (Unconditional External Offer/Imposition Inertness)
#print axioms Baugr.autonomy_unaccepted_offer_inert

-- T5d & T6: Canonical Functor Φ & Reverse Light Cone Perturbation Containment (Value Bodies)
#print axioms Baugr.projectSst_wellFormed
#print axioms Baugr.perturbation_in_reverse_cone

-- T7: Opaque Superagent Encapsulation & Topological Event-Horizon Vertex-Cut Theorem
#print axioms Baugr.noOpaqueWall_refl
#print axioms Baugr.noOpaqueWall_symm
#print axioms Baugr.opaque_non_piercing
#print axioms Baugr.opaque_non_piercing_inward
#print axioms Baugr.opaque_interior_perturbation_contained
#print axioms Baugr.opaque_no_direct_causal_crossing
#print axioms Baugr.opaque_event_horizon_cut

-- T8: Monoidal Valency (`Cap R`), Grouped Budgets, Composable ScopeLaws & Universal Static Discharge
#print axioms Baugr.valency_withdrawal_safe
#print axioms Baugr.allLaws_cons
#print axioms Baugr.activeBindings_sublist_staticMax
#print axioms Baugr.static_discharge_universal
#print axioms Baugr.budget_downward_closed
#print axioms Baugr.disjoint_downward_closed
#print axioms Baugr.agreement_downward_closed
