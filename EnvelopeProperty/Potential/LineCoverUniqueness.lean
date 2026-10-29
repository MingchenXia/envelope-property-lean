import EnvelopeProperty.Potential.LineAffinoidRestrictions

/-! # Actual arbitrary-cover restrictions detect whole original completed functions -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- Whole evaluations in the SAME original completed residue fields faithfully determine actual functions. -/
theorem analyticFunctions_eq_of_evaluation_eq (f g : U.AnalyticFunctions)
    (hfg : ∀ x : U.carrier, U.evaluationToH x f = U.evaluationToH x g) : f = g := by
  apply sub_eq_zero.mp
  apply nnnorm_eq_zero.mp
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  rw [U.nnnorm_eq_boundary_max]
  apply le_antisymm _ zero_le
  apply Finset.sup_le
  intro z _
  change ‖U.evaluationToH ⟨z.1,U.boundary_subset z.2⟩ (f-g)‖₊ ≤ 0
  rw [map_sub,hfg,sub_self,nnnorm_zero]

variable {ι : Type*} {n : ι → ℕ} (V : ∀ i, FCStandardAffinoid w (n i))
variable (hVU : ∀ i, (V i).carrier ⊆ U.carrier)
variable (hcover : ∀ x ∈ U.carrier, ∃ i, x ∈ (V i).carrier)

include hcover in
/-- Arbitrary actual covers detect WHOLE functions, using only their actual restriction equalities. -/
theorem analyticFunctions_eq_of_cover_restrictions_eq (f g : U.AnalyticFunctions)
    (hfg : ∀ i, U.analyticRestriction (V i) (hVU i) f = U.analyticRestriction (V i) (hVU i) g) :
    f = g := by
  apply U.analyticFunctions_eq_of_evaluation_eq f g
  intro x
  obtain ⟨i,hi⟩ := hcover x.1 x.2
  have he := congrArg ((V i).evaluationToH ⟨x.1,hi⟩) (hfg i)
  rw [U.analyticRestriction_evaluation,U.analyticRestriction_evaluation] at he
  exact he

/-- The ACTUAL whole restriction to every original covering affinoid, retaining all original completed algebras. -/
def analyticCoverRestriction : U.AnalyticFunctions →+* (∀ i, (V i).AnalyticFunctions) where
  toFun f i := U.analyticRestriction (V i) (hVU i) f
  map_one' := by funext i; exact map_one _
  map_mul' f g := by funext i; exact map_mul _ _ _
  map_zero' := by funext i; exact map_zero _
  map_add' f g := by funext i; exact map_add _ _ _

include hcover in
theorem analyticCoverRestriction_injective : Function.Injective (U.analyticCoverRestriction V hVU) := by
  intro f g hfg
  apply U.analyticFunctions_eq_of_cover_restrictions_eq V hVU hcover f g
  intro i
  exact congrFun hfg i

include hcover in
/-- The exact original joint norm of every WHOLE completed function on ANY actual finite cover. -/
theorem nnnorm_eq_cover_restrictions [Fintype ι] (f : U.AnalyticFunctions) :
    ‖f‖₊ = Finset.univ.sup (fun i => ‖U.analyticRestriction (V i) (hVU i) f‖₊) := by
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  apply le_antisymm
  · rw [U.nnnorm_eq_boundary_max]
    apply Finset.sup_le
    intro z _
    obtain ⟨i,hi⟩ := hcover z.1 (U.boundary_subset z.2)
    change ‖U.evaluationToH ⟨z.1,U.boundary_subset z.2⟩ f‖₊ ≤ _
    have he := U.analyticRestriction_evaluation (V i) (hVU i) ⟨z.1,hi⟩ f
    rw [← he]
    exact ((V i).nnnorm_evaluationToH_le _ _).trans
      (Finset.le_sup (f := fun j => ‖U.analyticRestriction (V j) (hVU j) f‖₊) (Finset.mem_univ i))
  · exact Finset.sup_le fun i _ => U.nnnorm_analyticRestriction_le (V i) (hVU i) f

include hcover in
/-- The ACTUAL joint whole restriction into the genuine finite product is an isometry. -/
theorem isometry_analyticCoverRestriction [Fintype ι] : Isometry (U.analyticCoverRestriction V hVU) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  have he : ‖U.analyticCoverRestriction V hVU f‖₊ = ‖f‖₊ := by
    rw [Pi.nnnorm_def]
    exact (U.nnnorm_eq_cover_restrictions V hVU hcover f).symm
  exact congrArg NNReal.toReal he
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
