import EnvelopeProperty.Potential.CurveAnalyticSpecializationNorm

/-! # Actual whole curve analytic restriction and exact specialization compatibility -/

open scoped NNReal Polynomial TensorProduct
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)

/-- Actual completed analytic restriction retains the ORIGINAL polynomial algebra action. -/
def polynomialAnalyticRestriction : U.AnalyticFunctions →ₐ[K[X]] V.AnalyticFunctions where
  __ := U.analyticRestriction V hVU
  commutes' := U.analyticRestriction_polynomial V hVU

/-- The entire ORIGINAL tensor curve algebra restricts for every actual carrier containment. -/
def curveAnalyticRestriction : U.CurveAnalyticTensor B →ₐ[K[X]] V.CurveAnalyticTensor B :=
  Algebra.TensorProduct.map (U.polynomialAnalyticRestriction V hVU) (AlgHom.id K[X] B)

theorem curveAnalyticRestriction_tmul (r : U.AnalyticFunctions) (c : B) :
    U.curveAnalyticRestriction V hVU (r ⊗ₜ[K[X]] c) = U.analyticRestriction V hVU r ⊗ₜ[K[X]] c := rfl

/-- Every WHOLE original completed-fibre specialization commutes with actual restriction. -/
theorem curveAnalyticRestriction_specialization (x : V.carrier) (v : U.CurveAnalyticTensor B) :
    V.curveAnalyticSpecialization x (U.curveAnalyticRestriction V hVU v) =
      U.curveAnalyticSpecialization ⟨x.1,hVU x.2⟩ v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r c =>
      rw [U.curveAnalyticRestriction_tmul,curveAnalyticSpecialization,curveAnalyticSpecialization,
        Algebra.TensorProduct.map_tmul,Algebra.TensorProduct.map_tmul]
      change V.evaluationToH x (U.analyticRestriction V hVU r) ⊗ₜ[K[X]] c = _
      rw [U.analyticRestriction_evaluation V hVU x r]
      rfl
  | add v z hv hz => simp only [map_add,hv,hz]

/-- The same WHOLE original restriction map on the genuine constructed normed ring copies. -/
def curveAnalyticNormedRestriction (basis : Module.Basis ι K[X] B) :
    U.CurveAnalyticAlgebra basis →+* V.CurveAnalyticAlgebra basis :=
  (V.curveAnalyticOriginalEquiv basis).symm.toRingHom.comp
    ((U.curveAnalyticRestriction V hVU).toRingHom.comp (U.curveAnalyticOriginalEquiv basis).toRingHom)

omit [Fintype ι] in
theorem curveAnalyticNormedRestriction_specialization (basis : Module.Basis ι K[X] B)
    (x : V.carrier) (v : U.CurveAnalyticAlgebra basis) :
    V.curveAnalyticNormedSpecialization basis x (U.curveAnalyticNormedRestriction V hVU basis v) =
      U.curveAnalyticNormedSpecialization basis ⟨x.1,hVU x.2⟩ v := by
  change (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.1.H)).symm
      (V.curveAnalyticSpecialization x
        ((U.curveAnalyticRestriction V hVU) (U.curveAnalyticOriginalEquiv basis v))) =
    (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.1.H)).symm
      (U.curveAnalyticSpecialization ⟨x.1,hVU x.2⟩ (U.curveAnalyticOriginalEquiv basis v))
  rw [U.curveAnalyticRestriction_specialization V hVU]

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
