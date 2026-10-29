import EnvelopeProperty.Potential.CurveAnalyticBasisCoefficients

/-! # Norm control of the entire original analytic tensor specialization -/

open scoped NNReal Polynomial TensorProduct
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- Every whole analytic coefficient specializes to its original value in the SAME H(x). -/
theorem curveAnalyticSpecialization_coefficient (x : U.carrier) (v : U.CurveAnalyticTensor B) (i : ι) :
    (basis.baseChange x.1.1.H).equivFun (U.curveAnalyticSpecialization x v) i =
      U.evaluationToH x ((U.curveAnalyticBasis basis).equivFun v i) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero,Pi.zero_apply]
  | tmul r c =>
      rw [curveAnalyticSpecialization,Algebra.TensorProduct.map_tmul,
        U.curveAnalyticBasis_coefficient_tmul,map_mul]
      change (basis.baseChange x.1.1.H).equivFun
        (U.evaluationToH x r ⊗ₜ[K[X]] c) i = _
      have hc := basis.baseChange_repr_tmul x.1.1.H (U.evaluationToH x r) c i
      have hp : U.evaluationToH x (U.polynomialAnalyticMap (basis.equivFun c i)) =
          x.1.1.toH (basis.equivFun c i) :=
        (U.polynomialAnalyticEvaluation x).commutes _
      rw [hp]
      simpa only [Module.Basis.equivFun_apply,Algebra.smul_def,Spectrum.algebraMap_H] using hc
  | add v z hv hz =>
      simp only [map_add,Pi.add_apply,hv,hz]

/-- No certificate is input: actual coefficient evaluations are contractive. -/
theorem curveAnalyticSpecialization_coefficientNorm_le (x : U.carrier) (v : U.CurveAnalyticTensor B) :
    (basis.baseChange x.1.1.H).fcCoefficientNorm (U.curveAnalyticSpecialization x v) ≤
      (U.curveAnalyticBasis basis).fcCoefficientNorm v := by
  apply (pi_norm_le_iff_of_nonneg ((U.curveAnalyticBasis basis).fcCoefficientNorm_nonneg v)).mpr
  intro i
  rw [U.curveAnalyticSpecialization_coefficient]
  have he : ‖U.evaluationToH x ((U.curveAnalyticBasis basis).equivFun v i)‖ ≤
      ‖(U.curveAnalyticBasis basis).equivFun v i‖ :=
    U.nnnorm_evaluationToH_le x _
  exact he.trans (norm_le_pi_norm _ i)

/-- The entire specialization, in the genuine constructed normed copies. -/
def curveAnalyticNormedSpecialization (x : U.carrier) :
    U.CurveAnalyticAlgebra basis →+* FiniteFreeAnalyticCopy (basis.baseChange x.1.1.H) :=
  (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.1.H)).symm.toRingHom.comp
    ((U.curveAnalyticSpecialization x).toRingHom.comp (U.curveAnalyticOriginalEquiv basis).toRingHom)

/-- The actual whole specialization ring-norm bound follows from the original three norm
comparisons, retaining every original coefficient and nilpotent direction. -/
theorem norm_curveAnalyticNormedSpecialization_le (x : U.carrier) (v : U.CurveAnalyticAlgebra basis) :
    ‖U.curveAnalyticNormedSpecialization basis x v‖ ≤
      ((basis.baseChange x.1.1.H).fcMultiplicationBound*
        (U.curveAnalyticBasis basis).fcCoefficientNorm 1)*‖v‖ := by
  change (basis.baseChange x.1.1.H).fcCoefficientRingNorm
      (U.curveAnalyticSpecialization x (U.curveAnalyticOriginalEquiv basis v)) ≤ _
  calc
    _ ≤ (basis.baseChange x.1.1.H).fcMultiplicationBound*
        (basis.baseChange x.1.1.H).fcCoefficientNorm
          (U.curveAnalyticSpecialization x (U.curveAnalyticOriginalEquiv basis v)) :=
      (basis.baseChange x.1.1.H).fcCoefficientRingNorm_le _
    _ ≤ (basis.baseChange x.1.1.H).fcMultiplicationBound*
        (U.curveAnalyticBasis basis).fcCoefficientNorm (U.curveAnalyticOriginalEquiv basis v) :=
      mul_le_mul_of_nonneg_left (U.curveAnalyticSpecialization_coefficientNorm_le basis x _)
        (basis.baseChange x.1.1.H).fcMultiplicationBound_pos.le
    _ ≤ (basis.baseChange x.1.1.H).fcMultiplicationBound*
        ((U.curveAnalyticBasis basis).fcCoefficientNorm 1*‖v‖) :=
      mul_le_mul_of_nonneg_left ((U.curveAnalyticBasis basis).fcCoefficientNorm_le _)
        (basis.baseChange x.1.1.H).fcMultiplicationBound_pos.le
    _ = _ := by ring

/-- Actual Lipschitz continuity is a consequence of the whole original norm estimate. -/
theorem lipschitz_curveAnalyticNormedSpecialization (x : U.carrier) :
    LipschitzWith ⟨(basis.baseChange x.1.1.H).fcMultiplicationBound*
      (U.curveAnalyticBasis basis).fcCoefficientNorm 1,
      mul_nonneg (basis.baseChange x.1.1.H).fcMultiplicationBound_pos.le
        ((U.curveAnalyticBasis basis).fcCoefficientNorm_nonneg 1)⟩
      (U.curveAnalyticNormedSpecialization basis x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v z
  simp only [dist_eq_norm]
  change ‖U.curveAnalyticNormedSpecialization basis x v-
    U.curveAnalyticNormedSpecialization basis x z‖ ≤
    ((basis.baseChange x.1.1.H).fcMultiplicationBound*
      (U.curveAnalyticBasis basis).fcCoefficientNorm 1)*‖v-z‖
  rw [← (U.curveAnalyticNormedSpecialization basis x).map_sub]
  exact U.norm_curveAnalyticNormedSpecialization_le basis x (v-z)

theorem continuous_curveAnalyticNormedSpecialization (x : U.carrier) :
    Continuous (U.curveAnalyticNormedSpecialization basis x) :=
  (U.lipschitz_curveAnalyticNormedSpecialization basis x).continuous

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
