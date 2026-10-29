import EnvelopeProperty.Potential.LineAnalyticFractionBounds

/-! # Exact original coefficients of whole analytic curve fractions and their defects -/

open scoped NNReal Polynomial TensorProduct
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

omit [IsAlgClosed K] in
theorem curveAnalyticBasis_coefficient_tmul (r : U.AnalyticFunctions) (c : B) (i : ι) :
    (U.curveAnalyticBasis basis).equivFun (r ⊗ₜ[K[X]] c) i =
      U.polynomialAnalyticMap (basis.equivFun c i)*r := by
  simpa only [curveAnalyticBasis,Module.Basis.equivFun_apply,Algebra.smul_def,
    U.algebraMap_polynomial_analytic] using basis.baseChange_repr_tmul U.AnalyticFunctions r c i

omit [IsAlgClosed K] in
theorem curveAnalyticBasis_multiplication_coefficient (i j k : ι) :
    (U.curveAnalyticBasis basis).equivFun
      (U.curveAnalyticBasis basis i*U.curveAnalyticBasis basis j) k =
      U.polynomialAnalyticMap (basis.equivFun (basis i*basis j) k) := by
  rw [U.curveAnalyticBasis_apply,U.curveAnalyticBasis_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,U.curveAnalyticBasis_coefficient_tmul,mul_one]

omit [IsAlgClosed K] in
theorem curveAnalyticFraction_coefficient (d : K[X]) (c : B) (i : ι) :
    (U.curveAnalyticBasis basis).equivFun
      (U.curveAnalyticOriginalEquiv basis (U.curveAnalyticFraction basis d c)) i =
      U.polynomialAnalyticFraction (basis.equivFun c i) d := by
  rw [curveAnalyticFraction,AlgEquiv.apply_symm_apply,U.curveAnalyticBasis_coefficient_tmul]
  rfl

private theorem inverse_polynomial_square (d : K[X])
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) :
    Ring.inverse (U.polynomialAnalyticMap (d^2)) =
      (Ring.inverse (U.polynomialAnalyticMap d))^2 := by
  let a := U.polynomialAnalyticMap d
  have ha : IsUnit a := U.isUnit_polynomialAnalyticMap d hd
  have h : a^2*(Ring.inverse a)^2 = 1 := by
    rw [← mul_pow,Ring.mul_inverse_cancel a ha,one_pow]
  have hinv : a^2*Ring.inverse (a^2) = 1 := Ring.mul_inverse_cancel _ (ha.pow 2)
  have he : Ring.inverse (a^2) = (Ring.inverse a)^2 := calc
    _ = 1*Ring.inverse (a^2) := (one_mul _).symm
    _ = (a^2*(Ring.inverse a)^2)*Ring.inverse (a^2) := by rw [h]
    _ = (a^2*Ring.inverse (a^2))*(Ring.inverse a)^2 := by ring
    _ = _ := by rw [hinv,one_mul]
  simpa only [map_pow] using he

omit [Fintype ι] in
theorem curveAnalyticFraction_defect_tensor (d : K[X]) (c : B)
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) :
    U.curveAnalyticOriginalEquiv basis
      ((U.curveAnalyticFraction basis d c)^2-U.curveAnalyticFraction basis d c) =
      Ring.inverse (U.polynomialAnalyticMap (d^2)) ⊗ₜ[K[X]]
        (c^2-algebraMap K[X] B d*c) := by
  let a := Ring.inverse (U.polynomialAnalyticMap d)
  have ha : U.polynomialAnalyticMap d*a = 1 :=
    Ring.mul_inverse_cancel _ (U.isUnit_polynomialAnalyticMap d hd)
  have had : U.polynomialAnalyticMap d*a^2 = a := by
    calc
      _ = (U.polynomialAnalyticMap d*a)*a := by ring
      _ = a := by rw [ha,one_mul]
  rw [map_sub,map_pow,curveAnalyticFraction,AlgEquiv.apply_symm_apply,
    U.inverse_polynomial_square d hd,pow_two,Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sub]
  simp only [pow_two]
  congr 1
  change a ⊗ₜ[K[X]] c = (a*a) ⊗ₜ[K[X]] (algebraMap K[X] B d*c)
  rw [← Algebra.smul_def d c,TensorProduct.tmul_smul,TensorProduct.smul_tmul',
    Algebra.smul_def,U.algebraMap_polynomial_analytic]
  congr 1
  simpa only [pow_two] using had.symm

theorem curveAnalyticFraction_defect_coefficient (d : K[X]) (c : B)
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) (i : ι) :
    (U.curveAnalyticBasis basis).equivFun
      (U.curveAnalyticOriginalEquiv basis
        ((U.curveAnalyticFraction basis d c)^2-U.curveAnalyticFraction basis d c)) i =
      U.polynomialAnalyticFraction (basis.equivFun (c^2-algebraMap K[X] B d*c) i) (d^2) := by
  rw [U.curveAnalyticFraction_defect_tensor basis d c hd,U.curveAnalyticBasis_coefficient_tmul]
  rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
