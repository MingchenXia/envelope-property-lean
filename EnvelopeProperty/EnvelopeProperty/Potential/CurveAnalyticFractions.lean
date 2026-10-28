import EnvelopeProperty.Potential.CurveFiniteFreeAnalyticAlgebra
import EnvelopeProperty.Potential.LineAffinoidBasis
import EnvelopeProperty.Berkovich.SpectrumFibrePeak

/-! # Actual original fractions and whole completed-fibre specialization -/

open scoped NNReal Polynomial TensorProduct Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

/-- The regularity locus is DERIVED from the original polynomial and contains an actual
standard-affinoid neighbourhood of every original point where the denominator is nonzero. -/
theorem fc_exists_standardAffinoid_polynomial_ne_zero
    (x : RelativeSpectrum w K[X]) (d : K[X]) (hd : x.1.val d ≠ 0) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, x ∈ interior U.carrier ∧
      ∀ y ∈ U.carrier, y.1.val d ≠ 0 := by
  have hopen : IsOpen {y : RelativeSpectrum w K[X] | 0 < y.1.val d} :=
    isOpen_lt continuous_const (continuous_val_apply d)
  obtain ⟨m,U,hx,hU⟩ := fc_exists_standardAffinoid_nhds x
    (hopen.mem_nhds (show x ∈ {y : RelativeSpectrum w K[X] | 0 < y.1.val d} from
      pos_iff_ne_zero.mpr hd))
  exact ⟨m,U,hx,fun y hy => ne_of_gt (hU hy)⟩

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- The ENTIRE completed analytic coefficient evaluator retains the original polynomial action. -/
def polynomialAnalyticEvaluation (x : U.carrier) : U.AnalyticFunctions →ₐ[K[X]] x.1.1.H where
  __ := U.evaluationToH x
  commutes' p := by
    change U.evaluationToH x (U.polynomialAnalyticMap p) = x.1.1.toH p
    rw [polynomialAnalyticMap,RingHom.comp_apply,U.evaluationToH_rationalMap,
      U.rationalEvaluation_polynomial]

/-- The actual unit criterion derives denominator invertibility from original nonvanishing. -/
theorem isUnit_polynomialAnalyticMap (d : K[X])
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) : IsUnit (U.polynomialAnalyticMap d) := by
  apply (U.analyticFunctions_isUnit_iff _).mpr
  intro x
  change U.analyticValue (U.rationalMap (algebraMap K[X] U.RationalFunctions d)) x ≠ 0
  rw [U.analyticValue_rationalMap,U.rationalValue_polynomial]
  exact hd x

theorem evaluationToH_inverse_polynomial (d : K[X])
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) (x : U.carrier) :
    U.evaluationToH x (Ring.inverse (U.polynomialAnalyticMap d)) = (x.1.1.toH d)⁻¹ := by
  have he := congrArg (U.evaluationToH x)
    (Ring.mul_inverse_cancel (U.polynomialAnalyticMap d) (U.isUnit_polynomialAnalyticMap d hd))
  rw [map_mul,map_one] at he
  have hev : U.evaluationToH x (U.polynomialAnalyticMap d) = x.1.1.toH d :=
    (U.polynomialAnalyticEvaluation x).commutes d
  rw [hev] at he
  exact eq_inv_of_mul_eq_one_right he

variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The whole original tensor specialization to the SAME actual completed fibre. -/
def curveAnalyticSpecialization (x : U.carrier) :
    U.CurveAnalyticTensor B →ₐ[K[X]] x.1.1.H ⊗[K[X]] B :=
  Algebra.TensorProduct.map (U.polynomialAnalyticEvaluation x) (AlgHom.id K[X] B)

/-- An actual original fraction in the genuine whole analytic neighbourhood algebra. -/
def curveAnalyticFraction (basis : Module.Basis ι K[X] B) (d : K[X]) (c : B) :
    U.CurveAnalyticAlgebra basis :=
  (U.curveAnalyticOriginalEquiv basis).symm
    (Ring.inverse (U.polynomialAnalyticMap d) ⊗ₜ[K[X]] c)

omit [Fintype ι] in
theorem curveAnalyticFraction_specialization (basis : Module.Basis ι K[X] B) (d : K[X]) (c : B)
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) (x : U.carrier) :
    U.curveAnalyticSpecialization (B := B) x
      (U.curveAnalyticOriginalEquiv basis (U.curveAnalyticFraction basis d c)) =
      Spectrum.fractionTensor x.1.1 d c := by
  rw [curveAnalyticFraction,AlgEquiv.apply_symm_apply,curveAnalyticSpecialization,
    Algebra.TensorProduct.map_tmul]
  change U.evaluationToH x (Ring.inverse (U.polynomialAnalyticMap d)) ⊗ₜ[K[X]] c = _
  rw [U.evaluationToH_inverse_polynomial d hd x]
  rfl

end FCStandardAffinoid
end EnvelopeProperty.Berkovich.RelativeSpectrum
