import EnvelopeProperty.Potential.CurveAnalyticSpectrumMaps

/-!
# Whole bounded analytic curve points from actual original curve points

The entire tensor evaluator is constructed in the SAME original H(y).
The genuine finite basis supplies its norm bound, and the proved BGR power
argument gives point contractivity. No evaluator, boundedness or selected-piece
certificate is supplied as an input.
-/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- The actual original polynomial base point of a whole original curve-preimage point. -/
def curveOriginalBasePoint (y : U.CurvePreimage (B := B)) : U.carrier :=
  ⟨RelativeSpectrum.comap (IsScalarTower.toAlgHom K K[X] B) y.1, y.2⟩

/-- Every analytic coefficient evaluates in the SAME original completed residue field H(y). -/
def curveOriginalCoefficientEvaluation (y : U.CurvePreimage (B := B)) :
    U.AnalyticFunctions →+* Spectrum.H y.1.1 :=
  (Spectrum.H.map (algebraMap K[X] B)
    (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)).comp
      (U.evaluationToH (U.curveOriginalBasePoint y))

/-- The entire original polynomial action is retained in the original H(y). -/
theorem curveOriginalCoefficientEvaluation_polynomial (y : U.CurvePreimage (B := B)) (p : K[X]) :
    U.curveOriginalCoefficientEvaluation y (U.polynomialAnalyticMap p) =
      Spectrum.toH y.1.1 (algebraMap K[X] B p) := by
  have h := (U.polynomialAnalyticEvaluation (U.curveOriginalBasePoint y)).commutes p
  have hh := congrArg (Spectrum.H.map (algebraMap K[X] B)
    (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)) h
  exact hh.trans (Spectrum.H.map_toH (algebraMap K[X] B)
    (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1) p)

/-- The coefficient evaluator is genuinely continuous through the actual complete-field embedding. -/
theorem continuous_curveOriginalCoefficientEvaluation (y : U.CurvePreimage (B := B)) :
    Continuous (U.curveOriginalCoefficientEvaluation y) :=
  (Spectrum.H.isometry_map (algebraMap K[X] B) rfl).continuous.comp
    (U.continuous_evaluationToH (U.curveOriginalBasePoint y))

/-- Its actual norm is bounded by the genuine analytic coefficient norm. -/
theorem norm_curveOriginalCoefficientEvaluation_le (y : U.CurvePreimage (B := B))
    (a : U.AnalyticFunctions) : ‖U.curveOriginalCoefficientEvaluation y a‖ ≤ ‖a‖ := by
  exact (Spectrum.H.norm_map (algebraMap K[X] B)
    (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)
    (U.evaluationToH (U.curveOriginalBasePoint y) a)).le.trans
      (U.nnnorm_evaluationToH_le (U.curveOriginalBasePoint y) a)

/-- The actual entire tensor evaluator into the SAME H(y), constructed from the true coefficient triangle. -/
def curveOriginalTensorEvaluation (y : U.CurvePreimage (B := B)) :
    U.CurveAnalyticTensor B →+* Spectrum.H y.1.1 := by
  letI : Algebra K[X] (Spectrum.H y.1.1) :=
    ((Spectrum.toH y.1.1).comp (algebraMap K[X] B)).toAlgebra
  exact (Algebra.TensorProduct.productMap
    { U.curveOriginalCoefficientEvaluation y with
      commutes' p := U.curveOriginalCoefficientEvaluation_polynomial y p }
    { Spectrum.toH y.1.1 with commutes' _ := rfl }).toRingHom

/-- Every analytic coefficient and original curve element keeps its exact original tensor evaluation. -/
theorem curveOriginalTensorEvaluation_tmul (y : U.CurvePreimage (B := B))
    (a : U.AnalyticFunctions) (b : B) :
    U.curveOriginalTensorEvaluation y (a ⊗ₜ[K[X]] b) =
      U.curveOriginalCoefficientEvaluation y a * Spectrum.toH y.1.1 b := rfl

/-- The evaluator on the actual normed WHOLE analytic curve algebra. -/
def curveOriginalEvaluation (basis : Module.Basis ι K[X] B) (y : U.CurvePreimage (B := B)) :
    U.CurveAnalyticAlgebra basis →+* Spectrum.H y.1.1 :=
  (U.curveOriginalTensorEvaluation y).comp (U.curveAnalyticOriginalEquiv basis).toRingHom

omit [Fintype ι] in
/-- The same entire original curve map returns every actual original H(y)-value. -/
theorem curveOriginalEvaluation_curveMap (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (b : B) :
    U.curveOriginalEvaluation basis y (U.curveAnalyticCurveMap basis b) = Spectrum.toH y.1.1 b := by
  change U.curveOriginalTensorEvaluation y ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b) = _
  rw [U.curveOriginalTensorEvaluation_tmul, map_one, one_mul]

omit [Fintype ι] in
/-- The entire original analytic coefficient map also has exactly its constructed H(y)-evaluation. -/
theorem curveOriginalEvaluation_coefficientMap (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (a : U.AnalyticFunctions) :
    U.curveOriginalEvaluation basis y (U.curveAnalyticCoefficientMap basis a) =
      U.curveOriginalCoefficientEvaluation y a := by
  change U.curveOriginalTensorEvaluation y (a ⊗ₜ[K[X]] (1 : B)) = _
  rw [U.curveOriginalTensorEvaluation_tmul, map_one, mul_one]

/-- The actual WHOLE evaluator is the finite sum of its original basis coefficients and original H(y)-basis values. -/
theorem curveOriginalTensorEvaluation_basis (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (a : U.CurveAnalyticTensor B) :
    U.curveOriginalTensorEvaluation y a =
      ∑ i, U.curveOriginalCoefficientEvaluation y ((U.curveAnalyticBasis basis).equivFun a i) *
        Spectrum.toH y.1.1 (basis i) := by
  have ha : a = ∑ i, ((U.curveAnalyticBasis basis).equivFun a i) ⊗ₜ[K[X]] basis i := by
    simpa only [Module.Basis.equivFun_apply, U.curveAnalyticBasis_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      ((U.curveAnalyticBasis basis).sum_repr a).symm
  calc
    _ = U.curveOriginalTensorEvaluation y
        (∑ i, ((U.curveAnalyticBasis basis).equivFun a i) ⊗ₜ[K[X]] basis i) :=
      congrArg (U.curveOriginalTensorEvaluation y) ha
    _ = _ := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => U.curveOriginalTensorEvaluation_tmul y _ _)

/-- A genuine finite ORIGINAL basis bounds every actual whole evaluation by the actual coefficient norm. -/
theorem norm_curveOriginalEvaluation_coefficient_le (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (a : U.CurveAnalyticAlgebra basis) :
    ‖U.curveOriginalEvaluation basis y a‖ ≤
      (∑ i, ‖Spectrum.toH y.1.1 (basis i)‖) *
        (U.curveAnalyticBasis basis).fcCoefficientNorm (U.curveAnalyticOriginalEquiv basis a) := by
  change ‖U.curveOriginalTensorEvaluation y (U.curveAnalyticOriginalEquiv basis a)‖ ≤ _
  rw [U.curveOriginalTensorEvaluation_basis basis y]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, (U.curveAnalyticBasis basis).fcCoefficientNorm (U.curveAnalyticOriginalEquiv basis a) *
        ‖Spectrum.toH y.1.1 (basis i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((U.norm_curveOriginalCoefficientEvaluation_le y _).trans
          ((U.curveAnalyticBasis basis).norm_equivFun_le_fcCoefficientNorm _ i)) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- Actual whole evaluation is bounded in the constructed entire curve ring norm. -/
theorem curveOriginalEvaluation_isBounded (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) : (U.curveOriginalEvaluation basis y).IsBounded := by
  let D := (∑ i, ‖Spectrum.toH y.1.1 (basis i)‖) * (U.curveAnalyticBasis basis).fcCoefficientNorm 1
  have hD : 0 ≤ D := mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    ((U.curveAnalyticBasis basis).fcCoefficientNorm_nonneg 1)
  refine ⟨1 + D, by linarith, fun a => ?_⟩
  calc
    _ ≤ (∑ i, ‖Spectrum.toH y.1.1 (basis i)‖) *
        (U.curveAnalyticBasis basis).fcCoefficientNorm (U.curveAnalyticOriginalEquiv basis a) :=
      U.norm_curveOriginalEvaluation_coefficient_le basis y a
    _ ≤ (∑ i, ‖Spectrum.toH y.1.1 (basis i)‖) *
        ((U.curveAnalyticBasis basis).fcCoefficientNorm 1 * ‖a‖) :=
      mul_le_mul_of_nonneg_left ((U.curveAnalyticBasis basis).fcCoefficientNorm_le _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = D * ‖a‖ := by dsimp only [D]; ring
    _ ≤ (1 + D) * ‖a‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- Every actual original whole curve-preimage point supplies a genuine whole bounded analytic point. -/
def curveOriginalBoundedPoint (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) : U.CurveAnalyticBoundedSpectrum basis :=
  ⟨⟨Spectrum.comap (U.curveOriginalEvaluation basis y)
    (Spectrum.ofValuation (NormedField.valuation (K := Spectrum.H y.1.1))),
    Spectrum.isNormBounded_comap_of_isBounded _ (U.curveOriginalEvaluation_isBounded basis y)
      _ (fun _ => le_rfl)⟩, fun a => by
    change ‖U.curveOriginalEvaluation basis y (U.curveAnalyticCoefficients basis a)‖₊ = w a
    rw [← U.curveAnalyticCurveMap_coefficients basis a, U.curveOriginalEvaluation_curveMap basis y,
      Spectrum.nnnorm_toH]
    exact y.1.2 a⟩

/-- The actual lift recovers EVERY original curve value and thus the original whole preimage point. -/
theorem curveAnalyticPreimageRestriction_originalBoundedPoint (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) :
    U.curveAnalyticPreimageRestriction basis (U.curveOriginalBoundedPoint basis y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro b
  change ‖U.curveOriginalEvaluation basis y (U.curveAnalyticCurveMap basis b)‖₊ = y.1.1.val b
  rw [U.curveOriginalEvaluation_curveMap basis y, Spectrum.nnnorm_toH]

/-- The true whole bounded-spectrum restriction is onto the ENTIRE original curve preimage. -/
theorem curveAnalyticPreimageRestriction_surjective (basis : Module.Basis ι K[X] B) :
    Function.Surjective (U.curveAnalyticPreimageRestriction basis) :=
  fun y => ⟨U.curveOriginalBoundedPoint basis y,
    U.curveAnalyticPreimageRestriction_originalBoundedPoint basis y⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
