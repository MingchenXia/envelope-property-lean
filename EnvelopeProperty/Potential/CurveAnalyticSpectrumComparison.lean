import EnvelopeProperty.Potential.CurveAnalyticSpectrumLifts

/-!
# The actual whole bounded analytic curve spectrum is the original curve preimage

Original polynomial test uniqueness for continuous analytic coefficient maps
and whole tensor induction recover every actual bounded point. The true
compact bounded spectrum and the original Hausdorff point topology then give
the whole homeomorphism. No spectrum, evaluator or gluing certificate is input.
-/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- The genuine completed residue embedding induced by the actual original curve map. -/
def curveRestrictedResidueMap (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) :
    Spectrum.H (U.curveAnalyticPreimageRestriction basis z).1.1 →+* Spectrum.H z.1.1 :=
  Spectrum.H.map (U.curveAnalyticCurveMap basis) rfl

/-- This actual embedding preserves the entire original completed-field norm. -/
theorem norm_curveRestrictedResidueMap (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis)
    (a : Spectrum.H (U.curveAnalyticPreimageRestriction basis z).1.1) :
    ‖U.curveRestrictedResidueMap basis z a‖ = ‖a‖ :=
  Spectrum.H.norm_map (U.curveAnalyticCurveMap basis) rfl a

/-- The actual completed residue embedding retains every original whole curve function. -/
theorem curveRestrictedResidueMap_toH (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) (b : B) :
    U.curveRestrictedResidueMap basis z
      (Spectrum.toH (U.curveAnalyticPreimageRestriction basis z).1.1 b) =
        Spectrum.toH z.1.1 (U.curveAnalyticCurveMap basis b) :=
  Spectrum.H.map_toH (U.curveAnalyticCurveMap basis) rfl b

/-- Density and actual localization uniqueness identify the ENTIRE analytic coefficient evaluator. -/
theorem curveBoundedCoefficientEvaluation_eq (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) :
    (Spectrum.toH z.1.1).comp (U.curveAnalyticCoefficientMap basis) =
      (U.curveRestrictedResidueMap basis z).comp
        (U.curveOriginalCoefficientEvaluation (U.curveAnalyticPreimageRestriction basis z)) := by
  apply U.analyticRingHom_ext_on_polynomials
  · exact (Spectrum.lipschitz_toH_of_isNormBounded z.1.1 z.1.2).continuous.comp
      (FiniteFreeAnalyticCopy.continuous_coefficientHom (U.curveAnalyticBasis basis))
  · exact (Spectrum.H.isometry_map (U.curveAnalyticCurveMap basis) rfl).continuous.comp
      (U.continuous_curveOriginalCoefficientEvaluation (U.curveAnalyticPreimageRestriction basis z))
  · intro p
    change Spectrum.toH z.1.1 (U.curveAnalyticCoefficientMap basis (U.polynomialAnalyticMap p)) =
      U.curveRestrictedResidueMap basis z
        (U.curveOriginalCoefficientEvaluation (U.curveAnalyticPreimageRestriction basis z)
          (U.polynomialAnalyticMap p))
    rw [U.curveOriginalCoefficientEvaluation_polynomial, U.curveRestrictedResidueMap_toH,
      U.curveAnalyticCurveMap_algebraMap]

/-- Whole tensor induction identifies every actual bounded whole-ring evaluator through the original H(y). -/
theorem curveBoundedOriginalEvaluation_eq (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) (a : U.CurveAnalyticAlgebra basis) :
    Spectrum.toH z.1.1 a =
      U.curveRestrictedResidueMap basis z
        (U.curveOriginalEvaluation basis (U.curveAnalyticPreimageRestriction basis z) a) := by
  let y := U.curveAnalyticPreimageRestriction basis z
  have hcoef := U.curveBoundedCoefficientEvaluation_eq basis z
  have ht (t : U.CurveAnalyticTensor B) :
      Spectrum.toH z.1.1 ((U.curveAnalyticOriginalEquiv basis).symm t) =
        U.curveRestrictedResidueMap basis z (U.curveOriginalTensorEvaluation y t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul c b =>
      have he : (U.curveAnalyticOriginalEquiv basis).symm (c ⊗ₜ[K[X]] b) =
          U.curveAnalyticCoefficientMap basis c * U.curveAnalyticCurveMap basis b := by
        apply (U.curveAnalyticOriginalEquiv basis).injective
        change c ⊗ₜ[K[X]] b =
          (c ⊗ₜ[K[X]] (1 : B)) * ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he, map_mul, U.curveOriginalTensorEvaluation_tmul, map_mul]
      exact congrArg₂ (· * ·) (RingHom.congr_fun hcoef c)
        (U.curveRestrictedResidueMap_toH basis z b).symm
  calc
    _ = U.curveRestrictedResidueMap basis z
        (U.curveOriginalTensorEvaluation y (U.curveAnalyticOriginalEquiv basis a)) := by
      simpa only [AlgEquiv.symm_apply_apply] using ht (U.curveAnalyticOriginalEquiv basis a)
    _ = _ := rfl

/-- The actual whole lift recovers EVERY entire bounded analytic curve point. -/
theorem curveOriginalBoundedPoint_preimageRestriction (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) :
    U.curveOriginalBoundedPoint basis (U.curveAnalyticPreimageRestriction basis z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  change ‖U.curveOriginalEvaluation basis (U.curveAnalyticPreimageRestriction basis z) a‖₊ = z.1.1.val a
  calc
    _ = ‖U.curveRestrictedResidueMap basis z
        (U.curveOriginalEvaluation basis (U.curveAnalyticPreimageRestriction basis z) a)‖₊ :=
      (NNReal.eq (U.norm_curveRestrictedResidueMap basis z _)).symm
    _ = ‖Spectrum.toH z.1.1 a‖₊ := congrArg nnnorm (U.curveBoundedOriginalEvaluation_eq basis z a).symm
    _ = _ := Spectrum.nnnorm_toH z.1.1 a

/-- The genuine whole bounded analytic spectrum is the ENTIRE original curve preimage. -/
def curveAnalyticSpectrumHomeomorph (basis : Module.Basis ι K[X] B) :
    U.CurveAnalyticBoundedSpectrum basis ≃ₜ U.CurvePreimage (B := B) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.mk (U.curveAnalyticPreimageRestriction basis) (U.curveOriginalBoundedPoint basis)
      (U.curveOriginalBoundedPoint_preimageRestriction basis)
      (U.curveAnalyticPreimageRestriction_originalBoundedPoint basis))
    (U.continuous_curveAnalyticPreimageRestriction basis)

/-- Every original curve function is retained by the actual whole homeomorphism. -/
theorem curveAnalyticSpectrumHomeomorph_val (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) (b : B) :
    (U.curveAnalyticSpectrumHomeomorph basis z).1.1.val b =
      z.1.1.val (U.curveAnalyticCurveMap basis b) := rfl

/-- Its inverse retains the actual evaluator of EVERY whole analytic element in the SAME original H(y). -/
theorem curveAnalyticSpectrumHomeomorph_symm_val (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (a : U.CurveAnalyticAlgebra basis) :
    ((U.curveAnalyticSpectrumHomeomorph basis).symm y).1.1.val a =
      ‖U.curveOriginalEvaluation basis y a‖₊ := rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
