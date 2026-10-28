import EnvelopeProperty.Potential.FiniteFreeAnalyticMaps
import EnvelopeProperty.Potential.CurveAnalyticFractions
import EnvelopeProperty.Potential.LineAffinoidSpectrum

/-! # Genuine bounded whole analytic curve points restrict to the whole original preimage -/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The original complete coefficient ring acts on the same whole analytic copy. -/
def curveAnalyticCoefficientMap (basis : Module.Basis ι K[X] B) :
    U.AnalyticFunctions →+* U.CurveAnalyticAlgebra basis := algebraMap _ _

omit [IsAlgClosed K] in
/-- This actual entire coefficient map is bounded, without positive-rank or nonzero-algebra assumptions. -/
theorem curveAnalyticCoefficientMap_isBounded (basis : Module.Basis ι K[X] B) :
    (U.curveAnalyticCoefficientMap basis).IsBounded :=
  FiniteFreeAnalyticCopy.coefficientHom_isBounded (U.curveAnalyticBasis basis)

/-- The actual original ground-field coefficient map in the whole analytic curve algebra. -/
def curveAnalyticCoefficients (basis : Module.Basis ι K[X] B) :
    K →+* U.CurveAnalyticAlgebra basis :=
  (U.curveAnalyticCoefficientMap basis).comp U.analyticCoefficients

/-- The genuine entire prescribed-base bounded spectrum of the actual whole analytic curve algebra. -/
abbrev CurveAnalyticBoundedSpectrum (basis : Module.Basis ι K[X] B) :=
  RelativeNormBoundedSpectrum w (U.curveAnalyticCoefficients basis)

/-- Every actual bounded whole point restricts to the actual bounded analytic coefficient point. -/
def curveAnalyticBasePoint (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) : U.AnalyticBoundedSpectrum :=
  RelativeNormBoundedSpectrum.boundedComap w U.analyticCoefficients
    (U.curveAnalyticCoefficientMap basis) (U.curveAnalyticCoefficientMap_isBounded basis) z

/-- The original entire curve algebra maps into its actual analytic scalar extension. -/
def curveAnalyticCurveMap (basis : Module.Basis ι K[X] B) : B →+* U.CurveAnalyticAlgebra basis :=
  (U.curveAnalyticOriginalEquiv basis).symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B →ₐ[K[X]] U.CurveAnalyticTensor B).toRingHom

omit [IsAlgClosed K] [Fintype ι] in
/-- The whole original polynomial triangle is preserved by the two actual algebra inclusions. -/
theorem curveAnalyticCurveMap_algebraMap (basis : Module.Basis ι K[X] B) (p : K[X]) :
    U.curveAnalyticCurveMap basis (algebraMap K[X] B p) =
      U.curveAnalyticCoefficientMap basis (U.polynomialAnalyticMap p) := by
  apply (U.curveAnalyticOriginalEquiv basis).injective
  change (1 : U.AnalyticFunctions) ⊗ₜ[K[X]] algebraMap K[X] B p =
    algebraMap K[X] U.AnalyticFunctions p ⊗ₜ[K[X]] (1 : B)
  exact (Algebra.TensorProduct.algebraMap_apply' p).symm.trans
    (Algebra.TensorProduct.algebraMap_apply p)

variable [Algebra K B] [IsScalarTower K K[X] B]

omit [IsAlgClosed K] [Fintype ι] in
/-- The very same original ground-field coefficients are preserved by the original curve map. -/
theorem curveAnalyticCurveMap_coefficients (basis : Module.Basis ι K[X] B) (a : K) :
    U.curveAnalyticCurveMap basis (algebraMap K B a) = U.curveAnalyticCoefficients basis a := by
  rw [IsScalarTower.algebraMap_apply K K[X] B,
    U.curveAnalyticCurveMap_algebraMap basis]
  change U.curveAnalyticCoefficientMap basis (U.polynomialAnalyticMap (Polynomial.C a)) = _
  rw [U.polynomialAnalyticMap_C]
  rfl

/-- Actual whole bounded points give actual whole original prescribed-base curve points. -/
def curveAnalyticSpectrumRestriction (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) : RelativeSpectrum w B :=
  ⟨Spectrum.comap (U.curveAnalyticCurveMap basis) z.1.1, fun a => by
    change z.1.1.val (U.curveAnalyticCurveMap basis (algebraMap K B a)) = w a
    rw [U.curveAnalyticCurveMap_coefficients basis]
    exact z.2 a⟩

/-- Its original polynomial base point is exactly the original affinoid point of the actual coefficient restriction. -/
theorem curveAnalyticSpectrumRestriction_base (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) :
    RelativeSpectrum.comap (IsScalarTower.toAlgHom K K[X] B) (U.curveAnalyticSpectrumRestriction basis z) =
      (U.analyticSpectrumHomeomorph (U.curveAnalyticBasePoint basis z)).1 := by
  apply RelativeSpectrum.ext_val
  intro p
  change z.1.1.val (U.curveAnalyticCurveMap basis (algebraMap K[X] B p)) = _
  rw [U.curveAnalyticCurveMap_algebraMap basis]
  exact U.analyticSpectrumHomeomorph_val_polynomial (U.curveAnalyticBasePoint basis z) p

/-- The actual whole original curve preimage of the original standard carrier. -/
abbrev CurvePreimage :=
  {y : RelativeSpectrum w B //
    RelativeSpectrum.comap (IsScalarTower.toAlgHom K K[X] B) y ∈ U.carrier}

/-- Whole bounded analytic curve points restrict into the entire original curve preimage. -/
def curveAnalyticPreimageRestriction (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) : U.CurvePreimage (B := B) :=
  ⟨U.curveAnalyticSpectrumRestriction basis z, by
    rw [U.curveAnalyticSpectrumRestriction_base basis z]
    exact (U.analyticSpectrumHomeomorph (U.curveAnalyticBasePoint basis z)).2⟩

/-- Every original curve function keeps precisely its original whole-ring restriction value. -/
theorem curveAnalyticPreimageRestriction_val (basis : Module.Basis ι K[X] B)
    (z : U.CurveAnalyticBoundedSpectrum basis) (b : B) :
    (U.curveAnalyticPreimageRestriction basis z).1.1.val b =
      z.1.1.val (U.curveAnalyticCurveMap basis b) := rfl

/-- The genuine whole restriction is continuous for the original evaluation topologies. -/
theorem continuous_curveAnalyticPreimageRestriction (basis : Module.Basis ι K[X] B) :
    Continuous (U.curveAnalyticPreimageRestriction basis) := by
  apply Continuous.subtype_mk
  rw [RelativeSpectrum.continuous_iff]
  intro b
  exact (Spectrum.continuous_val_apply (U.curveAnalyticCurveMap basis b)).comp
    (continuous_subtype_val.comp continuous_subtype_val)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
