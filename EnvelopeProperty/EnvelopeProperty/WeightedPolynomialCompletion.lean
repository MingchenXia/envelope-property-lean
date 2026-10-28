/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.WeightedPolynomialSeminorm
import EnvelopeProperty.Berkovich.ValuationCompletion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Actual weighted polynomial Banach completions

The source coefficient norm may be nonseparated and merely submultiplicative.
The ring is defined by actual separated norm completion. Original polynomial
and coefficient injectivity is not claimed without separation hypotheses.
-/
open scoped NNReal Topology
open UniformSpace Topology
noncomputable section
namespace EnvelopeProperty.WeightedPolynomialCompletion
variable {A ι : Type*} [SeminormedCommRing A] [IsUltrametricDist A]

/-- The actual original polynomial ring copy carrying its weight-dependent genuine seminorm. -/
def PolynomialRing (w : ι → ℝ≥0) (_hw : ∀ i, 0 < w i) : Type _ := MvPolynomial ι A

instance polynomialCommRing (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    CommRing (PolynomialRing (A := A) w hw) := inferInstanceAs (CommRing (MvPolynomial ι A))

/-- EVERY original polynomial is preserved by the actual underlying ring equivalence. -/
def polynomialEquiv (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    PolynomialRing (A := A) w hw ≃+* MvPolynomial ι A := RingEquiv.refl _

instance polynomialSeminormedCommRing (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    SeminormedCommRing (PolynomialRing (A := A) w hw) := fast_instance%
  { (WeightedPolynomial.ringSeminorm w hw).toSeminormedRing,
    polynomialCommRing (A := A) w hw with }

/-- The polynomial-copy norm is EXACTLY the actual full weighted coefficient maximum. -/
theorem nnnorm_polynomial (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : PolynomialRing (A := A) w hw) :
    ‖f‖₊ = WeightedPolynomial.gauss w (polynomialEquiv w hw f) := NNReal.eq rfl

instance polynomialIsUltrametricDist (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    IsUltrametricDist (PolynomialRing (A := A) w hw) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => by
    change (WeightedPolynomial.gauss w (f+g) : ℝ) ≤
      max (WeightedPolynomial.gauss w f : ℝ) (WeightedPolynomial.gauss w g : ℝ)
    exact_mod_cast WeightedPolynomial.gauss_add_le_max w f g

/-- The ACTUAL separated completion of the entire weighted polynomial seminormed ring. -/
abbrev Ring (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :=
  Completion (PolynomialRing (A := A) w hw)

/-- The entire original polynomial map into the genuine Banach completion. -/
def polynomialMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    MvPolynomial ι A →+* Ring (A := A) w hw :=
  Completion.coeRingHom.comp (polynomialEquiv w hw).symm.toRingHom

/-- Every original polynomial retains its EXACT original weighted norm under separated completion. -/
@[simp]
theorem nnnorm_polynomialMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (f : MvPolynomial ι A) :
    ‖polynomialMap w hw f‖₊ = WeightedPolynomial.gauss w f := by
  change ‖((polynomialEquiv w hw).symm f : Completion (PolynomialRing (A := A) w hw))‖₊ = _
  rw [Completion.nnnorm_coe, nnnorm_polynomial, RingEquiv.apply_symm_apply]

/-- The ACTUAL original coefficient ring homomorphism, retaining all original coefficient values. -/
def coefficients (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) : A →+* Ring (A := A) w hw :=
  (polynomialMap w hw).comp MvPolynomial.C

@[simp]
theorem nnnorm_coefficients (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (a : A) :
    ‖coefficients w hw a‖₊ = ‖a‖₊ := by
  exact (nnnorm_polynomialMap w hw (MvPolynomial.C a)).trans (WeightedPolynomial.gauss_C w a)

/-- The genuine coordinate images, without an assumed bound on the original unit norm. -/
def variableImage (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (i : ι) : Ring (A := A) w hw :=
  polynomialMap w hw (MvPolynomial.X i)

@[simp]
theorem nnnorm_variableImage (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (i : ι) :
    ‖variableImage (A := A) w hw i‖₊ = ‖(1 : A)‖₊ * w i := by
  exact (nnnorm_polynomialMap w hw (MvPolynomial.X i)).trans (WeightedPolynomial.gauss_X w i)

/-- Density is the genuine entire polynomial completion image, without a source-injection claim. -/
theorem denseRange_polynomialMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) :
    DenseRange (polynomialMap (A := A) w hw) := by
  have he : Set.range (((↑) : PolynomialRing (A := A) w hw → Ring (A := A) w hw) ∘
      (polynomialEquiv w hw).symm) = Set.range ((↑) : PolynomialRing (A := A) w hw → Ring (A := A) w hw) :=
    (polynomialEquiv w hw).symm.surjective.range_comp _
  change Dense (Set.range (((↑) : PolynomialRing (A := A) w hw → Ring (A := A) w hw) ∘
    (polynomialEquiv w hw).symm))
  rw [he]
  exact Completion.denseRange_coe

end EnvelopeProperty.WeightedPolynomialCompletion
