import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussGeometry
import EnvelopeProperty.Berkovich.SpectrumPolynomialGauss

/-! # The same original total-model Gauss point and native valuative center

The original unit inclusion and original polynomial parameter retain their
whole geometric identities. Original source projectivity and derived bounded
polynomial Gauss values construct the true original model center. No center
or metric comparison is an input.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Polynomial Topology Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich

/-- The actual original polynomial inclusion maps the ENTIRE genuine Laurent
Gauss point to the native point of its SAME actual polynomial Gauss valuation. -/
theorem originalNativeLaurentGaussPoint_map_toLaurent {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom
        (Polynomial.toLaurent : A[X] →+* A[T;T⁻¹])))
        (originalNativeLaurentGaussPoint v r hr) =
      SchemeValuedPoint.basePoint (gaussValuation v r) := by
  apply (SchemeValuedPoint.spectrumHomeomorph (A := A[X])).injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map, originalNativeLaurentGaussPoint,
    Homeomorph.apply_symm_apply, SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply]
  apply Spectrum.ext_val
  intro F
  exact Spectrum.laurentGauss_val_toLaurent v r hr F

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- The SAME original unit-open parameter and inclusion derive their literal
whole original polynomial parameter triangle. -/
theorem originalTestConfigurationUnitParameter_line :
    originalTestConfigurationUnitParameter C ≫
        Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹])) =
      C.unitOpen.ι ≫ C.projection := by
  have h := congrArg (fun a : C.unitOpenOver ⟶ ProjBerk.nativeParameterLine k => a.left)
    (NativeTestConfiguration.TestConfiguration.unitOpenIso_structure C)
  rw [Over.comp_left, Over.comp_left, ProjBerk.nativeParameterGroupInclusion_left] at h
  rw [← Category.assoc] at h
  change (C.unitOpenIso.hom ≫
    CartesianMonoidalCategory.snd X (ProjBerk.nativeMultiplicativeGroup k)).left ≫ _ = _ at h
  rw [originalTestConfigurationUnitParameter_eq] at h
  exact h

variable {v : Valuation k ℝ≥0} (x : RelativeSchemeValuedPoint v X.hom)

/-- The SAME original unit inclusion constructs the actual original total-model Gauss point. -/
def originalTestConfigurationTotalGaussPoint (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint C.total :=
  SchemeValuedPoint.map C.unitOpen.ι (originalTestConfigurationUnitGaussPoint C x r hr)

/-- Its ENTIRE original parameter-line point is the true original polynomial Gauss point. -/
theorem originalTestConfigurationTotalGaussPoint_parameter (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map C.projection (originalTestConfigurationTotalGaussPoint C x r hr) =
      SchemeValuedPoint.basePoint (gaussValuation v r) := by
  rw [originalTestConfigurationTotalGaussPoint, ← SchemeValuedPoint.map_comp,
    ← originalTestConfigurationUnitParameter_line, SchemeValuedPoint.map_comp,
    originalTestConfigurationUnitGaussPoint_parameter, originalNativeLaurentGaussPoint_map_toLaurent]

/-- The derived whole parameter identity constructs actual native prescribed-base membership. -/
def originalTestConfigurationGaussRelativePoint (r : ℝ≥0) (hr : 0 < r) :
    RelativeSchemeValuedPoint (gaussValuation v r) C.projection :=
  ⟨originalTestConfigurationTotalGaussPoint C x r hr,
    originalTestConfigurationTotalGaussPoint_parameter C x r hr⟩

/-- Actual bounded coefficients and radius at most one bound EVERY original polynomial. -/
theorem originalPolynomialGauss_bounded {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (hv : ∀ a, v a ≤ 1) (r : ℝ≥0) (hr : r ≤ 1) :
    ∀ F : A[X], gaussValuation v r F ≤ 1 :=
  Spectrum.isBounded_gauss (Spectrum.ofValuation v) hv r hr

/-- For the ORIGINAL trivial field valuation, polynomial boundedness is DERIVED. -/
theorem originalTrivialPolynomialGauss_bounded (r : ℝ≥0) (hr : r ≤ 1) :
    ∀ F : k[X], gaussValuation (1 : Valuation k ℝ≥0) r F ≤ 1 :=
  originalPolynomialGauss_bounded 1 Valuation.one_apply_le_one r hr

/-- Original TC projectivity and the DERIVED original polynomial Gauss bound
construct the actual proper-model center of the SAME original valued point. -/
def originalTestConfigurationTrivialGaussCenter
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1) : C.total := by
  let : IsProper C.projection := C.projection_isProper
  exact RelativeSchemeValuedPoint.center (originalTrivialPolynomialGauss_bounded r hr₁)
    (originalTestConfigurationGaussRelativePoint C x r hr)

/-- The SAME actual original total-model Gauss support specializes to its
constructed actual center, through the genuine native valuative lift. -/
theorem originalTestConfigurationTrivialGaussPoint_specializes_center
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1) :
    (originalTestConfigurationTotalGaussPoint C x r hr).point ⤳
      originalTestConfigurationTrivialGaussCenter C x r hr hr₁ := by
  let : IsProper C.projection := C.projection_isProper
  exact RelativeSchemeValuedPoint.support_specializes_center
    (originalTrivialPolynomialGauss_bounded r hr₁)
    (originalTestConfigurationGaussRelativePoint C x r hr)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
