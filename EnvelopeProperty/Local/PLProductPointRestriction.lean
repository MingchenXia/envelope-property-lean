import EnvelopeProperty.Local.PLIdealSubvarietyModels
import EnvelopeProperty.Local.ParameterMonomialModelNorms

/-! # Whole original subvariety restriction of arbitrary Gauss-base product points -/
open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The WHOLE actual ambient polynomial normalized point of an arbitrary
original variety-product valued point over the prescribed Gauss base. -/
def nativeProductNormalizedPoint
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) :
    RelativeNormalizedProjectiveSpectrum (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) M :=
  (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _).symm
    (RelativeSchemeValuedPoint.map (nativePolynomialLineProductIso k M).inv
      nativePolynomialLineProductIso_inv_over_base
      (RelativeSchemeValuedPoint.map X.nativeProductInclusion rfl y))

/-- The entire actual product point is recovered, including residue valuation. -/
theorem nativePolynomialLineProductPoint_nativeProductNormalizedPoint
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) :
    nativePolynomialLineProductPoint (X.nativeProductNormalizedPoint y) =
      RelativeSchemeValuedPoint.map X.nativeProductInclusion rfl y := by
  apply Subtype.ext
  dsimp only [nativePolynomialLineProductPoint, nativeProductNormalizedPoint]
  rw [Homeomorph.apply_symm_apply]
  change SchemeValuedPoint.map _ (SchemeValuedPoint.map _ _) = _
  rw [← SchemeValuedPoint.map_comp, Iso.inv_hom_id, SchemeValuedPoint.map_id]

private theorem restriction_mem_original
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) :
    (normalizedSpectrumHomeomorph.symm
      (RelativeNormalizedProjectiveSpectrum.polynomialRestriction
        (1 : Valuation k ℝ≥0) gaussRadius (X.nativeProductNormalizedPoint y))) ∈ X.an := by
  let x := X.nativeProductNormalizedPoint y
  have hp : (nativePolynomialLineProductPoint x).1.point ∈ X.nativeProductCutIdeal.support := by
    rw [X.nativePolynomialLineProductPoint_nativeProductNormalizedPoint]
    change X.nativeProductInclusion y.1.point ∈ (X.nativeProductCutIdeal.support : Set _)
    rw [← X.nativeProductCutIdeal.range_subschemeι]
    exact ⟨y.1.point, rfl⟩
  rw [X.nativeProductCutIdeal_eq] at hp
  change (nativePolynomialLineProductPoint x).1.point ∈
    ((nativeHomogeneousIdealSheaf
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).comap
        (nativePolynomialLineProductIso k M).inv).support at hp
  rw [Scheme.IdealSheafData.support_comap] at hp
  have he := congrArg (fun z => z.1.point) (nativePolynomialLineProductPoint_inverse x)
  change (nativePolynomialLineProductIso k M).inv (nativePolynomialLineProductPoint x).1.point =
    NormalizedProjectiveSpectrum.nativeSupport x.1 at he
  change (nativePolynomialLineProductIso k M).inv (nativePolynomialLineProductPoint x).1.point ∈
    (nativeHomogeneousIdealSheaf
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).support at hp
  rw [he] at hp
  change NormalizedProjectiveSpectrum.nativeSupport x.1 ∈
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M)
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).support at hp
  rw [← SetLike.mem_coe, GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus] at hp
  change X.ideal.map (MvPolynomial.map Polynomial.C) ≤ x.1.1.val.supp at hp
  let z := RelativeNormalizedProjectiveSpectrum.polynomialRestriction
    (1 : Valuation k ℝ≥0) gaussRadius x
  let w := normalizedSpectrumHomeomorph.symm z
  change X.ideal ≤ w.1.val.supp
  intro F hF
  change w.1.val F = 0
  rw [← normalizedSpectrumHomeomorph_val_apply w F, Homeomorph.apply_symm_apply]
  exact hp (Ideal.mem_map_of_mem (MvPolynomial.map Polynomial.C) hF)

/-- Actual original analytic restriction of EVERY genuine Gauss-base variety
product point. Its membership in the ORIGINAL variety is derived from the
entire actual defining ideal, not a supplied support hypothesis. -/
def nativeProductBaseRestriction
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) : X.an :=
  ⟨normalizedSpectrumHomeomorph.symm
    (RelativeNormalizedProjectiveSpectrum.polynomialRestriction
      (1 : Valuation k ℝ≥0) gaussRadius (X.nativeProductNormalizedPoint y)),
    restriction_mem_original X y⟩

/-- EVERY original base form has its SAME actual full restricted value. -/
theorem nativeProductBaseRestriction_val
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) (F : MvPolynomial (Fin (M+1)) k) :
    (X.nativeProductBaseRestriction y).1.1.val F =
      (X.nativeProductNormalizedPoint y).1.1.val (MvPolynomial.map Polynomial.C F) := by
  rw [← normalizedSpectrumHomeomorph_val_apply]
  change (normalizedSpectrumHomeomorph (normalizedSpectrumHomeomorph.symm _)).1.1.val F = _
  rw [Homeomorph.apply_symm_apply]
  rfl
/-- Whole actual ambient restriction depends continuously on the original
product valued point, including its entire residue valuation. -/
@[fun_prop] theorem continuous_nativeProductNormalizedPoint :
    Continuous X.nativeProductNormalizedPoint :=
  (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _).symm.continuous.comp
    ((RelativeSchemeValuedPoint.continuous_map _ _).comp
      (RelativeSchemeValuedPoint.continuous_map _ _))

/-- The original analytic restriction is continuous on ALL actual product points. -/
@[fun_prop] theorem continuous_nativeProductBaseRestriction :
    Continuous X.nativeProductBaseRestriction :=
  (normalizedSpectrumHomeomorph.symm.continuous.comp
    ((RelativeNormalizedProjectiveSpectrum.continuous_polynomialRestriction
      (1 : Valuation k ℝ≥0) gaussRadius).comp
      (X.continuous_nativeProductNormalizedPoint))).subtype_mk _

/-- Entire Gauss product points retain their original normalized Gauss point. -/
theorem nativeProductNormalizedPoint_gauss (w : X.an) :
    X.nativeProductNormalizedPoint (X.nativeProductGaussPoint w) = gaussModelPoint w.1 := by
  dsimp only [nativeProductNormalizedPoint]
  rw [X.map_nativeProductGaussPoint, gaussProductPoint, nativePolynomialLineProductPoint_inverse,
    Homeomorph.symm_apply_apply]

/-- Restricting the genuine original Gauss lift recovers the SAME whole
original variety point, without a coordinate-only identification. -/
theorem nativeProductBaseRestriction_gauss (w : X.an) :
    X.nativeProductBaseRestriction (X.nativeProductGaussPoint w) = w := by
  apply Subtype.ext
  change normalizedSpectrumHomeomorph.symm
    (RelativeNormalizedProjectiveSpectrum.polynomialRestriction _ _ _) = w.1
  rw [X.nativeProductNormalizedPoint_gauss, gaussModelPoint,
    RelativeNormalizedProjectiveSpectrum.polynomialRestriction_polynomialGauss,
    Homeomorph.symm_apply_apply]
end EnvelopeProperty.ProjSubvariety
