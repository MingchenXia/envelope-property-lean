/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealModels
import EnvelopeProperty.Projective.IdealBaseChange
import EnvelopeProperty.Projective.NativeClosed

/-!
# Constructed ideal functions on the actual variety product

The ambient product ideals are pulled back to the actual native closed
subscheme X × A¹. The whole product isomorphism is constructed, the actual
Gauss point is lifted through its genuine closed immersion, and intrinsic
proper-center ideal logarithms preserve their entire original functions.
No comparison, model, or point-lifting certificate is an assumption.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The entire original homogeneous ideal, with its actual homogeneous grading. -/
def nativeHomogeneousIdeal : HomogeneousIdeal (ProjectiveGrading k M) :=
  ⟨X.ideal, (isHomogeneousIdeal_iff_isHomogeneous _).mp X.isHomogeneousIdeal⟩

/-- The genuine original projective quotient-kernel ideal sheaf. -/
def nativeIdeal : (NativeProjectiveScheme k M).IdealSheafData :=
  nativeHomogeneousIdealSheaf X.nativeHomogeneousIdeal

/-- The actual native closed projective scheme of the original subvariety. -/
abbrev NativeScheme : Scheme.{u} := X.nativeIdeal.subscheme

/-- The actual original closed immersion of the variety. -/
def nativeInclusion : X.NativeScheme ⟶ NativeProjectiveScheme k M :=
  X.nativeIdeal.subschemeι

instance nativeInclusion_isClosedImmersion : IsClosedImmersion X.nativeInclusion := by
  dsimp [nativeInclusion]
  infer_instance

/-- The native variety's entire actual coefficient structure morphism. -/
def nativeStructure : X.NativeScheme ⟶ Spec (CommRingCat.of k) :=
  X.nativeInclusion ≫ nativeStructureMap

/-- The original ideal is pulled back along the first projection of the actual product. -/
def nativeProductCutIdeal : (NativePolynomialLineProduct k M).IdealSheafData :=
  X.nativeIdeal.comap (pullback.fst (nativeStructureMap (R := k) (n := M))
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))))

/-- The actual closed subscheme X × A¹ in the original genuine ambient product. -/
abbrev NativeProductModel : Scheme.{u} := X.nativeProductCutIdeal.subscheme

/-- The actual original closed immersion into the ambient product. -/
def nativeProductInclusion : X.NativeProductModel ⟶ NativePolynomialLineProduct k M :=
  X.nativeProductCutIdeal.subschemeι

instance nativeProductInclusion_isClosedImmersion :
    IsClosedImmersion X.nativeProductInclusion := by
  dsimp [nativeProductInclusion]
  infer_instance

/-- The original polynomial-base structure on the actual variety product. -/
def nativeProductStructure : X.NativeProductModel ⟶ Spec (CommRingCat.of k[X]) :=
  X.nativeProductInclusion ≫ nativePolynomialLineProductStructure

/-- The whole native closed subscheme is the actual product of the original
native variety and the original affine polynomial line, by genuine pullback pasting. -/
def nativeProductModelIso : X.NativeProductModel ≅
    pullback X.nativeStructure
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
  (X.nativeIdeal.comapIso _).trans
    ((pullbackSymmetry _ _).trans
      (pullbackRightPullbackFstIso (nativeStructureMap (R := k) (n := M))
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) X.nativeInclusion))

/-- The actual product identification preserves its entire polynomial-base structure. -/
theorem nativeProductModelIso_over_base :
    X.nativeProductModelIso.hom ≫ pullback.snd _ _ = X.nativeProductStructure := by
  dsimp only [nativeProductModelIso, Iso.trans_hom, nativeStructure, nativeInclusion,
    nativeProductStructure, nativeProductInclusion, nativeProductCutIdeal]
  rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rfl

private local instance ambientProductProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

instance nativeProductStructure_isProper : IsProper X.nativeProductStructure := by
  dsimp [nativeProductStructure]
  infer_instance

/-- The actual proper variety product is locally Noetherian over the original
Noetherian polynomial model base; no such hypothesis is supplied. -/
instance nativeProductModel_isLocallyNoetherian : IsLocallyNoetherian X.NativeProductModel :=
  LocallyOfFiniteType.isLocallyNoetherian X.nativeProductStructure

/-- Coefficient base change and the actual ambient product isomorphism retain
the entire original defining ideal of X, including its actual sheaf structure. -/
theorem nativeProductCutIdeal_eq :
    X.nativeProductCutIdeal = nativePolynomialLineProductIdeal
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap (Polynomial.C : k →+* k[X]))) := by
  have hi : (nativePolynomialLineProductIso k M).inv ≫ nativeCoefficientMap Polynomial.C =
      pullback.fst (nativeStructureMap (R := k) (n := M))
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    change (nativeCoefficientBaseChangeIso (n := M) Polynomial.C).inv ≫ _ = _
    rw [← nativeCoefficientBaseChangeIso_hom_fst, Iso.inv_hom_id_assoc]
  rw [nativePolynomialLineProductIdeal, nativeHomogeneousIdealSheaf,
    ← homogeneousQuotientIdealSheaf_comap_coefficientMap,
    ← Scheme.IdealSheafData.comap_comp, hi]
  rfl

/-- The actual ambient Gauss point kills the entire original pulled-back
defining ideal of X, so its genuine native support lies in the true closed model. -/
theorem gaussProductPoint_mem_nativeProductCutIdeal (v : X.an) :
    (gaussProductPoint v.1).1.point ∈ X.nativeProductCutIdeal.support := by
  rw [X.nativeProductCutIdeal_eq]
  change (gaussProductPoint v.1).1.point ∈
    ((nativeHomogeneousIdealSheaf
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).comap
        (nativePolynomialLineProductIso k M).inv).support
  rw [Scheme.IdealSheafData.support_comap]
  have hp := congrArg (fun y => y.1.point) (nativePolynomialLineProductPoint_inverse
    (gaussModelPoint v.1))
  change (nativePolynomialLineProductIso k M).inv (gaussProductPoint v.1).1.point =
    NormalizedProjectiveSpectrum.nativeSupport (gaussModelPoint v.1).1 at hp
  change (nativePolynomialLineProductIso k M).inv (gaussProductPoint v.1).1.point ∈
    (nativeHomogeneousIdealSheaf
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).support
  rw [hp]
  change NormalizedProjectiveSpectrum.nativeSupport (gaussModelPoint v.1).1 ∈
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M)
      (X.nativeHomogeneousIdeal.map (coefficientGradedMap Polynomial.C))).support
  rw [← SetLike.mem_coe, GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus]
  change (X.ideal.map (MvPolynomial.map Polynomial.C)) ≤
    (gaussModelPoint v.1).1.1.val.supp
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  change (gaussModelPoint v.1).1.1.val (MvPolynomial.map Polynomial.C f) = 0
  have hs := swap_modelMonomial (k := k) (n := M) f 1 0
  simp only [modelMonomial, pow_one, pow_zero, MvPolynomial.C_1, mul_one] at hs
  rw [gaussModelPoint_val_apply, hs, gaussExt_val_C]
  exact v.2 f hf

/-- The actual Gauss point on the actual native variety product, constructed
through the genuine closed-immersion homeomorphism and its true support. -/
def nativeProductGaussPoint (v : X.an) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure :=
  (RelativeSchemeValuedPoint.closedImmersionHomeomorph X.nativeProductInclusion rfl).symm
    ⟨gaussProductPoint v.1, by
      change _ ∈ Set.range X.nativeProductCutIdeal.subschemeι
      rw [X.nativeProductCutIdeal.range_subschemeι]
      exact X.gaussProductPoint_mem_nativeProductCutIdeal v⟩

/-- The actual closed inclusion preserves the full original ambient Gauss point. -/
theorem map_nativeProductGaussPoint (v : X.an) :
    RelativeSchemeValuedPoint.map X.nativeProductInclusion rfl (X.nativeProductGaussPoint v) =
      gaussProductPoint v.1 := by
  exact congrArg Subtype.val
    ((RelativeSchemeValuedPoint.closedImmersionHomeomorph X.nativeProductInclusion rfl).apply_symm_apply
      ⟨gaussProductPoint v.1, by
        change _ ∈ Set.range X.nativeProductCutIdeal.subschemeι
        rw [X.nativeProductCutIdeal.range_subschemeι]
        exact X.gaussProductPoint_mem_nativeProductCutIdeal v⟩)

@[fun_prop]
theorem continuous_nativeProductGaussPoint : Continuous X.nativeProductGaussPoint :=
  (RelativeSchemeValuedPoint.closedImmersionHomeomorph X.nativeProductInclusion rfl).symm.continuous.comp
    ((continuous_gaussProductPoint.comp continuous_subtype_val).subtype_mk _)

/-- The actual ideal on the actual variety product, retaining the original
ambient ideal by genuine geometric pullback. -/
def nativeProductIdeal (J : HomogeneousIdeal (ProjectiveGrading k[X] M)) :
    X.NativeProductModel.IdealSheafData :=
  (nativePolynomialLineProductIdeal J).comap X.nativeProductInclusion

/-- The whole intrinsic ideal logarithm on the true variety product is exactly
the original ambient Gauss model logarithm of the entire original ideal. -/
theorem modelIdealLog_nativeProductIdeal
    (J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (v : X.an) :
    RelativeSchemeValuedPoint.modelIdealLog (X.nativeProductIdeal J)
      gaussModelCoefficient_le_one (X.nativeProductGaussPoint v) =
      RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
        gaussModelCoefficient_le_one (gaussProductPoint v.1) := by
  rw [nativeProductIdeal, RelativeSchemeValuedPoint.modelIdealLog_comap
    (nativePolynomialLineProductIdeal J) X.nativeProductInclusion rfl
      gaussModelCoefficient_le_one (X.nativeProductGaussPoint v), X.map_nativeProductGaussPoint]

/-- Every actual PL function has an exact finite logarithm-difference formula
for genuine original ideal sheaves on the actual variety product. -/
theorem IsPL.exists_nativeProductIdeal_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData),
      (∀ v : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) ≠ ⊥) ∧
      ∀ v : X.an, (((r : ℝ) * φ v : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) -
        RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, _hIfg, _hJfg, _hIvert, _hJvert, hfin, heq⟩ :=
    hφ.exists_vertical_productIdeal_models
  exact ⟨r, hr, C, X.nativeProductIdeal I, X.nativeProductIdeal J,
    fun v => by simpa only [X.modelIdealLog_nativeProductIdeal] using hfin v,
    fun v => by simpa only [X.modelIdealLog_nativeProductIdeal] using heq v⟩

/-- The genuine restricted-product ideal construction applies to locally convex
functions through the proved PL germ/sheaf theorem. -/
theorem IsLocallyConvex.exists_nativeProductIdeal_models {a : ℚ} {φ : X.an → ℝ}
    (hφ : X.IsLocallyConvex a φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData),
      (∀ v : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) ≠ ⊥) ∧
      ∀ v : X.an, (((r : ℝ) * φ v : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) -
        RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint v) + ((C : ℝ) : EReal) :=
  hφ.isPL.exists_nativeProductIdeal_models X

end EnvelopeProperty.ProjSubvariety
