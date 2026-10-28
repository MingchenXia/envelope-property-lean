import EnvelopeProperty.Char0.MultiplierFamilySmoothnessNative
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdeals

/-! # The SAME whole original parameter quotient is genuinely the native variety product -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk ProjSubvariety.MultiplierBaseIdeals
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def subschemeEqIso {Y : Scheme.{u}} (I J : Y.IdealSheafData) (h : I = J) :
    I.subscheme ≅ J.subscheme := eqToIso (congrArg Scheme.IdealSheafData.subscheme h)
private theorem subschemeEqIso_inclusion {Y : Scheme.{u}} (I J : Y.IdealSheafData) (h : I = J) :
    (subschemeEqIso I J h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp [subschemeEqIso]
private def closedImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Y.IdealSheafData) (h : f.ker = I) : X ≅ I.subscheme :=
  asIso f.toImage ≪≫ subschemeEqIso f.ker I h
private theorem closedImageIso_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Y.IdealSheafData) (h : f.ker = I) :
    (closedImageIso f I h).hom ≫ I.subschemeι = f := by
  rw [closedImageIso, Iso.trans_hom, Category.assoc, subschemeEqIso_inclusion]
  exact Scheme.Hom.toImage_imageι f

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual original family's whole closed embedding into the actual ambient product. -/
def familyProductInclusion : familyScheme X ⟶ NativePolynomialLineProduct k M :=
  familyInclusion X ≫ (nativePolynomialLineProductIso k M).hom

/-- This is the genuine original closed immersion, with no model comparison supplied. -/
instance familyProductInclusion_isClosedImmersion : IsClosedImmersion (familyProductInclusion X) := by
  dsimp [familyProductInclusion]
  infer_instance

/-- The ENTIRE original defining ideal equals the kernel of the SAME actual family embedding. -/
theorem familyProduct_kernel : (familyProductInclusion X).ker = X.nativeProductCutIdeal := by
  rw [X.nativeProductCutIdeal_eq]
  exact (nativePolynomialLineProductIdeal_eq_kernel (familyHomogeneousIdeal X)).symm

/-- The SAME actual original parameter-family scheme is genuinely the original native closed product model. -/
def familyProductIso : familyScheme X ≅ X.NativeProductModel :=
  closedImageIso (familyProductInclusion X) X.nativeProductCutIdeal (familyProduct_kernel X)

/-- Its WHOLE original ambient inclusion triangle. -/
theorem familyProductIso_inclusion :
    (familyProductIso X).hom ≫ X.nativeProductInclusion = familyProductInclusion X :=
  closedImageIso_inclusion (familyProductInclusion X) X.nativeProductCutIdeal (familyProduct_kernel X)

/-- The SAME whole original polynomial-base projection is retained. -/
theorem familyProductIso_projection :
    (familyProductIso X).hom ≫ X.nativeProductStructure = familyProjection X := by
  change (familyProductIso X).hom ≫ X.nativeProductInclusion ≫ nativePolynomialLineProductStructure = _
  rw [← Category.assoc, familyProductIso_inclusion, familyProductInclusion, Category.assoc,
    nativePolynomialLineProductIso_over_base]
  rfl

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
