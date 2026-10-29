/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealFamilyLift
import EnvelopeProperty.Local.PLIdealPrincipalization

/-!
# Whole native coordinates of the actual original variety product

The true constant-ideal closed family is compared to the original actual
variety product by an actual scheme isomorphism, with whole inclusion/base
triangles and equality of every entire original parameter ideal sheaf.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual closed constant-ideal coordinates are the whole original
constructed variety product, through the genuine ambient product isomorphism. -/
def nativeConstantFamilyModelIso :
    (nativeConstantIdeal X.nativeHomogeneousIdeal).subscheme ≅ X.NativeProductModel := by
  apply Scheme.IdealSheafData.subschemeIsoOfComap _ _ (nativePolynomialLineProductIso k M)
  rw [X.nativeProductCutIdeal_eq, nativePolynomialLineProductIdeal,
    ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  rfl

/-- The entire actual coordinate comparison has its original ambient triangle. -/
@[reassoc]
theorem nativeConstantFamilyModelIso_hom_inclusion :
    X.nativeConstantFamilyModelIso.hom ≫ X.nativeProductInclusion =
      (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        (nativePolynomialLineProductIso k M).hom :=
  Scheme.IdealSheafData.subschemeIsoOfComap_hom_ι _ _ _ _

/-- The whole original polynomial-base structure is preserved, not assumed. -/
@[reassoc]
theorem nativeConstantFamilyModelIso_over_base :
    X.nativeConstantFamilyModelIso.hom ≫ X.nativeProductStructure =
      (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫ nativeStructureMap := by
  change _ ≫ X.nativeProductInclusion ≫ nativePolynomialLineProductStructure = _
  rw [← Category.assoc, X.nativeConstantFamilyModelIso_hom_inclusion,
    Category.assoc, nativePolynomialLineProductIso_over_base]

/-- Actual native coordinates preserve every entire original parameter ideal
on the original variety product, including its full nonradical sheaf data. -/
theorem nativeProductIdeal_comap_constantFamilyModelIso
    (I : HomogeneousIdeal (ProjectiveGrading k[X] M)) :
    (X.nativeProductIdeal I).comap X.nativeConstantFamilyModelIso.hom =
      (nativeHomogeneousIdealSheaf I).comap
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι := by
  rw [nativeProductIdeal, ← Scheme.IdealSheafData.comap_comp,
    X.nativeConstantFamilyModelIso_hom_inclusion,
    nativePolynomialLineProductIdeal, ← Scheme.IdealSheafData.comap_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual native-coordinate blowup is the same original simultaneous
blowup, via its genuine universal property and the proved whole product ideal
comparison. No blowup-comparison certificate is an assumption. -/
theorem exists_simultaneousIdealBlowup_nativeCoordinateIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) :
    ∃ e : (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUp ≅
      X.simultaneousIdealBlowup (X.nativeProductIdeal I) (X.nativeProductIdeal J),
      e.hom ≫ X.simultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) =
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
          X.nativeConstantFamilyModelIso.hom := by
  have hK : ((X.nativeProductIdeal I) * (X.nativeProductIdeal J)).comap
      X.nativeConstantFamilyModelIso.hom = nativeClosedProductIdeal X.nativeHomogeneousIdeal I J := by
    rw [Scheme.IdealSheafData.comap_mul,
      X.nativeProductIdeal_comap_constantFamilyModelIso,
      X.nativeProductIdeal_comap_constantFamilyModelIso]
    rfl
  obtain ⟨e, he, _⟩ := Scheme.IdealSheafData.blowUp.exists_mapIso
    (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J)
    X.nativeConstantFamilyModelIso ((X.nativeProductIdeal I) * (X.nativeProductIdeal J)) hK.symm
  exact ⟨e, he⟩

end EnvelopeProperty.ProjSubvariety
