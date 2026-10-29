/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierBlowupFlat
import EnvelopeProperty.Local.PLIdealNativeCoordinates

/-! # Actual flat polynomial-base structures on the original PL blowup models -/

open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual whole original variety product is flat over the same polynomial line. -/
theorem nativeProductStructure_isFlat : Flat X.nativeProductStructure := by
  have : Flat X.nativeStructure := inferInstance
  have h : Flat (X.nativeProductModelIso.hom ≫ pullback.snd _ _) := inferInstance
  exact X.nativeProductModelIso_over_base ▸ h

/-- The actual simultaneous product-ideal blowup is flat over the SAME
original polynomial line, without integrality or flatness hypotheses. -/
theorem simultaneousIdealBlowupStructure_isFlat
    (I L : X.NativeProductModel.IdealSheafData) :
    Flat (X.simultaneousIdealBlowupStructure I L) := by
  have : Flat X.nativeProductStructure := X.nativeProductStructure_isFlat
  exact Scheme.IdealSheafData.blowUp.flat_over_dedekind (I * L) X.nativeProductStructure

/-- The same actual native constant-family blowup has its genuine original
flat polynomial-base structure through the proved whole coordinate isomorphism. -/
theorem nativeClosedProductIdealPolynomialStructure_isFlat
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] M)) :
    Flat ((nativeClosedProductIdeal X.nativeHomogeneousIdeal I L).blowUpπ ≫
      (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
      (nativeStructureMap (R := k[X]) (n := M))) := by
  obtain ⟨e, he⟩ := X.exists_simultaneousIdealBlowup_nativeCoordinateIso I L
  have : Flat (X.simultaneousIdealBlowupStructure (X.nativeProductIdeal I) (X.nativeProductIdeal L)) :=
    X.simultaneousIdealBlowupStructure_isFlat _ _
  have h : Flat (e.hom ≫ X.simultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal L)) := inferInstance
  have htri : e.hom ≫ X.simultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal L) =
      (nativeClosedProductIdeal X.nativeHomogeneousIdeal I L).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫ nativeStructureMap := by
    change e.hom ≫ X.simultaneousIdealBlowupProjection _ _ ≫ X.nativeProductStructure = _
    rw [← Category.assoc, he, Category.assoc, X.nativeConstantFamilyModelIso_over_base]
  exact htri ▸ h

end EnvelopeProperty.ProjSubvariety
