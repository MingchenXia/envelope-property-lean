import EnvelopeProperty.AlgGeom.SchemeSectionHomology
import EnvelopeProperty.Algebra.LeftExactHomologyCoherence
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # Actual native homology restriction and SAME original coefficient square -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.SchemeSectionHomologyRestriction
open AlgebraicGeometry CategoryTheory Opposite

universe u
variable {X : Scheme.{u}} (K : CochainComplex X.Modules ℕ)
variable {U V : X.Opens} (j : U ⟶ V)

/-- The native homology of the ENTIRE original restriction complex, with true scalar comparison. -/
def restrictionHomologyMap (q : ℕ) :
    (SchemeSectionHomology.sectionComplex K V).homology q ⟶
      (ModuleCat.restrictScalars (X.presheaf.map j.op).hom).obj
        ((SchemeSectionHomology.sectionComplex K U).homology q) :=
  HomologicalComplex.homologyMap (SchemeSectionHomology.restrictionComplexMap K j) q ≫
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso (X.presheaf.map j.op).hom
      (SchemeSectionHomology.sectionComplex K U) q).hom

/-- The SAME canonical comparison commutes with actual original native homology restrictions. -/
theorem comparison_restriction (q : ℕ) :
    restrictionHomologyMap K j q ≫
        (ModuleCat.restrictScalars (X.presheaf.map j.op).hom).map
          (SchemeSectionHomology.comparison K U q) =
      SchemeSectionHomology.comparison K V q ≫
        (SchemeSectionHomology.restriction j).app (K.homology q) := by
  have h := SchemeSectionHomology.comparison_restriction K j q
  rw [LeftExactHomologyCoherence.map_comp,
    LeftExactHomologyCoherence.map_eq_mapHomologyIso] at h
  unfold restrictionHomologyMap ModuleComplexNativeCycleClasses.restrictionHomologyIso
    ModuleHomologyScalarRestriction.homologyIso
  rw [Category.assoc]
  exact h

end EnvelopeProperty.SchemeSectionHomologyRestriction
