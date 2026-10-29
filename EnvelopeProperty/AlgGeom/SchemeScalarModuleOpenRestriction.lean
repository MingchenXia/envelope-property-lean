import EnvelopeProperty.AlgGeom.SchemeScalarModulePresheaf
import EnvelopeProperty.AlgGeom.SchemeModuleOpenSectionsKernel

/-! # Literal scalar sections and actual original open restriction -/
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeScalarModuleOpenRestriction

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R)) (M : X.Modules)

/-- The literal original R action agrees with the native base section action. -/
def nativeSectionsIso (U : X.Opens) :
    SchemeScalarModulePresheaf.openSections p M U ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).obj
        ((Scheme.Modules.baseModulePresheaf p M).obj (op U)) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext (m : Γ(M, U))
  change (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (p.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) • m =
    (p.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of R)).inv r)) • m
  apply congrArg (fun a => a • m)
  have h := p.appLE_map (U := ⊤) (by simp) (homOfLE (le_top : U ≤ ⊤)).op
  erw [← Scheme.Hom.app_eq_appLE] at h
  exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv r)

/-- The entire module of original open sections agrees with the literal
whole global-section module on the original open subscheme. -/
def openRestrictIso (U : X.Opens) :
    SchemeScalarModulePresheaf.openSections p M U ≅
      AffineModuleFlatBaseChange.sections (U.ι ≫ p) (M.restrict U.ι) :=
  nativeSectionsIso p M U ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).mapIso
      (SchemeModuleOpenSectionsKernel.openSectionsRestrictIso p M U) ≪≫
    (nativeSectionsIso (U.ι ≫ p) (M.restrict U.ι) ⊤).symm ≪≫
    SchemeScalarModulePresheaf.topSectionsIso (U.ι ≫ p) (M.restrict U.ι)

/-- The entire scalar comparison retains the actual original open-section transport. -/
theorem openRestrictIso_apply (U : X.Opens)
    (m : SchemeScalarModulePresheaf.openSections p M U) :
    (openRestrictIso p M U).hom m =
      M.presheaf.map (eqToHom U.ι_image_top).op m := rfl

end EnvelopeProperty.SchemeScalarModuleOpenRestriction
