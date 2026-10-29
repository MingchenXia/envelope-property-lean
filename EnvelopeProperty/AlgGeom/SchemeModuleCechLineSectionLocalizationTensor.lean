import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalization
import EnvelopeProperty.AlgGeom.SchemeUnitScalarAction

/-! # Actual whole tensor multiplication and its original affine-frame readback

These maps use the original section and actual module tensor. The frame
readback is a proved equality of entire original sheaf maps, hence retains
every original section value needed for denominator lifting.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation
open SchemeGlobalSectionTensorPowerNorms CyclicSectionGlobalCoverRootSectionPowers

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def tensorRightUnit {X : Scheme.{u}} (F : X.Modules) : F ⊗ unitObj X ≅ F :=
  (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F

private theorem tensorRightUnit_action {X : Scheme.{u}}
    (F : X.Modules) (r : unitObj X ⟶ unitObj X) :
    (tensorRightUnit F).inv ≫ (𝟙 F ⊗ₘ r) ≫ (tensorRightUnit F).hom =
      SchemeUnitScalarAction.unitAction F r := by
  let l := SchemeTensorUnitSections.leftUnitIso F
  let d := tensorRightUnit F
  have h : (β_ (unitObj X) F).hom ≫ d.hom = l.hom := by
    dsimp only [d, l, tensorRightUnit, SchemeTensorUnitSections.leftUnitIso]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
      id_tensorHom, whiskerRightIso_hom]
    rw [← BraidedCategory.braiding_naturality_left_assoc,
      CategoryTheory.braiding_rightUnitor]
  have hi : d.inv = l.inv ≫ (β_ (unitObj X) F).hom := by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, h, Iso.inv_hom_id]
  change d.inv ≫ (𝟙 F ⊗ₘ r) ≫ d.hom = l.inv ≫ (r ▷ F) ≫ l.hom
  rw [hi, id_tensorHom, Category.assoc,
    ← BraidedCategory.braiding_naturality_left_assoc, h]

/-- Multiplication of the WHOLE original module by the SAME actual section. -/
def tensorSectionMap {X : Scheme.{u}} (F : X.Modules) {T : X.Modules}
    (t : unitObj X ⟶ T) : F ⟶ F ⊗ T :=
  (tensorRightUnit F).inv ≫ (𝟙 F ⊗ₘ t)

/-- An actual original line frame contracts the WHOLE actual module tensor. -/
def tensorFrameIso {X : Scheme.{u}} (F : X.Modules) {T : X.Modules}
    (e : T ≅ unitObj X) : F ⊗ T ≅ F :=
  (Iso.refl F ⊗ᵢ e) ≪≫ tensorRightUnit F

/-- Every actual section/frame contraction is the actual original unit action. -/
theorem tensorSectionMap_frame {X : Scheme.{u}} (F : X.Modules) {T : X.Modules}
    (t : unitObj X ⟶ T) (e : T ≅ unitObj X) :
    tensorSectionMap F t ≫ (tensorFrameIso F e).hom =
      SchemeUnitScalarAction.unitAction F
        (ModularCurves.unitEndomorphismOfTopSection
          (SchemeLineSectionUnitFrames.frameScalar e t)) := by
  change (tensorRightUnit F).inv ≫ (𝟙 F ⊗ₘ t) ≫
      (𝟙 F ⊗ₘ e.hom) ≫ (tensorRightUnit F).hom = _
  rw [← Category.assoc (𝟙 F ⊗ₘ t), tensorHom_comp_tensorHom,
    Category.comp_id, SchemeLineSectionUnitFrames.frameScalar_identity,
    tensorRightUnit_action]

/-- The WHOLE original map readback is the SAME scalar on EVERY actual section. -/
theorem tensorSectionMap_frame_apply {X : Scheme.{u}} (F : X.Modules) {T : X.Modules}
    (t : unitObj X ⟶ T) (e : T ≅ unitObj X) (U : X.Opens) (x : Γ(F, U)) :
    (tensorFrameIso F e).hom.val.app (op U)
        ((tensorSectionMap F t).val.app (op U) x) =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (SchemeLineSectionUnitFrames.frameScalar e t)) • x := by
  have h := congrArg (fun a : F ⟶ F => a.val.app (op U) x)
    (tensorSectionMap_frame F t e)
  change _ = _ at h
  exact h.trans ((SchemeUnitScalarAction.unitAction_apply F _ U x).trans (by
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply, one_mul]))

/-- Multiplication by the actual mth tensor power of the original section. -/
def powerSectionTensorMap {X : Scheme.{u}} (F L : X.Modules)
    (s : unitObj X ⟶ L) (m : ℕ) : F ⟶ F ⊗ bundleTensorPower L m :=
  tensorSectionMap F (powerSectionHom s m)

/-- The actual original power map has exactly the original scalar power in
every original frame; this is a WHOLE sheaf-map equality, not input matching. -/
theorem powerSectionTensorMap_frame {X : Scheme.{u}} (F L : X.Modules)
    (s : unitObj X ⟶ L) (e : L ≅ unitObj X) (m : ℕ) :
    powerSectionTensorMap F L s m ≫
      (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)).hom =
        SchemeUnitScalarAction.unitAction F
          (ModularCurves.unitEndomorphismOfTopSection
            (SchemeLineSectionUnitFrames.frameScalar e s ^ m)) := by
  change tensorSectionMap F (powerSectionHom s m) ≫ _ = _
  rw [tensorSectionMap_frame]
  congr 2
  have h := powerSectionHom_frame s e
    (SchemeLineSectionUnitFrames.frameScalar e s)
    (SchemeLineSectionUnitFrames.frameScalar_identity e s) m
  have hscalar := congrArg sectionAtOne h
  change SchemeLineSectionUnitFrames.frameScalar
    (SchemeTensorPowerFrames.powerFrame e m) (powerSectionHom s m) = _ at hscalar
  exact hscalar.trans (by
    change (1 : Γ(X, ⊤)) * X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
        (SchemeLineSectionUnitFrames.frameScalar e s ^ m) = _
    simp)

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
