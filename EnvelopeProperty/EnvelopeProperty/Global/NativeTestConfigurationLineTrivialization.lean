import EnvelopeProperty.Global.NativeTestConfigurationActionFibreDiagrams
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Genuine source-linearization producer for the WHOLE original noncentral-open module isomorphism -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

/-- The WHOLE original source action map on the unchanged original total scheme. -/
def lineActionMap : (ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection).left ⟶ C.total := by
  let := C.action
  exact (ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup k)
    (X := totalOver k C.projection)).left

/-- The WHOLE original last projection of the unchanged original action product. -/
def lineProjectionMap : (ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection).left ⟶ C.total :=
  (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left

/-- The SAME original whole unit-fibre projection of the original unit-open product trivialization. -/
def unitOpenFibreProjection : C.unitOpenOver ⟶ fibreOneOver k C.projection :=
  C.unitOpenFibreIso.hom ≫
    snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection)

/-- The original native action composite of the WHOLE original lift is EXACTLY the original open inclusion. -/
theorem lineActionLift_action : C.unitOpenActionLift.left ≫ C.lineActionMap =
    C.unitOpenInclusion.left :=
  congrArg Over.Hom.left C.unitOpenActionLift_action

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The WHOLE original last projection composite factors through the SAME original fibre ONE. -/
theorem lineActionLift_projection : C.unitOpenActionLift.left ≫ C.lineProjectionMap =
    C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left := by
  have h := congrArg Over.Hom.left C.unitOpenActionLift_projection
  simpa only [unitOpenFibreProjection, lineProjectionMap, Over.comp_left, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resulting whole original source X map is the ORIGINAL product trivialization's X projection. -/
theorem lineActionLift_original : C.unitOpenFibreProjection.left ≫ C.fibreOneIso.hom.left =
    C.unitOpenOriginalProjection.left := by
  have h := congrArg Over.Hom.left C.unitOpenOriginalProjection_eq
  simpa only [unitOpenFibreProjection, lineProjectionMap, Over.comp_left, Category.assoc] using h.symm

private def pullbackActionIso (M : C.total.Modules)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M) :
    (Scheme.Modules.pullback (C.unitOpenActionLift.left ≫ C.lineActionMap)).obj M ≅
      (Scheme.Modules.pullback (C.unitOpenActionLift.left ≫ C.lineProjectionMap)).obj M :=
  ((Scheme.Modules.pullbackComp C.unitOpenActionLift.left C.lineActionMap).app M).symm ≪≫
    (Scheme.Modules.pullback C.unitOpenActionLift.left).mapIso α ≪≫
      (Scheme.Modules.pullbackComp C.unitOpenActionLift.left C.lineProjectionMap).app M

/-- Actual ORIGINAL source action linearization and ORIGINAL fibre-one module identification
construct the ENTIRE ORIGINAL noncentral-open module isomorphism. No desired open/generic
trivialization is supplied; this stronger statement works for ANY module, hence original lines. -/
def unitOpenLineIso (M : C.total.Modules) (L : X.left.Modules)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) :
    (Scheme.Modules.pullback C.unitOpenInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.unitOpenOriginalProjection.left).obj L :=
  (Scheme.Modules.pullbackCongr C.lineActionLift_action.symm).app M ≪≫
    C.pullbackActionIso M α ≪≫
      (Scheme.Modules.pullbackCongr C.lineActionLift_projection).app M ≪≫
        ((Scheme.Modules.pullbackComp C.unitOpenFibreProjection.left
          C.fibreOneInclusion.left).app M).symm ≪≫
          (Scheme.Modules.pullback C.unitOpenFibreProjection.left).mapIso e₁ ≪≫
            (Scheme.Modules.pullbackComp C.unitOpenFibreProjection.left
              C.fibreOneIso.hom.left).app L ≪≫
                (Scheme.Modules.pullbackCongr C.lineActionLift_original).app L

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
