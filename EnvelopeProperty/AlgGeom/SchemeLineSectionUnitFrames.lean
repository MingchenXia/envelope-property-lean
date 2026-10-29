import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # Actual original sections are canonical frames on their genuine coefficient basic opens -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeLineSectionUnitFrames
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {N : X.Modules}

/-- The actual original top-open coefficient of the SAME whole section in a genuine whole frame. -/
def frameScalar (e : N ≅ unitObj X) (s : unitObj X ⟶ N) : Γ(X, ⊤) :=
  sectionAtOne (s ≫ e.hom)

/-- The ENTIRE original section/frame composite is its actual original scalar. -/
theorem frameScalar_identity (e : N ≅ unitObj X) (s : unitObj X ⟶ N) :
    s ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection (frameScalar e s) :=
  unitHom_eq_globalScalar (s ≫ e.hom)

/-- ANY actual original pullback retains this entire original scalar equality. -/
theorem pullback_frameScalar (f : Y ⟶ X) (e : N ≅ unitObj X) (s : unitObj X ⟶ N) :
    pullbackSectionHom f s ≫
      ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f).hom =
        ModularCurves.unitEndomorphismOfTopSection (f.appTop.hom (frameScalar e s)) := by
  have h := ModularCurves.pullback_unitEndomorphismOfTopSection f (frameScalar e s)
  rw [← frameScalar_identity e s] at h
  simpa only [pullbackSectionHom, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using h

/-- A genuine original coefficient unit derives an actual whole section isomorphism. -/
theorem pullbackSectionHom_isIso_of_isUnit (f : Y ⟶ X)
    (e : N ≅ unitObj X) (s : unitObj X ⟶ N)
    (hc : IsUnit (f.appTop.hom (frameScalar e s))) : IsIso (pullbackSectionHom f s) := by
  let E := (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f
  have hu : IsIso (ModularCurves.unitEndomorphismOfTopSection (f.appTop.hom (frameScalar e s))) := by
    rw [← hc.unit_spec]
    exact (ModularCurves.unitAutomorphismOfTopUnit hc.unit).isIso_hom
  have : IsIso (pullbackSectionHom f s ≫ E.hom) := by
    rw [pullback_frameScalar f e s]
    exact hu
  exact IsIso.of_isIso_comp_right (pullbackSectionHom f s) E.hom

/-- The SAME original top coefficient becomes a true unit on its actual original basic open. -/
theorem basicOpen_appTop_isUnit (r : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen r).ι.appTop.hom r) := by
  let U := X.basicOpen r
  have h := (X.toRingedSpace.isUnit_res_basicOpen r).map
    (X.presheaf.map (eqToHom U.ι_image_top).op).hom
  change IsUnit ((X.presheaf.map (eqToHom U.ι_image_top).op).hom
    ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r)) at h
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h

/-- The ACTUAL original pulled section is a whole isomorphism on the
actual original coefficient basic open, derived without a section-frame certificate. -/
theorem basicOpenSection_isIso (e : N ≅ unitObj X) (s : unitObj X ⟶ N) :
    IsIso (pullbackSectionHom (X.basicOpen (frameScalar e s)).ι s) :=
  pullbackSectionHom_isIso_of_isUnit _ e s (basicOpen_appTop_isUnit _)

/-- The canonical actual original frame is the inverse of the SAME original section. -/
def basicOpenFrame (e : N ≅ unitObj X) (s : unitObj X ⟶ N) :
    (Scheme.Modules.pullback (X.basicOpen (frameScalar e s)).ι).obj N ≅
      unitObj (X.basicOpen (frameScalar e s)).toScheme :=
  letI := basicOpenSection_isIso e s
  (asIso (pullbackSectionHom (X.basicOpen (frameScalar e s)).ι s)).symm

/-- The SAME original pulled section is EXACTLY one in this actual canonical frame. -/
theorem basicOpenFrame_section (e : N ≅ unitObj X) (s : unitObj X ⟶ N) :
    pullbackSectionHom (X.basicOpen (frameScalar e s)).ι s ≫
      (basicOpenFrame e s).hom = 𝟙 _ := by
  let := basicOpenSection_isIso e s
  exact (asIso (pullbackSectionHom (X.basicOpen (frameScalar e s)).ι s)).hom_inv_id

end EnvelopeProperty.SchemeLineSectionUnitFrames
