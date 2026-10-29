import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationIsoLineTopSectionCoherence
import EnvelopeProperty.AlgGeom.SchemeUnitScalarActionBaseChange

/-!
# Intrinsic PSH Comparison Continuation Iso Line Top Section Scalars

Actual global-function scalars on the SAME original top-section iso.
Route: owned `iso-line-top-section-scalars-route.tex`. -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual global scalar multiplication gives its genuine whole section Hom. -/
theorem sectionHom_global_smul {Y : Scheme.{u}} (L : Y.Modules)
    (c : Γ(Y, ⊤)) (s : Γ(L, ⊤)) :
    SchemeModuleGlobalSections.sectionHom L (c • s) =
      SchemeModuleGlobalSections.sectionHom L s ≫ SchemeUnitScalarAction.globalScalarAction L c := by
  have hc : (SchemeUnitScalarAction.globalScalarAction L c).val.app (op ⊤) s = c • s := by
    rw [SchemeUnitScalarAction.globalScalarAction_apply]
    exact congrArg (fun r : Γ(Y, ⊤) => r • s)
      (ConcreteCategory.congr_hom (Y.presheaf.map_id (op ⊤)) c)
  exact ((SchemeModuleGlobalSections.sectionHom_comp s
    (SchemeUnitScalarAction.globalScalarAction L c)).trans
      (congrArg (SchemeModuleGlobalSections.sectionHom L) hc)).symm

/-- Every actual module map commutes with the same actual regular function's whole actions. -/
theorem globalScalarAction_naturality {W : Scheme.{u}} {A B : W.Modules}
    (c : Γ(W, ⊤)) (b : A ⟶ B) :
    SchemeUnitScalarAction.globalScalarAction A c ≫ b =
      b ≫ SchemeUnitScalarAction.globalScalarAction B c := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change b.val.app (op U) ((SchemeUnitScalarAction.globalScalarAction A c).val.app (op U) m) =
    (SchemeUnitScalarAction.globalScalarAction B c).val.app (op U) (b.val.app (op U) m)
  rw [SchemeUnitScalarAction.globalScalarAction_apply,
    SchemeUnitScalarAction.globalScalarAction_apply]
  exact (b.val.app (op U)).hom.map_smul _ _

/-- The SAME original H0 plus actual whole line iso preserves actual pulled global-function scalars. -/
theorem isoLineTopSections_global_smul {Z Y : Scheme.{u}} (e : Z ≅ Y)
    (L : Y.Modules) (P : Z.Modules) (a : (pullback e.hom).obj L ≅ P)
    (c : Γ(Y, ⊤)) (s : Γ(L, ⊤)) :
    ((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom (c • s) =
      e.hom.appTop c • ((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom s := by
  let H := ((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom
  have hp : pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L (c • s)) =
      pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L s) ≫
        SchemeUnitScalarAction.globalScalarAction ((pullback e.hom).obj L) (e.hom.appTop c) := by
    rw [sectionHom_global_smul]
    simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
    rw [SchemeUnitScalarActionBaseChange.globalScalarAction_pullback]
  have hwhole : pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L (c • s)) ≫ a.hom =
      (pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L s) ≫ a.hom) ≫
        SchemeUnitScalarAction.globalScalarAction P (e.hom.appTop c) := by
    rw [hp, Category.assoc, globalScalarAction_naturality]
    simp only [Category.assoc]
  have hs : SchemeModuleGlobalSections.sectionHom P (H s) =
      pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L s) ≫ a.hom :=
    isoLineTopSections_topSectionHom e L P a s
  have hcs : SchemeModuleGlobalSections.sectionHom P (H (c • s)) =
      pullbackSectionHom e.hom (SchemeModuleGlobalSections.sectionHom L (c • s)) ≫ a.hom :=
    isoLineTopSections_topSectionHom e L P a (c • s)
  have he := hcs.trans (hwhole.trans (congrArg (fun β => β ≫
    SchemeUnitScalarAction.globalScalarAction P (e.hom.appTop c)) hs.symm))
  have hleft : sectionAtOne (SchemeModuleGlobalSections.sectionHom P (H (c • s))) =
      H (c • s) := Scheme.Modules.topSectionHom_app_top_apply_one _ _
  have hright : sectionAtOne (SchemeModuleGlobalSections.sectionHom P (H s) ≫
      SchemeUnitScalarAction.globalScalarAction P (e.hom.appTop c)) = e.hom.appTop c • H s := by
    change (SchemeUnitScalarAction.globalScalarAction P (e.hom.appTop c)).val.app (op ⊤)
      (sectionAtOne (SchemeModuleGlobalSections.sectionHom P (H s))) = _
    have hvalue : sectionAtOne (SchemeModuleGlobalSections.sectionHom P (H s)) = H s :=
      Scheme.Modules.topSectionHom_app_top_apply_one _ _
    rw [hvalue, SchemeUnitScalarAction.globalScalarAction_apply]
    exact congrArg (fun r : Γ(Z, ⊤) => r • H s)
      (ConcreteCategory.congr_hom (Z.presheaf.map_id (op ⊤)) (e.hom.appTop c))
  exact hleft.symm.trans ((congrArg sectionAtOne he).trans hright)

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.sectionHom_global_smul
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.sectionHom_global_smul
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.globalScalarAction_naturality
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.globalScalarAction_naturality
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_global_smul
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_global_smul
