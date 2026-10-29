import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionBaseChange
import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

/-! # Genuine original whole line maps as global Hom-line sections

The whole-map/global-section equivalence and its actual pullback comparison are
constructed from native dual evaluation and the canonical structure-line unit.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerSections
open SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unitHom_ext {X : Scheme.{u}} {M : X.Modules}
    {a b : unitObj X ⟶ M} (h : sectionAtOne a = sectionAtOne b) : a = b := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (show Γ(X, ⊤) from 1)
  have hb := PresheafOfModules.naturality_apply b.val i (show Γ(X, ⊤) from 1)
  change a.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) =
    M.presheaf.map i (sectionAtOne a) at ha
  change b.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) =
    M.presheaf.map i (sectionAtOne b) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun z => M.presheaf.map i z) h).trans hb.symm)

/-- Actual structure-line maps are precisely the actual whole global sections. -/
def topSectionEquiv {X : Scheme.{u}} (M : X.Modules) :
    (unitObj X ⟶ M) ≃ Γ(M, ⊤) where
  toFun := sectionAtOne
  invFun := topSectionHom M
  left_inv _a := unitHom_ext (topSectionHom_app_top_apply_one M _)
  right_inv := topSectionHom_app_top_apply_one M

/-- The actual native Hom line, using the original tensor sheaf and original dual. -/
abbrev homLine {X : Scheme.{u}} (A B : X.Modules) : X.Modules :=
  Scheme.Modules.tensorObj B (dualObj A)

/-- The original whole Hom set is identified with the original actual global Hom-line sections. -/
def homSectionEquiv {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) :
    (A ⟶ B) ≃ Γ(homLine A B, ⊤) :=
  (SchemeInvertibleHomSection.equiv A hA B).trans (topSectionEquiv (homLine A B))

/-- The evaluation-preserving actual pullback comparison for the original Hom line. -/
def pulledHomLineIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) :
    (Scheme.Modules.pullback f).obj (homLine A B) ≅
      homLine ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B) := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f
  exact (Scheme.Modules.pullback f).mapIso (ModularCurves.monoidalTensorObjIso B (dualObj A)).symm ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) B (dualObj A)).symm ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback f).obj B)
      (SchemeInvertibleHomSection.rightDualPullbackEvaluationIso f A hA) ≪≫
    ModularCurves.monoidalTensorObjIso ((Scheme.Modules.pullback f).obj B)
      (dualObj ((Scheme.Modules.pullback f).obj A))

private theorem pullbackUnitComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let : (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f
    (ModularCurves.monoidalUnitObjIso Y).hom ≫ (pullbackUnitIso f).inv =
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫
        (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f
  have h := congrArg Iso.hom (pullback_monoidalUnitObjIso f)
  change (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv ≫
      (ModularCurves.monoidalUnitObjIso Y).hom =
      (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).hom ≫
        (pullbackUnitIso f).hom at h
  apply (cancel_epi (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv).mp
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- The actual Hom-section correspondence commutes with genuine whole pullback. -/
theorem equiv_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) (a : A ⟶ B) :
    SchemeInvertibleHomSection.equiv ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
      ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).map a) =
      pullbackSectionHom f (SchemeInvertibleHomSection.equiv A hA B a) ≫
        (pulledHomLineIso f A hA B).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f
  apply (cancel_epi (ModularCurves.monoidalUnitObjIso Y).hom).mp
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso
    ((Scheme.Modules.pullback f).obj B) (dualObj ((Scheme.Modules.pullback f).obj A))).inv).mp
  simp only [Category.assoc]
  rw [SchemeInvertibleHomSection.equiv_pullback_monoidal f A hA B a]
  dsimp only [pulledHomLineIso, pullbackSectionHom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    whiskerLeftIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc (ModularCurves.monoidalUnitObjIso Y).hom,
    pullbackUnitComparison]
  simp only [Category.assoc]

/-- The actual original whole map's section is the canonical pulled original
section under the actual evaluation-preserving Hom-line comparison. -/
theorem homSectionEquiv_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) (a : A ⟶ B) :
    homSectionEquiv ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
      ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).map a) =
      (pulledHomLineIso f A hA B).hom.app ⊤
        (affinePullbackUnitTop f (homLine A B) (homSectionEquiv A hA B a)) := by
  change sectionAtOne (SchemeInvertibleHomSection.equiv
    ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
    ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).map a)) = _
  rw [equiv_pullback]
  change (pulledHomLineIso f A hA B).hom.app ⊤
      (sectionAtOne (pullbackSectionHom f (SchemeInvertibleHomSection.equiv A hA B a))) = _
  have h := Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
    f (homLine A B) (homSectionEquiv A hA B a)
  change affinePullbackUnitTop f (homLine A B) (sectionAtOne (SchemeInvertibleHomSection.equiv A hA B a)) =
      sectionAtOne (pullbackSectionHom f
        (topSectionHom (homLine A B) (sectionAtOne (SchemeInvertibleHomSection.equiv A hA B a)))) at h
  have hrec : topSectionHom (homLine A B) (sectionAtOne (SchemeInvertibleHomSection.equiv A hA B a)) =
      SchemeInvertibleHomSection.equiv A hA B a :=
    unitHom_ext (topSectionHom_app_top_apply_one (homLine A B) _)
  rw [hrec] at h
  exact congrArg ((pulledHomLineIso f A hA B).hom.app ⊤) h.symm

end EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerSections
