import EnvelopeProperty.Vanishing.NadelNefBigGlobalGenerators
import EnvelopeProperty.Vanishing.NadelNefBigGlobalFrameCore
import ModularCurves.ForMathlib.PullbackUnitMonoidal

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalFrames
open NadelNefBigGlobalGenerators SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f

def untwist {X : Scheme.{u}} (M B : X.Modules) (e : B ≅ unitObj X) : M ⊗ B ≅ M :=
  whiskerLeftIso M (e ≪≫ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ M

private theorem pullbackUnit_square {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackUnitIso f).hom ≫ (ModularCurves.monoidalUnitObjIso Y).inv =
      (pullback f).map (ModularCurves.monoidalUnitObjIso X).inv ≫
        (Functor.Monoidal.εIso (pullback f)).inv := by
  let F := pullback f
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  have h := congrArg Iso.hom (pullback_monoidalUnitObjIso f)
  change (Functor.Monoidal.εIso F).inv ≫ uY.hom = F.map uX.hom ≫ (pullbackUnitIso f).hom at h
  apply (cancel_epi (F.map uX.hom)).mp
  change F.map uX.hom ≫ (pullbackUnitIso f).hom ≫ uY.inv =
    F.map uX.hom ≫ F.map uX.inv ≫ (Functor.Monoidal.εIso F).inv
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

theorem comapTensorMap_untwist {X Y : Scheme.{u}} (D : X.IdealSheafData) (f : Y ⟶ X)
    (B : X.Modules) (e : B ≅ unitObj X) :
    comapTensorMap D f B ≫
        (untwist (D.comap f).toModules ((pullback f).obj B)
          ((pullback f).mapIso e ≪≫ pullbackUnitIso f)).hom =
      (pullback f).map (untwist D.toModules B e).hom ≫ D.toModulesComapPullbackMap f := by
  let F := pullback f
  let eX := e ≪≫ (ModularCurves.monoidalUnitObjIso X).symm
  let eY := (F.mapIso e ≪≫ pullbackUnitIso f) ≪≫ (ModularCurves.monoidalUnitObjIso Y).symm
  have he : eY.hom = F.map eX.hom ≫ (Functor.Monoidal.εIso F).inv := by
    simp only [eX, eY, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    rw [pullbackUnit_square]
  change (Functor.Monoidal.μIso F D.toModules B).inv ≫
      D.toModulesComapPullbackMap f ▷ F.obj B ≫
      (D.comap f).toModules ◁ eY.hom ≫ (ρ_ (D.comap f).toModules).hom =
    F.map (D.toModules ◁ eX.hom ≫ (ρ_ D.toModules).hom) ≫ D.toModulesComapPullbackMap f
  rw [he]
  exact NadelNefBigGlobalFrameCore.map_right_frame_comp F D.toModules B (D.comap f).toModules
    (D.toModulesComapPullbackMap f) eX.hom

theorem generatorHom_comapGenerators_untwist {X Y : Scheme.{u}} (D : X.IdealSheafData)
    (f : Y ⟶ X) (B : X.Modules) (hB : IsInvertible B) (e : B ≅ unitObj X)
    (G : (D.toModules ⊗ B).GeneratingSections) (i : G.I) :
    generatorHom (comapGenerators D f B hB G) i ≫
        (untwist (D.comap f).toModules ((pullback f).obj B)
          ((pullback f).mapIso e ≪≫ pullbackUnitIso f)).hom =
      pullbackSectionHom f (generatorHom G i ≫ (untwist D.toModules B e).hom) ≫
        D.toModulesComapPullbackMap f := by
  rw [generatorHom_generators, Category.assoc, comapTensorMap_untwist]
  change ((pullbackUnitIso f).inv ≫ (pullback f).map (generatorHom G i)) ≫
      (pullback f).map (untwist D.toModules B e).hom ≫ D.toModulesComapPullbackMap f =
    ((pullbackUnitIso f).inv ≫ (pullback f).map (generatorHom G i ≫
      (untwist D.toModules B e).hom)) ≫ D.toModulesComapPullbackMap f
  rw [Functor.map_comp]
  simp only [Category.assoc]
end EnvelopeProperty.Vanishing.NadelNefBigGlobalFrames
