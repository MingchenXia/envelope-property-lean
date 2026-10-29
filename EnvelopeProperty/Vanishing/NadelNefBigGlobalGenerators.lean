import EnvelopeProperty.AlgGeom.IdealModulePullbackEpimorphism
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections

/-! # Actual ideal--line comap generators with exact whole original basis maps -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalGenerators
open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f
variable {X Y : Scheme.{u}} (D : X.IdealSheafData) (f : Y ⟶ X) (B : X.Modules)

def comapTensorMap : (pullback f).obj (D.toModules ⊗ B) ⟶
    (D.comap f).toModules ⊗ (pullback f).obj B :=
  (Functor.Monoidal.μIso (pullback f) D.toModules B).inv ≫
    (tensorRight ((pullback f).obj B)).map (D.toModulesComapPullbackMap f)

theorem comapTensorMap_epi (hB : IsInvertible B) : Epi (comapTensorMap D f B) := by
  let C := (pullback f).obj B
  let : (tensorRight C).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence C (hB.pullback f)
  let : Epi (D.toModulesComapPullbackMap f) := D.toModulesComapPullbackMap_epi f
  have hp : Epi ((tensorRight C).map (D.toModulesComapPullbackMap f)) := inferInstance
  let := hp
  exact CategoryTheory.epi_comp (Functor.Monoidal.μIso (pullback f) D.toModules B).inv
    ((tensorRight C).map (D.toModulesComapPullbackMap f))

def comapGenerators (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections) :
    ((D.comap f).toModules ⊗ (pullback f).obj B).GeneratingSections :=
  @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G) (comapTensorMap D f B)
    (comapTensorMap_epi D f B hB)

theorem generators_isFiniteType (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    [hG : G.IsFiniteType] : (comapGenerators D f B hB G).IsFiniteType := by
  constructor
  exact hG.finite

theorem generatorHom_generators (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    (i : G.I) : generatorHom (comapGenerators D f B hB G) i =
      pullbackSectionHom f (generatorHom G i) ≫ comapTensorMap D f B := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections f G
  have h := @generatorHom_ofEpi Y _ _ H (comapTensorMap D f B) (comapTensorMap_epi D f B hB) i
  exact h.trans (congrArg (fun q => q ≫ comapTensorMap D f B) (generatorHom_pullback f G i))
end EnvelopeProperty.Vanishing.NadelNefBigGlobalGenerators
