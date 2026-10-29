import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedParameterScalarCover
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationEquivariantPolarization

/-! # Actual whole same-power section transport by an original group point

The original test-model action and the isomorphism part of its genuine line
linearization are ordinary geometric data. Every point-action map, entire
power pullback iso and transported global section below is constructed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open Scheme.Modules
open scoped CategoryTheory.MonObj
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGroupPointTransport
open NativeTestConfiguration CanonicalGeometry SchemeLineSectionEvaluation
open TestConfigurationLaurentExpansionContinuation
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- Evaluate the SAME original whole action at an actual original group point. -/
def groupPointAction (a : 𝟙_ (Over (Spec (.of k))) ⟶ ProjBerk.nativeMultiplicativeGroup k) :
    C.total ⟶ C.total :=
  (lift (toUnit (totalOver k C.projection) ≫ a) (𝟙 (totalOver k C.projection)) ≫
    originalTestConfigurationTotalAction C).left

/-- The actual original linearization constructs an ENTIRE original pullback
isomorphism for EVERY SAME tensor power, including its genuine unit power. -/
def groupPointPowerIso (M : C.total.Modules)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback (snd (ProjBerk.nativeMultiplicativeGroup k)
          (totalOver k C.projection)).left).obj M)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ ProjBerk.nativeMultiplicativeGroup k) (m : ℕ) :
    (Scheme.Modules.pullback (groupPointAction C a)).obj (bundleTensorPower M m) ≅
      bundleTensorPower M m := by
  let pointMap := lift (toUnit (totalOver k C.projection) ≫ a)
    (𝟙 (totalOver k C.projection))
  have hπ : pointMap.left ≫ (snd (ProjBerk.nativeMultiplicativeGroup k)
      (totalOver k C.projection)).left = 𝟙 C.total :=
    congrArg Over.Hom.left (lift_snd (toUnit (totalOver k C.projection) ≫ a)
      (𝟙 (totalOver k C.projection)))
  let e : (Scheme.Modules.pullback (groupPointAction C a)).obj M ≅ M :=
    (frameFactorIso pointMap.left (originalTestConfigurationTotalAction C).left
      (groupPointAction C a) rfl M).symm ≪≫
      (Scheme.Modules.pullback pointMap.left).mapIso linearization ≪≫
      frameFactorIso pointMap.left (snd (ProjBerk.nativeMultiplicativeGroup k)
        (totalOver k C.projection)).left (𝟙 C.total) hπ M ≪≫
      (Scheme.Modules.pullbackId C.total).app M
  exact TestConfigurationSectionTransport.tensorPowerPullbackIso
    (groupPointAction C a) M m ≪≫ TestConfigurationSectionTransport.tensorPowerIso e m

/-- A SAME original GLOBAL power section is transported by the ACTUAL whole
point action and the internally constructed entire SAME-power isomorphism. -/
def groupPointPowerSectionHom (M : C.total.Modules)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback (snd (ProjBerk.nativeMultiplicativeGroup k)
          (totalOver k C.projection)).left).obj M)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ ProjBerk.nativeMultiplicativeGroup k) (m : ℕ)
    (τ : Γ(bundleTensorPower M m, ⊤)) : unitObj C.total ⟶ bundleTensorPower M m :=
  pullbackSectionHom (groupPointAction C a)
      (SchemeModuleGlobalSections.sectionHom (bundleTensorPower M m) τ) ≫
    (groupPointPowerIso C M linearization a m).hom

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGroupPointTransport
