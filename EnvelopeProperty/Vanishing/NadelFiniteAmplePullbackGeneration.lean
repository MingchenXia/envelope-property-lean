import EnvelopeProperty.Vanishing.NadelAmpleCoherentGeneration
import EnvelopeProperty.Vanishing.NadelFinitePushforward
import EnvelopeProperty.Vanishing.NadelAffineCounit
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
/-! # Actual finite pullback eventually generates every original coherent twist on the whole source -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackGeneration
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
noncomputable local instance {X W : Scheme.{u}} (π : W ⟶ X) :
    (pullback π).Monoidal := pullbackMonoidal π

/-- The whole original finite pullback eventually generates every original
finite-type quasicoherent twist; all sections and the actual counit are internal. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] (M : W.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (M ⊗ bundleTensorPower ((pullback π).obj L) m).GeneratingSections,
        G.IsFiniteType := by
  let Q := (pushforward π).obj M
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom π
  let : Q.IsFiniteType := NadelFinitePushforward.isFiniteType π M
  obtain ⟨N, hN⟩ := NadelAmpleCoherentGeneration.exists_eventual_generatingSections p L hL Q
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨G, hG⟩ := hN m hm
  let F := pullback π
  let B := F.obj (bundleTensorPower L m)
  have hB : IsInvertible B :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL.isInvertible m).pullback π
  let : (tensorRight B).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence B hB
  let e := (pullbackPushforwardAdjunction π).counit.app M
  let : Epi e := NadelAffineCounit.counit_epi π M
  let E0 : F.obj (bundleTensorPower L m ⊗ Q) ≅ F.obj Q ⊗ B :=
    F.mapIso (β_ (bundleTensorPower L m) Q) ≪≫
      (Functor.Monoidal.μIso F Q (bundleTensorPower L m)).symm
  let E1 : M ⊗ B ≅ M ⊗ bundleTensorPower (F.obj L) m :=
    Iso.refl M ⊗ᵢ BundleTensorPowerPullback.pullbackIso π L m
  let : Epi E0.hom := @CategoryTheory.IsIso.epi_of_iso W.Modules _ _ _ E0.hom E0.isIso_hom
  let : Epi E1.hom := @CategoryTheory.IsIso.epi_of_iso W.Modules _ _ _ E1.hom E1.isIso_hom
  have he : Epi ((tensorRight B).map e) := inferInstance
  let q : F.obj (bundleTensorPower L m ⊗ Q) ⟶ M ⊗ bundleTensorPower (F.obj L) m :=
    E0.hom ≫ (tensorRight B).map e ≫ E1.hom
  have hq : Epi q := by
    let : Epi ((tensorRight B).map e) := he
    dsimp only [q]
    infer_instance
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections π G
  let K := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ H q hq
  exact ⟨K, ⟨hG.finite⟩⟩
end EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackGeneration
