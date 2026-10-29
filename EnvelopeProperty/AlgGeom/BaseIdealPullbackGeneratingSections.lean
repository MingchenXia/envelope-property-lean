import EnvelopeProperty.AlgGeom.ProjectiveBaseIdealEpimorphism
import EnvelopeProperty.AlgGeom.IdealModulePullbackGlobalGeneration

/-! # Actual finite global generation of pulled whole base-ideal polarizations -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.BaseIdealPullbackGeneratingSections
open Scheme.Modules InvertibleSheafBaseIdeal ProjectiveBaseIdealEpimorphism
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Actual dual evaluation cancels the original two tensor factors. -/
def cancelDualTensorIso {X : Scheme.{u}} (M L : X.Modules) (hL : IsInvertible L) :
    (tensorRight L).obj ((tensorRight (dualObj L)).obj M) ≅ M := by
  let := Scheme.Modules.symmetricCategory X
  exact α_ M (dualObj L) L ≪≫
    (Iso.refl M ⊗ᵢ ((β_ (dualObj L) L) ≪≫ hL.monoidalEvaluationIso)) ≪≫ ρ_ M

/-- The same cancellation after the actual monoidal pullback comparison. -/
def pullbackCancelDualTensorIso {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (M L : X.Modules) (hL : IsInvertible L) :
    (tensorRight (C := Z.Modules) ((pullback μ).obj L)).obj
      ((pullback μ).obj ((tensorRight (dualObj L)).obj M)) ≅ (pullback μ).obj M := by
  let : (pullback μ).Monoidal := pullbackMonoidal μ
  exact Functor.Monoidal.μIso (pullback μ) ((tensorRight (dualObj L)).obj M) L ≪≫
    (pullback μ).mapIso (cancelDualTensorIso M L hL)

/-- Pull the original whole ideal epimorphism, use the true geometric comap,
then tensor and cancel; every map is the actual original categorical map. -/
def dividedEpimorphism {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (M L : X.Modules) (hL : IsInvertible L) (I : X.IdealSheafData)
    (p : (tensorRight (dualObj L)).obj M ⟶ I.toModules) :
    (pullback μ).obj M ⟶
      (tensorRight (C := Z.Modules) ((pullback μ).obj L)).obj (I.comap μ).toModules :=
  (pullbackCancelDualTensorIso μ M L hL).inv ≫
    (tensorRight ((pullback μ).obj L)).map
      ((pullback μ).map p ≫ I.toModulesComapPullbackMap μ)

/-- No flatness is needed: actual pullback and invertible tensoring preserve epi. -/
theorem dividedEpimorphism_epi {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (M L : X.Modules) (hL : IsInvertible L) (I : X.IdealSheafData)
    (p : (tensorRight (dualObj L)).obj M ⟶ I.toModules) [Epi p] :
    Epi (dividedEpimorphism μ M L hL I p) := by
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u,u} (pullback μ) :=
    (pullbackPushforwardAdjunction μ).leftAdjoint_preservesColimits
  let : Epi (I.toModulesComapPullbackMap μ) := I.toModulesComapPullbackMap_epi μ
  let : (tensorRight ((pullback μ).obj L)).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ (hL.pullback μ)
  unfold dividedEpimorphism
  infer_instance

/-- One original finite global section index set gives TRUE global generators
of the WHOLE actual pulled base-ideal polarization under ANY original morphism. -/
theorem exists_finite_original_generatingSections {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) (μ : Z ⟶ X) :
    ∃ (G : Finset Γ(L, ⊤))
      (H : ((tensorRight (C := Z.Modules) ((pullback μ).obj L)).obj
        ((baseIdeal hL).comap μ).toModules).GeneratingSections),
      H.IsFiniteType ∧ H.I = G := by
  obtain ⟨G, p, hp, _hc⟩ := exists_finite_original_baseIdeal_epi f hf L hL
  let M : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) G
  let : Epi p := hp
  let q := dividedEpimorphism μ M L hL (baseIdeal hL) p
  have hq : Epi q := dividedEpimorphism_epi μ M L hL (baseIdeal hL) p
  let G₀ := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) G
  let : G₀.IsFiniteType := ⟨inferInstanceAs (Finite G)⟩
  let H₀ := ClosedProjectiveGlobalGeneration.pullback_generatingSections μ G₀
  let : H₀.IsFiniteType :=
    ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType μ G₀
  let H := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ H₀ q hq
  exact ⟨G, H, ⟨inferInstanceAs (Finite G)⟩, rfl⟩

end EnvelopeProperty.BaseIdealPullbackGeneratingSections
