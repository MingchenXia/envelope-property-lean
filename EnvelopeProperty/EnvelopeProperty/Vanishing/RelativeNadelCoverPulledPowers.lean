import EnvelopeProperty.AlgGeom.AmpleTensorLines

/-! # Actual eventual original ample twists on an integral relative source -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverPulledPowers
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- Original eventual finite generation suffices on the actual integral
source, so no domain condition on the original affine base is needed. -/
theorem exists_eventual_isAmple_tensor_pullback {R : Type u} [CommRing R]
    {X W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    (p : X ⟶ Spec (.of R)) (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple p H)
    (f : W ⟶ X) (B : W.Modules) (hB : SchemeLineAmpleness.IsAmple (f ≫ p) B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SchemeLineAmpleness.IsAmple (f ≫ p)
      (B ⊗ (pullback f).obj (bundleTensorPower H n)) := by
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p H hH
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections f G
  have hK : K.IsFiniteType := ⟨hG.finite⟩
  exact AmpleTensorLines.isAmple_tensor_of_generatingSections (f ≫ p) B
    ((pullback f).obj (bundleTensorPower H n)) hB
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible n).pullback f) K hK

end EnvelopeProperty.Vanishing.RelativeNadelCoverPulledPowers
