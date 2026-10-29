import EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackGeneration
import EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackProjective
import EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackTensor
/-! # Finite pullback of the actual original ample line on the whole covering scheme

Original target projectivity, whole-source very ampleness, actual coherent
generators and the original affine counit are all derived internally.
No component, integral-source hypothesis or ampleness certificate is supplied.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelFiniteAmplePullback
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The actual original finite pullback of the original ample line is ample
on the entire original covering scheme, with no component selected. -/
theorem isAmple_pullback {R : Type u} [CommRing R] [IsDomain R] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] :
    SchemeLineAmpleness.IsAmple (π ≫ p) ((pullback π).obj L) := by
  have hP := hL.isInvertible.pullback π
  obtain ⟨H, hH⟩ := NadelFiniteAmplePullbackProjective.exists_isVeryAmple_line p L hL π
  let D := dualObj H
  have hD : IsInvertible D := hH.isInvertible.dual
  let : D.IsQuasicoherent := hD.isQuasicoherent
  let : D.IsFiniteType := @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _ _ _ _ _ _ D hD.isFinitePresentation
  obtain ⟨N, hN⟩ := NadelFiniteAmplePullbackGeneration.exists_eventual_generatingSections p L hL π D
  obtain ⟨G, hG⟩ := hN (N + 1) (Nat.le_succ N)
  exact ⟨hP, N + 1, Nat.succ_pos N,
    NadelFiniteAmplePullbackTensor.isVeryAmple_of_inverse_twist_generated (π ≫ p) H _ hH
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hP (N + 1)) G hG⟩
end EnvelopeProperty.Vanishing.NadelFiniteAmplePullback
