import EnvelopeProperty.Vanishing.NadelFiniteAmpleTensor
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackTensor
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

theorem isVeryAmple_of_inverse_twist_generated {R : Type u} [CommRing R] [IsDomain R]
    {W : Scheme.{u}} (q : W ⟶ Spec (.of R)) (H B : W.Modules)
    (hH : SchemeLineAmpleness.IsVeryAmple q H) (hB : IsInvertible B)
    (G : (dualObj H ⊗ B).GeneratingSections) (hG : G.IsFiniteType) :
    SchemeLineAmpleness.IsVeryAmple q B := by
  have hHB : IsInvertible (dualObj H ⊗ B) :=
    (hH.isInvertible.dual.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso (dualObj H) B)
  have hV := NadelFiniteAmpleTensor.isVeryAmple_tensor q H (dualObj H ⊗ B) hH hHB G hG
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    ((α_ H (dualObj H) B).symm ≪≫ (hH.isInvertible.monoidalEvaluationIso ⊗ᵢ Iso.refl B) ≪≫ λ_ B)
end EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackTensor
