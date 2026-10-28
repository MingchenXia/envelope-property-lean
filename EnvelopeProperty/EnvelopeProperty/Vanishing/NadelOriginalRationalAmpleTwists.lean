import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Actual positive twists of the same original rational ample tuple

The original B,d,t and original power isomorphism are retained. The new
base line is literally A tensor H^m and its ample numerator is literally
C tensor H^(m*d). The original generators of I tensor B and original
principalization remain the same data in every application.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelOriginalRationalAmpleTwists
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The exact original power relation gives the actual native relation
for every original ample twist, retaining the same B,d,t. -/
def twistedSourcePowerIso {X : Scheme.{u}} (A B C H : X.Modules)
    (d t m : ℕ) (e₀ : bundleTensorPower A d ≅ C ⊗ bundleTensorPower B t) :
    bundleTensorPower (A ⊗ bundleTensorPower H m) d ≅
      (C ⊗ bundleTensorPower H (m * d)) ⊗ bundleTensorPower B t :=
  BundleTensorPowerTensor.powerTensorIso A (bundleTensorPower H m) d ≪≫
    (e₀ ⊗ᵢ BundleTensorPowerPullback.powerMulIso H m d) ≪≫
    (α_ C (bundleTensorPower B t) (bundleTensorPower H (m * d))) ≪≫
    (Iso.refl C ⊗ᵢ (β_ (bundleTensorPower B t) (bundleTensorPower H (m * d)))) ≪≫
    (α_ C (bundleTensorPower H (m * d)) (bundleTensorPower B t)).symm

/-- The actual twisted original source is invertible and has an actual
ample numerator with the same original power data, for every m at least one.
No trace, vanishing group, new generators or numerical class is input. -/
theorem twistedSourceData {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (A : X.Modules) (hA : IsInvertible A)
    (B C H : X.Modules) (hC : SchemeLineAmpleness.IsAmple f C)
    (hH : SchemeLineAmpleness.IsAmple f H) (d t : ℕ) (hd : 0 < d)
    (e₀ : bundleTensorPower A d ≅ C ⊗ bundleTensorPower B t)
    (m : ℕ) (hm : 1 ≤ m) :
    IsInvertible (A ⊗ bundleTensorPower H m) ∧
      SchemeLineAmpleness.IsAmple f (C ⊗ bundleTensorPower H (m * d)) ∧
      Nonempty (bundleTensorPower (A ⊗ bundleTensorPower H m) d ≅
        (C ⊗ bundleTensorPower H (m * d)) ⊗ bundleTensorPower B t) := by
  have hHm : IsInvertible (bundleTensorPower H m) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible m
  have hmd : 0 < m * d := Nat.mul_pos (Nat.zero_lt_one.trans_le hm) hd
  refine ⟨(hA.tensorObj hHm).of_iso (ModularCurves.monoidalTensorObjIso A _), ?_,
    ⟨twistedSourcePowerIso A B C H d t m e₀⟩⟩
  exact AmpleTensorLines.isAmple_tensor f C (bundleTensorPower H (m * d)) hC
    (AmpleLinePositivePowers.isAmple_tensorPower f H hH (m * d) hmd)

end EnvelopeProperty.Vanishing.NadelOriginalRationalAmpleTwists
