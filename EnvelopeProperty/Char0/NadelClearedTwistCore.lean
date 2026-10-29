import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Actual original cleared powers for the relative ample Nadel consumer

The line, polarization and ample cleared factor are native scheme modules.
All original tensor and iterated-power comparisons are constructed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
universe u
namespace EnvelopeProperty.Char0.NadelClearedTwist
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

/-- The literal original line in a positive projective regularity twist. -/
def line {X : Scheme.{u}} (H L : X.Modules) (e m : ℕ) : X.Modules :=
  bundleTensorPower H e ⊗ bundleTensorPower L m

/-- The actual original power used to generate the original ideal. -/
def polarization {X : Scheme.{u}} (L : X.Modules) (p : ℕ) : X.Modules := bundleTensorPower L p

/-- The SAME actual original ample factor after clearing by original p. -/
def clearedLine {X : Scheme.{u}} (H : X.Modules) (e p : ℕ) : X.Modules :=
  bundleTensorPower H (p * e)

theorem coefficient_nonneg (m p : ℕ) : 0 ≤ (m : ℚ) / p :=
  div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg p)

theorem clearingCoefficient_eq (m p : ℕ) (hp : 0 < p) :
    (p : ℚ) * ((m : ℚ) / p) = (m : ℚ) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  field_simp [hp0]

/-- Genuine tensor-power distribution and the original exponent equalities
produce the actual cleared power iso; it is never a consumer premise. -/
def clearingIso {X : Scheme.{u}} (H L : X.Modules) (e m p : ℕ) :
    bundleTensorPower (line H L e m) p ≅
      clearedLine H e p ⊗ bundleTensorPower (polarization L p) m :=
  BundleTensorPowerTensor.powerTensorIso (bundleTensorPower H e) (bundleTensorPower L m) p ≪≫
    ((BundleTensorPowerPullback.powerMulIso H e p ≪≫
      eqToIso (congrArg (bundleTensorPower H) (Nat.mul_comm e p))) ⊗ᵢ
      (BundleTensorPowerPullback.powerMulIso L m p ≪≫
        eqToIso (congrArg (bundleTensorPower L) (Nat.mul_comm m p)) ≪≫
        (BundleTensorPowerPullback.powerMulIso L p m).symm))

theorem line_isInvertible {X : Scheme.{u}} (H L : X.Modules)
    (hH : IsInvertible H) (hL : IsInvertible L) (e m : ℕ) : IsInvertible (line H L e m) :=
  ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hH e).tensorObj
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)).of_iso
      (ModularCurves.monoidalTensorObjIso _ _)

theorem polarization_isInvertible {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (p : ℕ) : IsInvertible (polarization L p) :=
  TensorPowerBaseIdealGrading.tensorPower_isInvertible hL p

/-- The SAME actual cleared factor is geometrically ample from original
hyperplane ampleness and the genuine positive original exponents. -/
theorem clearedLine_isAmple {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of R)) (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple π H)
    (e p : ℕ) (he : 0 < e) (hp : 0 < p) :
    SchemeLineAmpleness.IsAmple π (clearedLine H e p) :=
  AmpleLinePositivePowers.isAmple_tensorPower π H hH (p * e) (Nat.mul_pos hp he)

end EnvelopeProperty.Char0.NadelClearedTwist
