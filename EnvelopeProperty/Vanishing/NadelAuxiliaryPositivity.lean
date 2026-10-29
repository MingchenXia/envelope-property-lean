import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration

/-! # Actual positive auxiliary systems for the original Nadel component lines

The original geometric ample datum produces the exponent and every actual
very-ample comparison. No auxiliary line, generator family or embedding is
supplied. Integrality is the original Nadel geometry, available also on the
actual principalization by `NadelPrincipalization.last_isIntegral`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryPositivity
open CanonicalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of R)) (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple p H)

include hH

/-- Every sufficiently large original ample power, with the SAME original
invertible module as first tensor factor, is geometrically very ample. -/
theorem exists_eventual_twist_isVeryAmple (M : X.Modules) (hM : IsInvertible M) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      SchemeLineAmpleness.IsVeryAmple p (M ⊗ bundleTensorPower H r) := by
  obtain ⟨N, hN⟩ := AmpleLineTwistGeneration.exists_eventual_isVeryAmple p H hH M hM
  exact ⟨N, fun r hr => SchemeAmpleClosedRestriction.veryAmple_of_iso (hN r hr)
    (β_ (bundleTensorPower H r) M)⟩

/-- One actual positive original exponent internally supplies very-ample
auxiliary systems for every original positive denominator in a finite family. -/
theorem exists_uniform_auxiliary_power {ι : Type v} [Finite ι]
    (M : ι → X.Modules) (hM : ∀ i, IsInvertible (M i))
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      ∀ i, SchemeLineAmpleness.IsVeryAmple p
        (bundleTensorPower (bundleTensorPower H r) (m i) ⊗ M i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨N, hN⟩ :=
    AmpleLineTwistGeneration.exists_uniform_eventual_isVeryAmple p H hH M hM
  obtain ⟨T, hT⟩ := AmpleTensorLines.exists_eventual_isVeryAmple p H hH
  let r := max N T + 1
  have hr : 0 < r := by dsimp [r]; omega
  have hNr : N ≤ r := by dsimp [r]; omega
  have hTr : T ≤ r := by dsimp [r]; omega
  refine ⟨r, hr, hT r hTr, fun i => ?_⟩
  have hOne : 1 ≤ m i := by have := hm i; omega
  have hle : r ≤ r * m i := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left r hOne
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso ((hN (r * m i) (hNr.trans hle) i).1)
    ((BundleTensorPowerPullback.powerMulIso H r (m i)).symm ⊗ᵢ Iso.refl (M i))

/-- The same actual auxiliary-power producer for one prescribed original
invertible twist and one prescribed positive denominator. -/
theorem exists_auxiliary_power (M : X.Modules) (hM : IsInvertible M)
    (m : ℕ) (hm : 0 < m) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      SchemeLineAmpleness.IsVeryAmple p
        (bundleTensorPower (bundleTensorPower H r) m ⊗ M) := by
  obtain ⟨r, hr, hV, hTwist⟩ := exists_uniform_auxiliary_power p H hH
    (fun _ : Unit => M) (fun _ => hM) (fun _ => m) (fun _ => hm)
  exact ⟨r, hr, hV, hTwist ()⟩

/-- The original invertible twists themselves remain SECOND in the actual
native tensor object; in particular they may already be the component inverses. -/
theorem exists_uniform_auxiliary_power_tensorObj {ι : Type v} [Finite ι]
    (M : ι → X.Modules) (hM : ∀ i, IsInvertible (M i))
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      ∀ i, SchemeLineAmpleness.IsVeryAmple p
        (Scheme.Modules.tensorObj (bundleTensorPower (bundleTensorPower H r) (m i)) (M i)) := by
  obtain ⟨r, hr, hV, hTwist⟩ := exists_uniform_auxiliary_power p H hH M hM m hm
  exact ⟨r, hr, hV, fun i => SchemeAmpleClosedRestriction.veryAmple_of_iso (hTwist i)
    (ModularCurves.monoidalTensorObjIso _ _)⟩

/-- The actual original component inverses give the SAME original auxiliary
systems, with every line H_i literally the produced original H^r. -/
theorem exists_component_auxiliary_power {ι : Type v} [Finite ι]
    (D : ι → X.Modules) (hD : ∀ i, IsInvertible (D i))
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      ∀ i, SchemeLineAmpleness.IsVeryAmple p
        (bundleTensorPower (bundleTensorPower H r) (m i) ⊗ dualObj (D i)) :=
  exists_uniform_auxiliary_power p H hH (fun i => dualObj (D i)) (fun i => (hD i).dual) m hm

/-- The original component inverse remains SECOND in the actual native
sheafified tensor object required by the original auxiliary cover geometry. -/
theorem exists_component_auxiliary_power_tensorObj {ι : Type v} [Finite ι]
    (D : ι → X.Modules) (hD : ∀ i, IsInvertible (D i))
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      ∀ i, SchemeLineAmpleness.IsVeryAmple p
        (Scheme.Modules.tensorObj (bundleTensorPower (bundleTensorPower H r) (m i))
          (dualObj (D i))) :=
  exists_uniform_auxiliary_power_tensorObj p H hH (fun i => dualObj (D i))
    (fun i => (hD i).dual) m hm

end EnvelopeProperty.Vanishing.NadelAuxiliaryPositivity
