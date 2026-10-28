import EnvelopeProperty.AlgGeom.AmpleTensorLines

/-! # Geometric original ampleness and true positive original tensor powers -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.AmpleLinePositivePowers
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- EVERY positive actual original power of a SAME original ample line
is geometrically ample, from its internally derived high embedding powers. -/
theorem isAmple_tensorPower {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (s : ℕ) (hs : 0 < s) : SchemeLineAmpleness.IsAmple p (bundleTensorPower A s) := by
  refine ⟨TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible s, ?_⟩
  obtain ⟨N, hN⟩ := AmpleTensorLines.exists_eventual_isVeryAmple p A hA
  have hst : N ≤ s * (N + 1) := by nlinarith
  exact ⟨N + 1, by omega, SchemeAmpleClosedRestriction.veryAmple_of_iso (hN _ hst)
    (BundleTensorPowerPullback.powerMulIso A s (N + 1)).symm⟩

/-- Geometric ampleness of a positive actual power gives the SAME original
invertible line's geometric ample criterion, with the real exponent product. -/
theorem isAmple_of_tensorPower {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : IsInvertible A) (s : ℕ) (hs : 0 < s)
    (hP : SchemeLineAmpleness.IsAmple p (bundleTensorPower A s)) : SchemeLineAmpleness.IsAmple p A := by
  refine ⟨hA, ?_⟩
  obtain ⟨r, hr, hV⟩ := hP.2
  exact ⟨s * r, Nat.mul_pos hs hr, SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    (BundleTensorPowerPullback.powerMulIso A s r)⟩

/-- The SAME original geometric ample criterion is invariant under ANY
positive true actual tensor exponent, with no numerical or embedding premise. -/
theorem isAmple_tensorPower_iff {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : IsInvertible A) (s : ℕ) (hs : 0 < s) :
    SchemeLineAmpleness.IsAmple p (bundleTensorPower A s) ↔ SchemeLineAmpleness.IsAmple p A :=
  ⟨isAmple_of_tensorPower p A hA s hs, fun h => isAmple_tensorPower p A h s hs⟩
end EnvelopeProperty.AmpleLinePositivePowers
