import EnvelopeProperty.AlgGeom.VeryAmpleTensorGenerated
import EnvelopeProperty.AlgGeom.GeneratedLineTensorPowers
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
import EnvelopeProperty.AlgGeom.SchemeAmpleLineGlobalGeneration

/-! # Genuine geometric original ample tensor closure and eventual very ampleness -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.AmpleTensorLines
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensorInvertible {X : Scheme.{u}} {A B : X.Modules}
    (hA : IsInvertible A) (hB : IsInvertible B) : IsInvertible (A ⊗ B) :=
  (hA.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso A B)

/-- A WHOLE original line isomorphism transports the actual geometric ample criterion. -/
theorem ample_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {A B : X.Modules}
    (hA : SchemeLineAmpleness.IsAmple p A) (e : A ≅ B) : SchemeLineAmpleness.IsAmple p B := by
  refine ⟨hA.isInvertible.of_iso e.symm, ?_⟩
  obtain ⟨r, hr, hV⟩ := hA.2
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso hV (BundleTensorPowerPullback.powerIso e r)⟩

/-- The SAME actual tensor of an original ample line and a genuine original
finite globally generated invertible line is geometrically ample. -/
theorem isAmple_tensor_of_generatingSections {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of R)) (A B : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (hB : IsInvertible B)
    (G : B.GeneratingSections) (hG : G.IsFiniteType) : SchemeLineAmpleness.IsAmple p (A ⊗ B) := by
  refine ⟨tensorInvertible hA.isInvertible hB, ?_⟩
  obtain ⟨r, hr, hVA⟩ := hA.2
  obtain ⟨H, hH⟩ := GeneratedLineTensorPowers.exists_generatingSections_tensorPower p B hB G hG r
  have hV := VeryAmpleTensorGenerated.isVeryAmple_tensor p (bundleTensorPower A r) (bundleTensorPower B r)
    hVA (TensorPowerBaseIdealGrading.tensorPower_isInvertible hB r) H hH
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    (BundleTensorPowerTensor.powerTensorIso A B r).symm⟩

/-- EVERY sufficiently large SAME original ample power is a true original
closed-embedding line, from its genuine geometry and internally derived generators. -/
theorem exists_eventual_isVeryAmple {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m) := by
  obtain ⟨r, _hr, hVA⟩ := hA.2
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p A hA
  refine ⟨N + r, fun m hm => ?_⟩
  have hd : N ≤ m - r := by omega
  have he : r + (m - r) = m := by omega
  obtain ⟨G, hG⟩ := hN (m - r) hd
  have hV := VeryAmpleTensorGenerated.isVeryAmple_tensor p (bundleTensorPower A r)
    (bundleTensorPower A (m - r)) hVA
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible (m - r)) G hG
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    (TensorPowerBaseIdealGrading.tensorPowerAddIso A r (m - r) ≪≫
      eqToIso (congrArg (bundleTensorPower A) he))

/-- The SAME original tensor of TWO genuine original geometrically ample
lines is geometrically ample, with a shared positive embedding power internally produced. -/
theorem isAmple_tensor {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (A B : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (hB : SchemeLineAmpleness.IsAmple p B) :
    SchemeLineAmpleness.IsAmple p (A ⊗ B) := by
  refine ⟨tensorInvertible hA.isInvertible hB.isInvertible, ?_⟩
  obtain ⟨N, hN⟩ := exists_eventual_isVeryAmple p A hA
  obtain ⟨M, hM⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p B hB
  let r := max N M + 1
  have hr : 0 < r := by omega
  have hNr : N ≤ r := by dsimp [r]; omega
  have hMr : M ≤ r := by dsimp [r]; omega
  obtain ⟨G, hG⟩ := hM r hMr
  have hV := VeryAmpleTensorGenerated.isVeryAmple_tensor p (bundleTensorPower A r)
    (bundleTensorPower B r) (hN r hNr)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hB.isInvertible r) G hG
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    (BundleTensorPowerTensor.powerTensorIso A B r).symm⟩
end EnvelopeProperty.AmpleTensorLines
