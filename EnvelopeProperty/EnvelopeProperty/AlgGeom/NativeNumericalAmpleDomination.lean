import EnvelopeProperty.AlgGeom.NativeNumericalAmpleClasses
import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration

/-! # Genuine geometric ample domination on SAME original native numerical classes -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
open CanonicalGeometry NativeClosedCurveDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

private theorem tensorInvertible {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- The SAME actual sheafified tensor powers give genuine natural real multiples of their original class. -/
theorem lineClass_tensorPower (L : X.Modules) (hL : IsInvertible L) (m : ℕ) :
    lineClass p (bundleTensorPower L m) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) =
      (m : ℝ) • lineClass p L hL := by
  induction m with
  | zero => simpa only [bundleTensorPower, Scheme.Modules.unitObj, Nat.cast_zero, zero_smul] using lineClass_unit p
  | succ m ih =>
    calc
      lineClass p (bundleTensorPower L (m + 1)) _ =
          lineClass p (bundleTensorPower L m ⊗ L)
            (tensorInvertible (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) hL) :=
        lineClass_eq_of_iso p _ _ (ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).symm
      _ = lineClass p (bundleTensorPower L m) _ + lineClass p L hL :=
        lineClass_tensor p _ _ _ _
      _ = ((m + 1 : ℕ) : ℝ) • lineClass p L hL := by rw [ih, Nat.cast_succ, add_smul, one_smul]

variable [IsIntegral X] (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
  {ι : Type v} [Fintype ι] (B : ι → X.Modules) (hB : ∀ i, IsInvertible (B i))

/-- Actual original geometric ample twists DERIVE exact ample representatives of BOTH
signs of EVERY original finite-family numerical direction, with one internally derived bound. -/
theorem exists_eventual_ample_numerical_lifts :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i,
      ∃ hplus : SchemeLineAmpleness.IsAmple p (bundleTensorPower A m ⊗ B i),
        ∃ hminus : SchemeLineAmpleness.IsAmple p (bundleTensorPower A m ⊗ dualObj (B i)),
          lineClass p (bundleTensorPower A m ⊗ B i) hplus.isInvertible =
            (m : ℝ) • lineClass p A hA.isInvertible + lineClass p (B i) (hB i) ∧
          lineClass p (bundleTensorPower A m ⊗ dualObj (B i)) hminus.isInvertible =
            (m : ℝ) • lineClass p A hA.isInvertible - lineClass p (B i) (hB i) := by
  obtain ⟨N, hN⟩ := AmpleLineTwistGeneration.exists_uniform_eventual_isVeryAmple p A hA B hB
  refine ⟨N, fun m hm i => ?_⟩
  have hplus := AmpleLineTwistGeneration.isAmple_of_isVeryAmple (hN m hm i).1
  have hminus := AmpleLineTwistGeneration.isAmple_of_isVeryAmple (hN m hm i).2
  refine ⟨hplus, hminus, ?_, ?_⟩
  · rw [lineClass_tensor p _ _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible m)
      (hB i), lineClass_tensorPower]
  · rw [lineClass_tensor p _ _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible m)
      (hB i).dual, lineClass_tensorPower, lineClass_dual, sub_eq_add_neg]

/-- Actual geometric ampleness DERIVES genuine uniform positive/negative numerical nef domination. -/
theorem exists_eventual_nef_domination :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i,
      (m : ℝ) • lineClass p A hA.isInvertible + lineClass p (B i) (hB i) ∈ nefCone p ∧
        (m : ℝ) • lineClass p A hA.isInvertible - lineClass p (B i) (hB i) ∈ nefCone p := by
  obtain ⟨N, hN⟩ := exists_eventual_ample_numerical_lifts p A hA B hB
  refine ⟨N, fun m hm i => ?_⟩
  obtain ⟨hp, hn, hep, hen⟩ := hN m hm i
  exact ⟨hep ▸ ampleLineClass_mem_nefCone p _ hp, hen ▸ ampleLineClass_mem_nefCone p _ hn⟩

/-- The SAME uniform original numerical domination is STRICT on EVERY original true closed curve. -/
theorem exists_eventual_strict_degree_domination :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i, ∀ C : ClosedIntegralCurve X,
      0 < curveDegree p C ((m : ℝ) • lineClass p A hA.isInvertible + lineClass p (B i) (hB i)) ∧
        0 < curveDegree p C ((m : ℝ) • lineClass p A hA.isInvertible - lineClass p (B i) (hB i)) := by
  obtain ⟨N, hN⟩ := exists_eventual_ample_numerical_lifts p A hA B hB
  refine ⟨N, fun m hm i C => ?_⟩
  obtain ⟨hp, hn, hep, hen⟩ := hN m hm i
  exact ⟨hep ▸ curveDegree_ampleLineClass_pos p _ hp C, hen ▸ curveDegree_ampleLineClass_pos p _ hn C⟩

end EnvelopeProperty.NativeRealNumericalClasses
