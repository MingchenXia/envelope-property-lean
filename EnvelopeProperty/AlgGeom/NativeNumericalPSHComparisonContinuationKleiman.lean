import EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationRayComparison
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmple
import EnvelopeProperty.AlgGeom.NativeNumericalRationalAmpleLines

/-! # Kleiman's criterion from "nef plus ample is ample"

On an integral projective scheme, an invertible sheaf `T` whose numerical class lies in the ample
cone is ample (`numericalAmplenessCriterion`).  Write `[T] = ∑ cᵢ [Aᵢ]` with `Aᵢ` ample and
`cᵢ > 0`, choose rationals `0 < qᵢ < cᵢ` and an ample `B` with `[B] = d ∑ qᵢ [Aᵢ]` (`d > 0`).  Then
`N = T^{⊗d} ⊗ B^∨` has the nef class `d ∑ (cᵢ - qᵢ) [Aᵢ]`, so `N ⊗ B ≅ T^{⊗d}` is ample by
`SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef`, and so is `T`.

Consequently the comparison theorem `isCurveWeakPSH_iff_isPSH_ray'` needs only the finite
dimensionality of `N¹(X)`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open scoped Classical NNReal ENNReal

noncomputable section

universe u

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry NativeRealNumericalClasses

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- Kleiman's criterion on an integral projective scheme: an invertible sheaf whose numerical
class lies in the ample cone is ample. -/
theorem numericalAmplenessCriterion [IsIntegral X] : NumericalAmplenessCriterion p := by
  intro T hT h
  obtain ⟨n, hn, A, hA, c, hc, he⟩ := exists_positive_ample_line_sum p _ h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose q hq₁ hq₂ using fun i => exists_rat_btwn (half_lt_self (hc i))
  have hqpos (i : Fin n) : 0 < q i := by exact_mod_cast (half_pos (hc i)).trans (hq₁ i)
  obtain ⟨d, hd, B, hB, hBe⟩ := exists_rational_ample_line_representative p hn A hA q hqpos
  have hTd := TensorPowerBaseIdealGrading.tensorPower_isInvertible hT d
  have hNinv : IsInvertible (bundleTensorPower T d ⊗ dualObj B) :=
    hTd.monoidalTensor hB.isInvertible.dual
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB' : lineClass p B hB.isInvertible =
      (d : ℝ) • lineFamilyMap p A (fun i => (hA i).isInvertible) (fun i => (q i : ℝ)) := by
    rw [hBe, smul_smul, mul_inv_cancel₀ hd', one_smul]
  have hNclass : lineClass p (bundleTensorPower T d ⊗ dualObj B) hNinv =
      ∑ i, ((d : ℝ) * (c i - q i)) • lineClass p (A i) (hA i).isInvertible := by
    rw [lineClass_tensor p _ _ hTd hB.isInvertible.dual, lineClass_dual p B hB.isInvertible,
      lineClass_tensorPower p T hT d, hB', he, lineFamilyMap_apply, lineFamilyMap_apply,
      Finset.smul_sum, Finset.smul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← sub_smul, mul_sub]
  have hnef : lineClass p (bundleTensorPower T d ⊗ dualObj B) hNinv ∈ nefCone p := by
    rw [hNclass]
    exact positive_ample_sum_mem_nefCone p A hA _
      (fun i => mul_pos (by exact_mod_cast hd) (sub_pos.mpr (hq₂ i)))
  have hNB := SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef p _ B hNinv hnef hB
  have hpow : SchemeLineAmpleness.IsAmple p (bundleTensorPower T d) :=
    AmpleTensorLines.ample_of_iso hNB
      (α_ _ _ _ ≪≫ whiskerLeftIso _ ((β_ (dualObj B) B) ≪≫ hB.isInvertible.monoidalEvaluationIso) ≪≫
        ρ_ _)
  exact AmpleLinePositivePowers.isAmple_of_tensorPower p T hT d hd hpow

/-- **Comparison on an ample ray**, assuming only that `N¹(X)` is finite dimensional. -/
theorem isCurveWeakPSH_iff_isPSH_ray' [IsIntegral X]
    [FiniteDimensional ℝ (NativeRealNumericalClasses.Space p)]
    (L : X.Modules) (hLA : SchemeLineAmpleness.IsAmple p L) {a : ℝ} (ha : 0 ≤ a)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsCurveWeakPSH p (a • NativeRealNumericalClasses.lineClass p L hLA.isInvertible) φ ↔
      NativeLineFubiniStudy.IsPSH p L hLA.isInvertible a φ :=
  isCurveWeakPSH_iff_isPSH_ray p (numericalAmplenessCriterion p) L hLA ha φ

end EnvelopeProperty.NativeNumericalFubiniStudy
