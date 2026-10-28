import TranscendentalNakamaye.Pending.MonicRelationWeightedNormBound
import TranscendentalNakamaye.Pending.IEquivalentMax
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

/-! # Actual finite weighted integrability from a genuine monic relation -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace TranscendentalNakamaye.Pending.MonicRelationWeightedIntegrability

open FirstPass IEquivalentMax

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Actual finite weighted masses and a monic relation internally dominate and
integrate the original root, including zero generators and infinite pole weights. -/
theorem weightedL2On_of_monic_relation {φ : E → EReal} {c : ℝ} (hc : 0 < c)
    {O : Set E} (hO : IsOpen O) (hφ : QuasiPlurisubharmonicOn φ O)
    {F : E → ℂ} (hF : DifferentiableOn ℂ F O) {N d : ℕ} (hd : 0 < d)
    (G : Fin N → E → ℂ) (b : Fin d → E → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ i, WeightedL2On φ c (G i) O μ)
    (hcoeff : ∀ z ∈ O, ∀ i, ‖b i z‖ ≤ C * (∑ j, ‖G j z‖) ^ (d - i.val))
    (hrel : ∀ z ∈ O, F z ^ d + ∑ i, b i z * F z ^ i.val = 0) :
    WeightedL2On φ c F O μ := by
  let B : ℝ := (d : ℝ) * C + 1
  let K : ℝ≥0∞ := ENNReal.ofReal (B ^ 2 * (N : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ z ∈ O, multiplierDensity φ c F z ≤
      ∑ j, K * multiplierDensity φ c (G j) z := by
    intro z hz
    have hroot : ‖F z‖ ≤ B * ∑ j, ‖G j z‖ :=
      MonicRelationWeightedNormBound.norm_le_of_monic_relation hd (F z) (fun i => b i z)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC (hcoeff z hz) (hrel z hz)
    have hsum : (∑ j, ‖G j z‖) ^ 2 ≤ (N : ℝ) * ∑ j, ‖G j z‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin N => (1 : ℝ)) (fun j => ‖G j z‖)
    have hnorm : ‖F z‖ ^ 2 ≤ (B ^ 2 * (N : ℝ)) * ∑ j, ‖G j z‖ ^ 2 := by
      calc
        ‖F z‖ ^ 2 ≤ (B * ∑ j, ‖G j z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hroot 2
        _ = B ^ 2 * (∑ j, ‖G j z‖) ^ 2 := mul_pow _ _ _
        _ ≤ B ^ 2 * ((N : ℝ) * ∑ j, ‖G j z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
        _ = _ := by ring
    have hreal : ENNReal.ofReal (‖F z‖ ^ 2) ≤ K * ∑ j, ENNReal.ofReal (‖G j z‖ ^ 2) := by
      have h := ENNReal.ofReal_le_ofReal hnorm
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg ‖G j z‖)] at h
      exact h
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖F z‖ ^ 2) * multiplierWeight c (φ z) ≤
          (K * ∑ j, ENNReal.ofReal (‖G j z‖ ^ 2)) * multiplierWeight c (φ z) :=
        mul_le_mul' hreal le_rfl
      _ = ∑ j, K * (ENNReal.ofReal (‖G j z‖ ^ 2) * multiplierWeight c (φ z)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  refine ⟨aemeasurable_multiplierDensity_restrict hO hφ hc.ne' hF.continuousOn, ?_⟩
  have hmeas := fun j => (hG j).1.const_mul K
  calc
    (∫⁻ z in O, multiplierDensity φ c F z ∂μ) ≤
        ∫⁻ z in O, ∑ j, K * multiplierDensity φ c (G j) z ∂μ :=
      setLIntegral_mono_ae' hO.measurableSet (Eventually.of_forall hpoint)
    _ = ∑ j, K * ∫⁻ z in O, multiplierDensity φ c (G j) z ∂μ := by
      rw [lintegral_finsetSum' _ fun j _ => hmeas j]
      simp_rw [lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun j _ => ENNReal.mul_lt_top hK.lt_top (hG j).2

end
end TranscendentalNakamaye.Pending.MonicRelationWeightedIntegrability
