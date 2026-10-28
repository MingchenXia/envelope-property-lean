/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.SpectrumSmoothing
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology
open Filter
noncomputable section
namespace EnvelopeProperty

/-- A strict genuine smoothing radius is equivalent to an actual positive contracting power, without normalization. -/
theorem smoothingFun_lt_one_iff_exists_pow_lt_one {R : Type*} [CommRing R]
    (μ : RingSeminorm R) (a : R) :
    smoothingFun μ a < 1 ↔ ∃ N : ℕ, 0 < N ∧ μ (a ^ N) < 1 := by
  rw [smoothingFun, ciInf_lt_iff (smoothingSeminormSeq_bddBelow μ a)]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, N.pos, ?_⟩
    exact (Real.rpow_lt_one_iff' (apply_nonneg μ _) (by positivity)).mp hN
  · rintro ⟨N, hN, h⟩
    exact ⟨⟨N, hN⟩, (Real.rpow_lt_one_iff' (apply_nonneg μ _) (by positivity)).mpr h⟩

/-- Positive-power contraction detects actual topological nilpotence in the original seminormed ring. -/
theorem exists_norm_pow_lt_one_iff_tendsto_pow_zero {E : Type*} [SeminormedRing E] (a : E) :
    (∃ N : ℕ, 0 < N ∧ ‖a ^ N‖ < 1) ↔ Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  constructor
  · rintro ⟨N, hN, ha⟩
    let B : ℝ := 1 + ∑ j ∈ Finset.range N, ‖a ^ j‖
    have hB (r : ℕ) (hr : r < N) : ‖a ^ r‖ ≤ B := by
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (a ^ j))
        (Finset.mem_range.mpr hr)).trans (by dsimp [B]; linarith)
    have hdiv : Tendsto (fun n : ℕ => n / N) atTop atTop :=
      le_of_eq (map_div_atTop_eq_nat N hN)
    have hlim : Tendsto (fun n : ℕ => ‖a ^ N‖ ^ (n / N) * B) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_mul] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha).comp hdiv).mul_const B
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hdiv.eventually (eventually_ge_atTop 1)] with n hn
    calc
      ‖a ^ n‖ = ‖(a ^ N) ^ (n / N) * a ^ (n % N)‖ := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      _ ≤ ‖(a ^ N) ^ (n / N)‖ * ‖a ^ (n % N)‖ := norm_mul_le _ _
      _ ≤ ‖a ^ N‖ ^ (n / N) * B :=
        mul_le_mul (norm_pow_le' _ (by omega)) (hB _ (Nat.mod_lt _ hN))
          (norm_nonneg _) (by positivity)
  · intro ha
    have hnorm := (tendsto_zero_iff_norm_tendsto_zero.mp ha).eventually_lt_const zero_lt_one
    obtain ⟨N, hN, h⟩ := ((eventually_ge_atTop 1).and hnorm).exists
    exact ⟨N, hN, h⟩

namespace Berkovich
/-- Strict values on EVERY original bounded point exactly detect convergence of the original powers to zero. -/
theorem forall_normBoundedSpectrum_lt_one_iff_tendsto_pow_zero
    {E : Type*} [SeminormedCommRing E] [IsUltrametricDist E] [NormOneClass E] (a : E) :
    (∀ x : NormBoundedSpectrum E, x.1.val a < 1) ↔
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := exists_normBoundedSpectrum_attaining_smoothing a
    have hs : smoothingFun (SeminormedRing.toRingSeminorm E) a < 1 := by
      rw [← hx]
      exact_mod_cast ha x
    exact (exists_norm_pow_lt_one_iff_tendsto_pow_zero a).mp
      ((smoothingFun_lt_one_iff_exists_pow_lt_one _ _).mp hs)
  · intro ha x
    obtain ⟨N, hN, h⟩ := (exists_norm_pow_lt_one_iff_tendsto_pow_zero a).mpr ha
    have hp : (x.1.val a : ℝ) ^ N < 1 := by
      calc
        (x.1.val a : ℝ) ^ N = (x.1.val (a ^ N) : ℝ) := by simp
        _ ≤ ‖a ^ N‖ := x.2 _
        _ < 1 := h
    have hl : (x.1.val a : ℝ) < 1 := by
      by_contra hn
      exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt hn))) hp
    exact_mod_cast hl

end Berkovich
end EnvelopeProperty
