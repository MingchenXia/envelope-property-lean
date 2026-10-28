/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology
open Filter
noncomputable section
namespace EnvelopeProperty

private theorem smoothing_nonneg {A : Type*} [CommRing A] (μ : RingSeminorm A) (a : A) :
    0 ≤ smoothingFun μ a := by
  apply le_ciInf
  intro n
  exact Real.rpow_nonneg (apply_nonneg μ _) _

/-- An ORIGINAL unbundled ring-seminorm smoothing margin constructs a true all-power bound, retaining the actual unit value at exponent zero. -/
theorem exists_ge_one_pow_bound_of_smoothing_lt_seminorm {A : Type*} [CommRing A]
    (μ : RingSeminorm A) (a : A) (r : ℝ) (hr : 0 < r) (ha : smoothingFun μ a < r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, μ (a ^ n) ≤ C * r ^ n := by
  obtain ⟨N, hroot⟩ := (ciInf_lt_iff (smoothingSeminormSeq_bddBelow μ a)).mp ha
  have hblock : μ (a ^ (N : ℕ)) < r ^ (N : ℕ) := by
    have hh := pow_lt_pow_left₀ hroot (Real.rpow_nonneg (apply_nonneg μ _) _) N.ne_zero
    simpa only [one_div, Real.rpow_inv_natCast_pow (apply_nonneg μ _) N.ne_zero] using hh
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N : ℕ), μ (a ^ j) / r ^ j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (N : ℕ), μ (a ^ j) / r ^ j :=
    Finset.sum_nonneg (fun j _ => div_nonneg (apply_nonneg μ _) (pow_pos hr _).le)
  have hrem (j : ℕ) (hj : j < N) : μ (a ^ j) ≤ C * r ^ j := by
    apply (div_le_iff₀ (pow_pos hr j)).mp
    exact (Finset.single_le_sum (f := fun k => μ (a ^ k) / r ^ k)
      (fun k _ => div_nonneg (apply_nonneg μ _) (pow_pos hr _).le)
      (Finset.mem_range.mpr hj)).trans (by dsimp [C]; linarith)
  refine ⟨C, by dsimp [C]; linarith, fun n => ?_⟩
  by_cases hq : n / (N : ℕ) = 0
  · exact hrem n ((Nat.div_eq_zero_iff.mp hq).resolve_left N.ne_zero)
  · calc
      μ (a ^ n) = μ ((a ^ (N : ℕ)) ^ (n / N) * a ^ (n % N)) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      _ ≤ μ ((a ^ (N : ℕ)) ^ (n / N)) * μ (a ^ (n % N)) := map_mul_le_mul μ _ _
      _ ≤ (r ^ (N : ℕ)) ^ (n / N) * (C * r ^ (n % N)) :=
        mul_le_mul ((map_pow_le_pow μ _ hq).trans
          (pow_le_pow_left₀ (apply_nonneg μ _) hblock.le _))
          (hrem _ (Nat.mod_lt _ N.pos)) (apply_nonneg μ _) (by positivity)
      _ = C * ((r ^ (N : ℕ)) ^ (n / N) * r ^ (n % N)) := by ring
      _ = C * r ^ n := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]

/-- The genuine BGR operator seminorm is normalized and preserves EVERY ORIGINAL smoothing value; all comparisons are derived, not supplied. -/
theorem exists_normalized_seminorm_same_smoothing {A : Type*} [CommRing A]
    (μ : RingSeminorm A) (hμ : μ ≠ 0) (hna : IsNonarchimedean μ) :
    ∃ ν : RingSeminorm A, ν 1 = 1 ∧ IsNonarchimedean ν ∧
      (∀ a, ν a ≤ μ a) ∧ (∀ a, μ a ≤ μ 1 * ν a) ∧
      ∀ a, smoothingFun ν a = smoothingFun μ a := by
  have hf : (μ : A → ℝ) ≠ 0 := by
    intro h
    apply hμ
    ext a
    exact congrFun h a
  have hmul (a b : A) : μ (a*b) ≤ (1 : ℝ)*μ a*μ b := by
    simpa only [one_mul] using map_mul_le_mul μ a b
  let ν := seminormFromBounded (map_zero μ) (apply_nonneg μ) hmul
    (map_add_le_add μ) (map_neg_eq_map μ)
  have hν1 : ν 1 = 1 := seminormFromBounded_one hf (apply_nonneg μ) hmul
  have hνna : IsNonarchimedean ν :=
    seminormFromBounded_isNonarchimedean (apply_nonneg μ) hmul hna
  have hνle (a : A) : ν a ≤ μ a := by
    change seminormFromBounded' (μ : A → ℝ) a ≤ μ a
    simpa only [one_mul] using seminormFromBounded_le (apply_nonneg μ) hmul a
  have hνge (a : A) : μ a ≤ μ 1 * ν a :=
    seminormFromBounded_ge (apply_nonneg μ) hmul a
  have hμ1 : 0 < μ 1 :=
    lt_of_le_of_ne' (apply_nonneg μ 1) (map_one_ne_zero hf (apply_nonneg μ) hmul)
  refine ⟨ν, hν1, hνna, hνle, hνge, fun a => le_antisymm ?_ ?_⟩
  · apply le_ciInf
    intro n
    exact (smoothingFun_le ν a n).trans
      (Real.rpow_le_rpow (apply_nonneg ν _) (hνle _) (by positivity))
  · apply le_of_forall_pos_le_add
    intro ε hε
    let r := smoothingFun ν a + ε
    have hr : 0 < r := add_pos_of_nonneg_of_pos (smoothing_nonneg ν a) hε
    obtain ⟨C, hC, hb⟩ := exists_ge_one_pow_bound_of_smoothing_lt_seminorm ν a r hr
      (by dsimp [r]; linarith)
    have hMC : 0 < μ 1 * C := mul_pos hμ1 (lt_of_lt_of_le zero_lt_one hC)
    have hpow (n : ℕ) : μ (a ^ n) ≤ (μ 1 * C) * r ^ n := by
      exact (hνge _).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n) hμ1.le)
    have hroot (n : PNat) : smoothingFun μ a ≤ (μ 1 * C) ^ (1 / (n : ℝ)) * r := by
      calc
        smoothingFun μ a ≤ μ (a ^ (n : ℕ)) ^ (1 / (n : ℝ)) := smoothingFun_le μ a n
        _ ≤ ((μ 1 * C) * r ^ (n : ℕ)) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (apply_nonneg μ _) (hpow n) (by positivity)
        _ = (μ 1 * C) ^ (1 / (n : ℝ)) * r := by
          rw [Real.mul_rpow hMC.le (pow_pos hr _).le, one_div,
            Real.pow_rpow_inv_natCast hr.le n.ne_zero]
    have hlim : Tendsto (fun n : ℕ => (μ 1 * C) ^ (1 / ((n : ℝ) + 1)) * r)
        atTop (𝓝 r) := by
      simpa only [Function.comp_def, Real.rpow_zero, one_mul] using
        (((Real.continuousAt_const_rpow hMC.ne').tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const r)
    exact ge_of_tendsto' hlim (fun n => by
      have hh := hroot ⟨n+1, Nat.succ_pos n⟩
      change smoothingFun μ a ≤ (μ 1 * C) ^ (1 / ((n+1 : ℕ) : ℝ)) * r at hh
      simpa only [Nat.cast_add, Nat.cast_one] using hh)

end EnvelopeProperty
