/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Supporting lines of `log (1 + s)`

Real analysis behind the strict exhaustion of FHX Lemma 5.18 (`lem:strict-exhaustion`). In the
source, `λ(τ) = log(1 + e^{-τ})` on `𝐓 = ℝ ∪ {+∞}` and, for `τ⁰ ∈ ℝ`, the supporting line is
`ℓ_{τ⁰}(τ) = λ(τ⁰) - p (τ - τ⁰)` with `p = e^{-τ⁰}/(1 + e^{-τ⁰})`. We work with `s = e^{-τ} ≥ 0`
(so `s = |f|` and `λ = log(1 + |f|)`), `s₀ = e^{-τ⁰} > 0` and `p = s₀/(1+s₀)`:
`ℓ = log(1 + s₀) + p (log s - log s₀)`.

* `supportLine_lt`: `ℓ(s) < log (1 + s)` for `0 < s ≠ s₀` (weighted AM–GM);
* `exists_supportLine_gap`: `ℓ(s) + δ ≤ log (1 + s)` whenever `|s - s₀| ≥ ε`, for some `δ > 0`;
* the case `τ⁰ = +∞` (`s₀ = 0`, `ℓ = 0`) is `Real.log (1 + ε) ≤ Real.log (1 + s)` for `s ≥ ε`.
-/

noncomputable section

namespace EnvelopeProperty

open Real

/-- The slope `p = s₀/(1+s₀) ∈ (0,1)` of the supporting line at `s₀`. -/
def supportSlope (s₀ : ℝ) : ℝ := s₀ / (1 + s₀)

/-- The supporting line `ℓ(s) = log(1 + s₀) + p (log s - log s₀)` of `log (1 + s)` at `s₀`,
written in the variable `log s`. -/
def supportLine (s₀ s : ℝ) : ℝ := Real.log (1 + s₀) + supportSlope s₀ * (Real.log s - Real.log s₀)

theorem supportSlope_pos {s₀ : ℝ} (h : 0 < s₀) : 0 < supportSlope s₀ := by
  unfold supportSlope; positivity

theorem supportSlope_lt_one {s₀ : ℝ} (h : 0 < s₀) : supportSlope s₀ < 1 := by
  unfold supportSlope
  rw [div_lt_one (by linarith)]
  linarith

@[simp]
theorem supportLine_self (s₀ : ℝ) : supportLine s₀ s₀ = Real.log (1 + s₀) := by
  simp [supportLine]

/-- Strict inequality off the contact point: weighted AM–GM for `1` and `t = s/s₀`. -/
theorem supportLine_lt {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : 0 < s) (hne : s ≠ s₀) :
    supportLine s₀ s < Real.log (1 + s) := by
  set p := supportSlope s₀ with hp
  have hp0 : 0 < p := supportSlope_pos hs₀
  have hp1 : p < 1 := supportSlope_lt_one hs₀
  set t := s / s₀ with ht
  have ht0 : 0 < t := div_pos hs hs₀
  have ht1 : (1 : ℝ) ≠ t := by
    intro h
    apply hne
    have : s = 1 * s₀ := by rw [h, ht, div_mul_cancel₀ _ hs₀.ne']
    simpa using this
  -- weighted AM–GM: `1^(1-p) * t^p < (1-p) * 1 + p * t`
  have key := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
    ![1 - p, p] ![1, t] (by intro i _; fin_cases i <;> simp [hp0, hp1])
    (by simp [Fin.sum_univ_two]) (by intro i _; fin_cases i <;> simp [ht0.le])).2
    ⟨0, by simp, 1, by simp, by simpa using ht1⟩
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.one_rpow, one_mul, mul_one] at key
  -- `(1-p) + p t = (1+s)/(1+s₀)`
  have hsum : (1 - p) + p * t = (1 + s) / (1 + s₀) := by
    rw [hp, ht, supportSlope]
    field_simp
    ring
  rw [hsum] at key
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos ht0 p) key
  rw [Real.log_rpow ht0, ht, Real.log_div hs.ne' hs₀.ne',
    Real.log_div (by positivity) (by positivity)] at hlog
  unfold supportLine
  rw [← hp]
  linarith

/-- The supporting line is below `log(1 + s)` everywhere on `(0, ∞)`. -/
theorem supportLine_le {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : 0 < s) :
    supportLine s₀ s ≤ Real.log (1 + s) := by
  rcases eq_or_ne s s₀ with rfl | hne
  · simp
  · exact (supportLine_lt hs₀ hs hne).le

/-- **Uniform gap** away from the contact point. -/
theorem exists_supportLine_gap {s₀ : ℝ} (hs₀ : 0 < s₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ, 0 < s → ε ≤ |s - s₀| → supportLine s₀ s + δ ≤ Real.log (1 + s) := by
  set p := supportSlope s₀ with hp
  have hp0 : 0 < p := supportSlope_pos hs₀
  have hp1 : p < 1 := supportSlope_lt_one hs₀
  set ψ : ℝ → ℝ := fun s => Real.log (1 + s) - supportLine s₀ s with hψ
  -- `ψ ≥ 1` for large `s`
  set L := (1 + Real.log (1 + s₀) - p * Real.log s₀) / (1 - p) with hL
  set B := Real.exp L with hB
  have hlarge : ∀ s, B ≤ s → 1 ≤ ψ s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (Real.exp_pos L) hs
    have hlogs : L ≤ Real.log s := by
      rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) hs
    have h1 : Real.log s ≤ Real.log (1 + s) := Real.log_le_log hs0 (by linarith)
    simp only [hψ, supportLine, ← hp]
    have : (1 - p) * L = 1 + Real.log (1 + s₀) - p * Real.log s₀ := by
      rw [hL]; field_simp [show (1 - p) ≠ 0 by linarith]
    nlinarith
  -- `ψ ≥ 1` for small `s`
  set L' := (p * Real.log s₀ - Real.log (1 + s₀) - 1) / p with hL'
  set a := Real.exp L' with ha
  have ha0 : 0 < a := Real.exp_pos L'
  have hsmall : ∀ s, 0 < s → s ≤ a → 1 ≤ ψ s := by
    intro s hs0 hs
    have hlogs : Real.log s ≤ L' := by
      rw [← Real.log_exp L']; exact Real.log_le_log hs0 hs
    have h1 : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
    simp only [hψ, supportLine, ← hp]
    have : p * L' = p * Real.log s₀ - Real.log (1 + s₀) - 1 := by
      rw [hL']; field_simp [hp0.ne']
    nlinarith
  -- compact middle range
  set M := Set.Icc a B ∩ {s | ε ≤ |s - s₀|} with hM
  have hMc : IsCompact M :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_abs.comp
      (continuous_id.sub continuous_const)))
  have hψcont : ContinuousOn ψ M := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1.1
    apply ContinuousAt.continuousWithinAt
    simp only [hψ, supportLine]
    have h1 : (1 + s) ≠ 0 := by linarith
    fun_prop (disch := assumption)
  have hψpos : ∀ s ∈ M, 0 < ψ s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1.1
    have hne : s ≠ s₀ := by
      intro h; have := hs.2; simp [h] at this; linarith
    simp only [hψ]
    linarith [supportLine_lt hs₀ hs0 hne]
  by_cases hMne : M.Nonempty
  · obtain ⟨m, hm, hmin⟩ := hMc.exists_isMinOn hMne hψcont
    refine ⟨min 1 (ψ m), lt_min one_pos (hψpos m hm), fun s hs0 hs => ?_⟩
    have : min 1 (ψ m) ≤ ψ s := by
      by_cases h1 : s ≤ a
      · exact (min_le_left _ _).trans (hsmall s hs0 h1)
      by_cases h2 : B ≤ s
      · exact (min_le_left _ _).trans (hlarge s h2)
      · exact (min_le_right _ _).trans (hmin ⟨⟨(not_le.1 h1).le, (not_le.1 h2).le⟩, hs⟩)
    simp only [hψ] at this
    linarith
  · refine ⟨1, one_pos, fun s hs0 hs => ?_⟩
    have : 1 ≤ ψ s := by
      by_cases h1 : s ≤ a
      · exact hsmall s hs0 h1
      by_cases h2 : B ≤ s
      · exact hlarge s h2
      · exact absurd ⟨s, ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩, hs⟩ hMne
    simp only [hψ] at this
    linarith

/-- The case `τ⁰ = +∞`: `log (1 + s) ≥ log (1 + ε) > 0` for `s ≥ ε > 0`. -/
theorem log_one_add_ge_of_le {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    Real.log (1 + ε) ≤ Real.log (1 + s) :=
  Real.log_le_log (by linarith) (by linarith)

theorem log_one_add_pos {ε : ℝ} (hε : 0 < ε) : 0 < Real.log (1 + ε) :=
  Real.log_pos (by linarith)

/-! ### Binomial bounds for `(1 + s)^m` -/

/-- Each binomial term is bounded by `(1 + s)^m`. -/
theorem choose_mul_pow_le_one_add_pow {s : ℝ} (hs : 0 ≤ s) {m α : ℕ} (hα : α ≤ m) :
    (m.choose α : ℝ) * s ^ α ≤ (1 + s) ^ m := by
  rw [add_comm, add_pow]
  have hmem : α ∈ Finset.range (m + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hα)
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => s ^ i * 1 ^ (m - i) * (m.choose i : ℝ))
    (fun i _ => by positivity) hmem)
  simp [mul_comm]

/-- `(1 + s)^m ≤ (m + 1) · max_α binom(m, α) s^α`. -/
theorem one_add_pow_le_succ_mul_sup {s : ℝ} (_hs : 0 ≤ s) (m : ℕ) :
    (1 + s) ^ m ≤ (m + 1 : ℝ) *
      (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        (fun α => (m.choose α : ℝ) * s ^ α) := by
  rw [add_comm, add_pow]
  calc ∑ i ∈ Finset.range (m + 1), s ^ i * 1 ^ (m - i) * (m.choose i : ℝ)
      ≤ ∑ _i ∈ Finset.range (m + 1), (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
          (fun α => (m.choose α : ℝ) * s ^ α) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have := Finset.le_sup' (fun α => (m.choose α : ℝ) * s ^ α) hi
        rw [one_pow, mul_one, mul_comm]
        exact this
    _ = (m + 1 : ℝ) * _ := by simp

end EnvelopeProperty
