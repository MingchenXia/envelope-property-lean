/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.UnbundledSmoothingBounds
import EnvelopeProperty.Berkovich.SpectrumSmoothing
import EnvelopeProperty.Berkovich.SpectralTopologicalNilpotence

open scoped NNReal Topology
open Filter
noncomputable section
namespace EnvelopeProperty.Berkovich

/-- EVERY original nonzero ultrametric ring seminorm has a genuine valuation attaining its ORIGINAL smoothing, without unit normalization. -/
theorem exists_valuation_le_attaining_smoothing_nonzero {A : Type*} [CommRing A]
    (μ : RingSeminorm A) (hμ : μ ≠ 0) (hna : IsNonarchimedean μ) (b : A) :
    ∃ v : Valuation A ℝ≥0, (∀ a, (v a : ℝ) ≤ μ a) ∧
      (v b : ℝ) = smoothingFun μ b := by
  obtain ⟨ν, hν1, hνna, hνle, _, heq⟩ :=
    exists_normalized_seminorm_same_smoothing μ hμ hna
  obtain ⟨v, hv, hb⟩ := exists_valuation_le_attaining_smoothing ν hν1 hνna b
  exact ⟨v, fun a => (hv a).trans (hνle a), hb.trans (heq b)⟩

/-- The whole ORIGINAL bounded spectrum attains the ORIGINAL smoothing maximum whenever the original unit seminorm is positive. -/
theorem isGreatest_normBoundedSpectrumValues_of_norm_one_pos
    {E : Type*} [SeminormedCommRing E] [IsUltrametricDist E]
    (h1 : 0 < ‖(1 : E)‖) (b : E) :
    IsGreatest {t : ℝ | ∃ x : NormBoundedSpectrum E, t = (x.1.val b : ℝ)}
      (smoothingFun (SeminormedRing.toRingSeminorm E) b) := by
  let μ := SeminormedRing.toRingSeminorm E
  have hμ : μ ≠ 0 := by
    intro h
    have hz := congrArg (fun f : RingSeminorm E => f 1) h
    exact h1.ne' hz
  obtain ⟨v, hv, hb⟩ := exists_valuation_le_attaining_smoothing_nonzero μ hμ
    IsUltrametricDist.isNonarchimedean_norm b
  let x : NormBoundedSpectrum E :=
    ⟨Spectrum.ofValuation v, fun a => by exact_mod_cast hv a⟩
  refine ⟨⟨x, hb.symm⟩, ?_⟩
  rintro t ⟨y, rfl⟩
  exact valuation_le_smoothingFun μ y.1.val (fun a => y.2 a) b

/-- Strict values on EVERY original bounded point detect actual ORIGINAL power convergence, including zero seminorms and without NormOne. -/
theorem forall_bounded_value_lt_one_iff_tendsto_pow_zero
    {E : Type*} [SeminormedCommRing E] [IsUltrametricDist E] (a : E) :
    (∀ x : NormBoundedSpectrum E, x.1.val a < 1) ↔
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  constructor
  · intro ha
    by_cases h1 : ‖(1 : E)‖ = 0
    · have hz (b : E) : ‖b‖ = 0 := by
        apply le_antisymm _ (norm_nonneg _)
        simpa only [mul_one, h1, mul_zero] using norm_mul_le b 1
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hp : 0 < ‖(1 : E)‖ := lt_of_le_of_ne' (norm_nonneg _) h1
      obtain ⟨x, hx⟩ := (isGreatest_normBoundedSpectrumValues_of_norm_one_pos hp a).1
      have hs : smoothingFun (SeminormedRing.toRingSeminorm E) a < 1 := by
        rw [hx]
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

end EnvelopeProperty.Berkovich
