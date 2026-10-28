/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.PowerSeminormValuation
import EnvelopeProperty.Berkovich.SpectrumNormedCompletion
import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
import Mathlib.Analysis.Normed.Group.Ultra

/-! # The genuine smoothing maximum of all original dominated valuations -/
open scoped NNReal
noncomputable section
namespace EnvelopeProperty.Berkovich
variable {A : Type*} [CommRing A]

/-- All ORIGINAL positive-power bounds force every dominated valuation below genuine smoothing. -/
theorem valuation_le_smoothingFun (μ : RingSeminorm A) (v : Valuation A ℝ≥0)
    (hv : ∀ a, (v a : ℝ) ≤ μ a) (b : A) : (v b : ℝ) ≤ smoothingFun μ b := by
  apply le_ciInf
  intro n
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  have hp : (v b : ℝ) ^ (n : ℕ) ≤ μ (b ^ (n : ℕ)) := by
    simpa only [map_pow, NNReal.coe_pow] using hv (b ^ (n : ℕ))
  calc
    (v b : ℝ) = ((v b : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (v b).coe_nonneg hn).symm
    _ ≤ μ (b ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hp (by positivity)
    _ = _ := by rw [one_div]

/-- Actual smoothing and genuine original-ring attainment construct a whole dominated valuation at its spectral radius. -/
theorem exists_valuation_le_attaining_smoothing (μ : RingSeminorm A) (hμ1 : μ 1 = 1)
    (hμna : IsNonarchimedean μ) (b : A) :
    ∃ v : Valuation A ℝ≥0, (∀ a, (v a : ℝ) ≤ μ a) ∧ (v b : ℝ) = smoothingFun μ b := by
  let ν := smoothingSeminorm μ hμ1.le hμna
  have hν1 : ν 1 = 1 := by
    change smoothingFun μ 1 = 1
    rw [smoothingFun_of_powMul μ hμ1.le (fun n _ => by simp [hμ1])]
    exact hμ1
  obtain ⟨v, hv, hb⟩ := exists_valuation_le_attaining ν hν1
    (isNonarchimedean_smoothingFun μ hμ1.le hμna) (isPowMul_smoothingFun μ hμ1.le) b
  exact ⟨v, fun a => (hv a).trans (smoothingFun_le_self μ a), hb⟩

/-- The actual smoothing value is a genuine MAXIMUM of all whole original dominated valuation values. -/
theorem isGreatest_smoothingValuationValues (μ : RingSeminorm A) (hμ1 : μ 1 = 1)
    (hμna : IsNonarchimedean μ) (b : A) :
    IsGreatest {t : ℝ | ∃ v : Valuation A ℝ≥0, (∀ a, (v a : ℝ) ≤ μ a) ∧ t = (v b : ℝ)}
      (smoothingFun μ b) := by
  obtain ⟨v, hv, hb⟩ := exists_valuation_le_attaining_smoothing μ hμ1 hμna b
  refine ⟨⟨v, hv, hb.symm⟩, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact valuation_le_smoothingFun μ w hw b

section Normed
variable {E : Type*} [SeminormedCommRing E] [IsUltrametricDist E] [NormOneClass E]

/-- Every actual smoothing norm value is attained by a whole ORIGINAL bounded point, without source completeness. -/
theorem exists_normBoundedSpectrum_attaining_smoothing (b : E) :
    ∃ x : NormBoundedSpectrum E, (x.1.val b : ℝ) =
      smoothingFun (SeminormedRing.toRingSeminorm E) b := by
  obtain ⟨v, hv, hb⟩ := exists_valuation_le_attaining_smoothing (SeminormedRing.toRingSeminorm E)
    (show (SeminormedRing.toRingSeminorm E) 1 = 1 from norm_one)
    (show IsNonarchimedean (SeminormedRing.toRingSeminorm E) from
      IsUltrametricDist.isNonarchimedean_norm) b
  refine ⟨⟨Spectrum.ofValuation v, fun a => ?_⟩, hb⟩
  exact_mod_cast hv a

/-- The original bounded spectrum has an actual smoothing-norm MAXIMUM, with no power law imposed on the norm. -/
theorem isGreatest_normBoundedSpectrumValues (b : E) :
    IsGreatest {t : ℝ | ∃ x : NormBoundedSpectrum E, t = (x.1.val b : ℝ)}
      (smoothingFun (SeminormedRing.toRingSeminorm E) b) := by
  obtain ⟨x, hx⟩ := exists_normBoundedSpectrum_attaining_smoothing b
  refine ⟨⟨x, hx.symm⟩, ?_⟩
  rintro t ⟨y, rfl⟩
  apply valuation_le_smoothingFun (SeminormedRing.toRingSeminorm E) y.1.val
  intro a
  exact y.2 a

end Normed
end EnvelopeProperty.Berkovich
