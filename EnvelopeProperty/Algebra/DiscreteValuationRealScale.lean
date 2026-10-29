import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Genuine whole real-valued scales of an original discrete valuation -/
open scoped NNReal WithZero
noncomputable section
namespace EnvelopeProperty.DiscreteValuationRealScale

/-- The actual positive real scaling base, including the original zero parameter. -/
def expBase (s : ℝ≥0) : ℝ≥0 := ⟨Real.exp (s : ℝ), (Real.exp_pos _).le⟩

/-- The actual exponential base is always nonzero, with no positivity certificate supplied. -/
theorem expBase_ne_zero (s : ℝ≥0) : expBase s ≠ 0 := by
  exact ne_of_gt (show (0 : ℝ≥0) < expBase s from Real.exp_pos _)

/-- The actual whole integer-value-group scaling map. -/
def scale (s : ℝ≥0) : ℤᵐ⁰ →*₀ ℝ≥0 := WithZeroMulInt.toNNReal (expBase_ne_zero s)

/-- Every original nonnegative parameter gives a genuine monotone whole scaling map. -/
theorem scale_monotone (s : ℝ≥0) : Monotone (scale s) := by
  by_cases hs : s = 0
  · subst s
    intro x y hxy
    by_cases hx : x = 0
    · rw [hx, map_zero]
      exact zero_le
    have hy : y ≠ 0 := by
      intro hy
      exact hx (le_zero_iff.mp (hy ▸ hxy))
    have hb : expBase 0 = 1 := by
      apply NNReal.eq
      exact Real.exp_zero
    change WithZeroMulInt.toNNReal (expBase_ne_zero 0) x ≤
      WithZeroMulInt.toNNReal (expBase_ne_zero 0) y
    rw [WithZeroMulInt.toNNReal_neg_apply _ hx, WithZeroMulInt.toNNReal_neg_apply _ hy, hb]
    simp only [one_zpow, le_refl]
  · have he : 1 < expBase s := by
      change (1 : ℝ) < Real.exp (s : ℝ)
      exact Real.one_lt_exp_iff.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs))
    exact (WithZeroMulInt.toNNReal_strictMono he).monotone

/-- Every original integer value has its exact original logarithmic scale. -/
theorem log_scale_exp (s : ℝ≥0) (n : ℤ) :
    Real.log ((scale s (WithZero.exp n) : ℝ≥0) : ℝ) = (s : ℝ) * (n : ℝ) := by
  have hp := NNReal.coe_zpow (expBase s) n
  change Real.log ((WithZeroMulInt.toNNReal (expBase_ne_zero s) (WithZero.exp n) : ℝ≥0) : ℝ) = _
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have hn : (WithZero.unzero (show WithZero.exp n ≠ 0 from WithZero.exp_ne_zero)).toAdd = n := by
    simp only [WithZero.exp_eq_coe_ofAdd, WithZero.unzero_coe]
    rfl
  rw [hn]
  rw [hp, Real.log_zpow]
  change (n : ℝ) * Real.log (Real.exp (s : ℝ)) = _
  rw [Real.log_exp, mul_comm]

/-- The SAME whole original valuation is genuinely scaled to nonnegative real values. -/
def valuation {R : Type*} [Ring R] (v : Valuation R ℤᵐ⁰) (s : ℝ≥0) : Valuation R ℝ≥0 :=
  Valuation.map (scale s) (scale_monotone s) v

/-- Exact original function values are retained by the genuine scaling construction. -/
theorem valuation_apply {R : Type*} [Ring R] (v : Valuation R ℤᵐ⁰) (s : ℝ≥0) (a : R) :
    valuation v s a = scale s (v a) := rfl

end EnvelopeProperty.DiscreteValuationRealScale
