/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ValuationCompletion
import EnvelopeProperty.Berkovich.ValuationIntegral

/-!
# Extension of a complete ultrametric norm to algebraic fields

These genuine existence and uniqueness theorems require a complete ultrametric
normed coefficient field, permitting its norm to be trivial. They use Mathlib's
spectral norm in the nontrivial case and the monic equation estimate in the
trivial case. Existing declaration names and proofs are preserved from Finite.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

/-! ### Extensions of a complete nonarchimedean absolute value to algebraic extensions -/

section extension

variable {K L : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [Field L]
  [Algebra K L] [Algebra.IsAlgebraic K L]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- If the norm of `K` is trivial, every valuation `L → ℝ≥0` extending it is `≤ 1` (the integral
equation estimate applied to minimal polynomials). -/
theorem Valuation.le_one_of_trivial_of_isAlgebraic (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (v : Valuation L ℝ≥0) (hv : ∀ c : K, v (algebraMap K L c) = ‖c‖₊) (l : L) : v l ≤ 1 := by
  have hint : IsIntegral K l := (Algebra.IsAlgebraic.isAlgebraic l).isIntegral
  refine Valuation.le_of_monic_eval₂_eq_zero v (algebraMap K L) (minpoly.monic hint)
    (by rw [← Polynomial.aeval_def]; exact minpoly.aeval K l) le_rfl fun i _ => ?_
  rw [hv]
  by_cases hc : (minpoly K l).coeff i = 0
  · simp [hc]
  · rw [← NNReal.coe_le_coe, coe_nnnorm, hK _ hc, NNReal.coe_one]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- If the norm of `K` is trivial, the only valuation `L → ℝ≥0` extending it is trivial. -/
theorem Valuation.eq_one_of_trivial_of_isAlgebraic (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (v : Valuation L ℝ≥0) (hv : ∀ c : K, v (algebraMap K L c) = ‖c‖₊) {l : L} (hl : l ≠ 0) :
    v l = 1 := by
  have h1 := Valuation.le_one_of_trivial_of_isAlgebraic hK v hv l
  have h2 := Valuation.le_one_of_trivial_of_isAlgebraic hK v hv l⁻¹
  have h3 : v l * v l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have := mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

/-- **Existence of extensions.** The norm of a complete nonarchimedean normed field `K` extends to
a multiplicative ultrametric norm (an `ℝ≥0`-valued valuation) on any algebraic extension `L`: the
spectral norm if the norm of `K` is nontrivial, the trivial absolute value otherwise. -/
theorem Valuation.exists_extends_norm :
    ∃ w : Valuation L ℝ≥0, ∀ c : K, w (algebraMap K L c) = ‖c‖₊ := by
  classical
  by_cases hK : ∃ c : K, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne hK
    refine ⟨{ toFun := fun l => ⟨spectralNorm K L l, spectralNorm_nonneg l⟩
              map_zero' := NNReal.eq spectralNorm_zero
              map_one' := NNReal.eq spectralNorm_one
              map_mul' := fun a b => NNReal.eq (spectralAlgNorm_mul a b)
              map_add_le_max' := fun a b =>
                le_max_iff.2 (le_max_iff.1 (isNonarchimedean_spectralNorm a b)) }, fun c => ?_⟩
    exact NNReal.eq (spectralNorm_extends c)
  · push Not at hK
    refine ⟨1, fun c => ?_⟩
    by_cases hc : c = 0
    · simp [hc]
    · rw [Valuation.one_apply_of_ne_zero ((map_ne_zero (algebraMap K L)).2 hc)]
      exact NNReal.eq (by rw [coe_nnnorm, hK c hc, NNReal.coe_one])

/-- **Uniqueness of extensions.** Two `ℝ≥0`-valued valuations on an algebraic extension `L` of a
complete nonarchimedean normed field `K` that both extend the norm of `K` coincide (Mathlib's
`spectralNorm_unique_field_norm_ext` if the norm of `K` is nontrivial). -/
theorem Valuation.eq_of_extends_norm {v w : Valuation L ℝ≥0}
    (hv : ∀ c : K, v (algebraMap K L c) = ‖c‖₊) (hw : ∀ c : K, w (algebraMap K L c) = ‖c‖₊) :
    v = w := by
  by_cases hK : ∃ c : K, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne hK
    ext l
    have hv' := spectralNorm_unique_field_norm_ext (f := Valuation.toRealAbs v)
      (fun c => by rw [Valuation.toRealAbs_apply, hv, coe_nnnorm]) l
    have hw' := spectralNorm_unique_field_norm_ext (f := Valuation.toRealAbs w)
      (fun c => by rw [Valuation.toRealAbs_apply, hw, coe_nnnorm]) l
    rw [Valuation.toRealAbs_apply] at hv' hw'
    exact hv'.trans hw'.symm
  · push Not at hK
    ext l
    by_cases hl : l = 0
    · simp [hl]
    · rw [Valuation.eq_one_of_trivial_of_isAlgebraic hK v hv hl,
        Valuation.eq_one_of_trivial_of_isAlgebraic hK w hw hl]

end extension

end EnvelopeProperty
