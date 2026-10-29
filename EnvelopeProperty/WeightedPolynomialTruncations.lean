/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.WeightedCompletionCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Original weighted polynomial truncations converge to every completed function -/
open scoped NNReal Topology
open UniformSpace Topology Filter
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EnvelopeProperty.WeightedPolynomialCompletion
open WeightedPolynomial
variable {A ι : Type*} [SeminormedCommRing A] [IsUltrametricDist A] [T0Space A] [CompleteSpace A]

/-- Every truncation is an ORIGINAL polynomial with coefficients in SAME A. -/
def truncationPolynomial (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (F : Finset (ι →₀ ℕ)) (f : Ring (A := A) w hw) : MvPolynomial ι A :=
  ∑ m ∈ F, MvPolynomial.monomial m (coefficientMap w hw m f)

/-- Every original exponent has its exact genuine finite-truncation coefficient. -/
theorem coeff_truncationPolynomial (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (F : Finset (ι →₀ ℕ)) (f : Ring (A := A) w hw) (m : ι →₀ ℕ) :
    (truncationPolynomial w hw F f).coeff m = if m ∈ F then coefficientMap w hw m f else 0 := by
  classical
  simp [truncationPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

/-- Every actual finite truncation is contractive on the ENTIRE original function. -/
theorem nnnorm_truncationPolynomial_le (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (F : Finset (ι →₀ ℕ)) (f : Ring (A := A) w hw) :
    ‖polynomialMap w hw (truncationPolynomial w hw F f)‖₊ ≤ ‖f‖₊ := by
  rw [nnnorm_polynomialMap]
  apply (gauss_le_iff w _ _).mpr
  intro m
  rw [coeff_truncationPolynomial]
  split_ifs
  · exact nnnorm_coefficientMap_weight_le w hw m f
  · simp

/-- The actual truncation error is bounded EXACTLY when all omitted original coefficients are. -/
theorem nnnorm_sub_truncation_le_iff (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (F : Finset (ι →₀ ℕ)) (f : Ring (A := A) w hw) (C : ℝ≥0) :
    ‖f-polynomialMap w hw (truncationPolynomial w hw F f)‖₊ ≤ C ↔
      ∀ m ∉ F, ‖coefficientMap w hw m f‖₊ * weight w m ≤ C := by
  classical
  rw [nnnorm_le_iff_coefficientMap]
  simp only [map_sub, coefficientMap_polynomialMap, coeff_truncationPolynomial]
  constructor
  · intro h m hm
    simpa only [if_neg hm,sub_zero] using h m
  · intro h m
    by_cases hm : m ∈ F
    · simp only [if_pos hm,sub_self,nnnorm_zero,zero_mul]
      exact zero_le
    · simpa only [if_neg hm,sub_zero] using h m hm

/-- The genuine error norm is exactly the bounded supremum of its omitted weighted coefficients. -/
theorem nnnorm_sub_truncation_eq_iSup (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (F : Finset (ι →₀ ℕ)) (f : Ring (A := A) w hw) :
    ‖f-polynomialMap w hw (truncationPolynomial w hw F f)‖₊ =
      ⨆ m, if m ∈ F then 0 else ‖coefficientMap w hw m f‖₊ * weight w m := by
  classical
  have hb : BddAbove (Set.range (fun m => if m ∈ F then 0 else ‖coefficientMap w hw m f‖₊ * weight w m)) := by
    refine ⟨‖f‖₊,?_⟩
    rintro _ ⟨m,rfl⟩
    dsimp only
    split_ifs
    · exact zero_le
    · exact nnnorm_coefficientMap_weight_le w hw m f
  apply le_antisymm
  · apply (nnnorm_sub_truncation_le_iff w hw F f _).mpr
    intro m hm
    simpa only [if_neg hm] using le_ciSup hb m
  · apply ciSup_le
    intro m
    by_cases hm : m ∈ F
    · simp only [if_pos hm]
      exact zero_le
    · rw [if_neg hm]
      exact (nnnorm_sub_truncation_le_iff w hw F f _).mp le_rfl m hm

/-- ORIGINAL finite polynomial images genuinely converge in norm to EVERY original completed function. -/
theorem tendsto_polynomialMap_truncationPolynomial (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) :
    Tendsto (fun F : Finset (ι →₀ ℕ) => polynomialMap w hw (truncationPolynomial w hw F f)) atTop (𝓝 f) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp (tendsto_weighted_coefficientMap w hw f)) (ε/2) (half_pos hε)
  have hfin := Filter.eventually_cofinite.mp he
  filter_upwards [eventually_ge_atTop hfin.toFinset] with F hF
  have hn : ‖f-polynomialMap w hw (truncationPolynomial w hw F f)‖₊ ≤ ⟨ε/2,le_of_lt (half_pos hε)⟩ := by
    apply (nnnorm_sub_truncation_le_iff w hw F f _).mpr
    intro m hm
    have hgood : dist (‖coefficientMap w hw m f‖₊ * weight w m) 0 < ε/2 := by
      by_contra hbad
      exact hm (hF (hfin.mem_toFinset.mpr hbad))
    apply NNReal.coe_le_coe.mp
    change ((‖coefficientMap w hw m f‖₊ * weight w m : ℝ≥0) : ℝ) ≤ ε/2
    simpa only [NNReal.dist_eq,NNReal.coe_zero,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)] using hgood.le
  have hn' : ‖f-polynomialMap w hw (truncationPolynomial w hw F f)‖ ≤ ε/2 := hn
  rw [dist_eq_norm,norm_sub_rev]
  exact hn'.trans_lt (half_lt_self hε)

/-- The genuine original monomial family is summable with sum equal to the ENTIRE function. -/
theorem hasSum_polynomialMap_monomial_coefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) :
    HasSum (fun m => polynomialMap w hw (MvPolynomial.monomial m (coefficientMap w hw m f))) f := by
  change Tendsto (fun F : Finset (ι →₀ ℕ) => ∑ m ∈ F,
    polynomialMap w hw (MvPolynomial.monomial m (coefficientMap w hw m f))) atTop (𝓝 f)
  simpa only [truncationPolynomial,map_sum] using tendsto_polynomialMap_truncationPolynomial w hw f

end EnvelopeProperty.WeightedPolynomialCompletion
