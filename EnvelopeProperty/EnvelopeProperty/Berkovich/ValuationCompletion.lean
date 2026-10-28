/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Absolute values and completions of real-valued ultrametric valuations

These general helpers turn a real-valued valuation on a field into an absolute
value, retain the ultrametric inequality under completion, characterize valuations
on fraction/residue fields by their values on the original ring, and extend
norm preservation to completions. No coefficient field or trivial base valuation
is required. The existing declarations and proofs are extracted unchanged from
`EnvelopeProperty.Berkovich.ResidueField`.
-/

open scoped NNReal ENNReal Topology nonZeroDivisors

noncomputable section

namespace EnvelopeProperty

/-! ### Real absolute values from `ℝ≥0`-valued valuations -/

/-- An `ℝ≥0`-valued valuation on a field, regarded as a real absolute value. -/
def Valuation.toRealAbs {K : Type*} [Field K] (v : Valuation K ℝ≥0) : AbsoluteValue K ℝ where
  toFun z := (v z : ℝ)
  map_mul' a b := by simp
  nonneg' z := NNReal.coe_nonneg _
  eq_zero' z := by simp
  add_le' a b := by
    have h' : (v (a + b) : ℝ) ≤ max (v a : ℝ) (v b : ℝ) := by exact_mod_cast v.map_add a b
    exact h'.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

@[simp]
theorem Valuation.toRealAbs_apply {K : Type*} [Field K] (v : Valuation K ℝ≥0) (z : K) :
    Valuation.toRealAbs v z = v z := rfl

theorem Valuation.isNonarchimedean_toRealAbs {K : Type*} [Field K] (v : Valuation K ℝ≥0) :
    IsNonarchimedean (Valuation.toRealAbs v) := by
  intro a b
  simp only [Valuation.toRealAbs_apply]
  exact_mod_cast v.map_add a b

/-- The completion of an ultrametric normed group is ultrametric. -/
instance UniformSpace.Completion.isUltrametricDist' {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] : IsUltrametricDist (UniformSpace.Completion E) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b => ?_
  induction a, b using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact IsUltrametricDist.norm_add_le_max a b

/-! ### Valuations on fraction fields -/

/-- A valuation on a fraction field `K` of `D` is determined by its values on `D`. -/
theorem Valuation.ext_of_isFractionRing {D K Γ₀ : Type*} [CommRing D] [Field K] [Algebra D K]
    [IsFractionRing D K] [LinearOrderedCommGroupWithZero Γ₀] {v w : Valuation K Γ₀}
    (h : ∀ d : D, v (algebraMap D K d) = w (algebraMap D K d)) : v = w := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq D⁰ z
  rw [IsFractionRing.mk'_eq_div, map_div₀, map_div₀, h, h]

/-- A valuation on the residue field `κ(p)` of a prime `p` of `R` is determined by its values on
`R`. -/
theorem Valuation.ext_of_residueField {R Γ₀ : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    [LinearOrderedCommGroupWithZero Γ₀] {v w : Valuation p.ResidueField Γ₀}
    (h : ∀ r : R, v (algebraMap R _ r) = w (algebraMap R _ r)) : v = w := by
  refine Valuation.ext_of_isFractionRing (D := R ⧸ p) fun d => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [Ideal.algebraMap_quotient_residueField_mk, h]

/-- The map of completions induced by an isometric ring homomorphism of normed fields is
isometric. -/
theorem UniformSpace.Completion.norm_mapRingHom {F F' : Type*} [NormedField F] [NormedField F']
    (f : F →+* F') (hf : ∀ a, ‖f a‖ = ‖a‖) (z : UniformSpace.Completion F) :
    ‖UniformSpace.Completion.mapRingHom f
      (AddMonoidHomClass.isometry_of_norm f hf).continuous z‖ = ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by
      simp only [UniformSpace.Completion.mapRingHom_apply]
      exact (UniformSpace.Completion.continuous_map).norm) continuous_norm
  | ih a =>
    rw [UniformSpace.Completion.mapRingHom_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, hf]

end EnvelopeProperty
