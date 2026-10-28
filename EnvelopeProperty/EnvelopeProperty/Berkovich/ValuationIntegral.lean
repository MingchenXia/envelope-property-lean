/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Integral equation bounds for real-valued ultrametric seminorms

The monic-root estimate below applies to arbitrary homomorphisms of commutative
rings and arbitrary real-valued ultrametric seminorms. It is the algebraic input
for compact inverse images under integral maps and for the integral-equation
argument in FHX `lem:growth`(2). No field, finite type, or completeness hypothesis
is required.

The declaration is extracted from `EnvelopeProperty.Berkovich.Finite`, with its
existing name and proof preserved.
-/

open scoped NNReal ENNReal Topology

open Topology

noncomputable section

namespace EnvelopeProperty

/-- **Integral equation estimate.** If `f` is a root of a monic polynomial `p` whose coefficients
`bᵢ` (mapped by `ψ`) satisfy `v(bᵢ) ≤ r` for `i < deg p`, where `r ≥ 1`, then `v(f) ≤ r`. This is
the form of `EnvelopeProperty.valuation_le_of_monic_eval₂_eq_zero` (FHX Lemma 5.8(2)) used for
the properness of finite morphisms. -/
theorem Valuation.le_of_monic_eval₂_eq_zero {R A : Type*} [CommRing R] [CommRing A]
    (v : Valuation A ℝ≥0) (ψ : R →+* A) {p : Polynomial R} (hp : p.Monic) {f : A}
    (hf : p.eval₂ ψ f = 0) {r : ℝ≥0} (hr1 : 1 ≤ r)
    (hr : ∀ i < p.natDegree, v (ψ (p.coeff i)) ≤ r) : v f ≤ r := by
  by_contra hlt
  rw [not_le] at hlt
  have hvf : 0 < v f := lt_of_le_of_lt zero_le hlt
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have heq : f ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i := by
    have h := hf
    rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at h
    exact eq_neg_of_add_eq_zero_left h
  have hlt' : v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) < v f ^ p.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hvf.ne') fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [v.map_mul, v.map_pow]
    calc v (ψ (p.coeff i)) * v f ^ i ≤ r ^ (p.natDegree - i) * v f ^ i :=
          mul_le_mul_of_nonneg_right ((hr i hi').trans (le_self_pow₀ hr1 (by omega))) zero_le
      _ < v f ^ (p.natDegree - i) * v f ^ i :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hlt hr0.le (by omega)) (pow_pos hvf _)
      _ = v f ^ p.natDegree := by rw [← pow_add, Nat.sub_add_cancel hi'.le]
  have h2 : v (f ^ p.natDegree) = v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) := by
    rw [heq, Valuation.map_neg]
  rw [v.map_pow] at h2
  rw [← h2] at hlt'
  exact lt_irrefl _ hlt'

end EnvelopeProperty
