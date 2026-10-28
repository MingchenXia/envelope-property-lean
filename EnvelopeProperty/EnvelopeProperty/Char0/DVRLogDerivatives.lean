/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRJacobian
import Mathlib.Algebra.BigOperators.Option

/-!
# Actual logarithmic derivatives and Jacobian bounds in a DVR

The product of arbitrary actual coordinate functions divides the Jacobian
times one uniformizer. This is the logarithmic bound behind finite valuative
tests on simultaneous monomial charts.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing
open scoped Classical

variable {k V : Type*} [CommRing k] [CommRing V] [Algebra k V]
  [IsDomain V] [IsDiscreteValuationRing V]

/-- Multiplication by the actual uniformizer turns every actual derivative into a
logarithmic derivative preserving each principal ideal of the DVR. -/
theorem dvd_uniformizer_mul_derivation (D : Derivation k V V)
    {π : V} (hπ : Irreducible π) (x : V) : x ∣ π * D x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  apply u.mul_left_dvd.mpr
  have hp : π * D (π ^ m) = π ^ m * ((m : V) * D π) := by
    cases m with
    | zero => simp
    | succ m =>
      rw [D.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, pow_succ]
      ring
  rw [D.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
  have hcomm : π * ((u : V) * D (π ^ m)) = (u : V) * (π * D (π ^ m)) := by ring
  rw [hcomm, hp]
  exact dvd_add ⟨(u : V) * ((m : V) * D π), by ring⟩ ⟨π * D (u : V), by ring⟩

/-- An actual derivation annihilating the uniformizer preserves every principal ideal. -/
theorem dvd_derivation_of_uniformizer_eq_zero (D : Derivation k V V)
    {π : V} (hπ : Irreducible π) (hDπ : D π = 0) (x : V) : x ∣ D x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  apply u.mul_left_dvd.mpr
  rw [D.leibniz, D.leibniz_pow, hDπ]
  simp only [smul_eq_mul]
  exact ⟨D (u : V), by simp⟩

/-- Scaling only the uniformizer column gives a determinant divisible by the product
of all actual coordinate functions, including zero functions. -/
theorem prod_dvd_uniformizer_mul_jacobian {ι : Type*} [Fintype ι]
    (D : Option ι → Derivation k V V) {π : V} (hπ : Irreducible π)
    (hDπ : ∀ i, D (some i) π = 0) (x : Option ι → V) :
    (∏ i, x i) ∣ π * (Matrix.of fun i j => D j (x i)).det := by
  let q : Option ι → V := fun j => if j = none then π else 1
  let M : Matrix (Option ι) (Option ι) V := fun i j => D j (x i)
  let N : Matrix (Option ι) (Option ι) V := fun i j => q j * M i j
  have hdiv (i j : Option ι) : x i ∣ N i j := by
    cases j with
    | none => exact dvd_uniformizer_mul_derivation (D none) hπ (x i)
    | some j =>
      simpa only [N, q, M, Option.some_ne_none, if_false, one_mul] using
        dvd_derivation_of_uniformizer_eq_zero (D (some j)) hπ (hDπ j) (x i)
  choose Q hQ using hdiv
  have hN : N = Matrix.of (fun i j => x i * Q i j) := by
    ext i j
    exact hQ i j
  have hprod : ∏ j, q j = π := by simp [q]
  have hdet : N.det = π * M.det := by
    change (Matrix.of fun i j => q j * M i j).det = π * M.det
    rw [Matrix.det_mul_row, hprod]
  refine ⟨Matrix.det (Matrix.of Q), ?_⟩
  change π * M.det = (∏ i, x i) * Matrix.det (Matrix.of Q)
  rw [← hdet, hN]
  exact Matrix.det_mul_column x (Matrix.of Q)

/-- The actual normalized Jacobian satisfies the logarithmic order bound. -/
theorem sum_addVal_le_one_add_addVal_jacobian {ι : Type*} [Fintype ι]
    (D : Option ι → Derivation k V V) {π : V} (hπ : Irreducible π)
    (hDπ : ∀ i, D (some i) π = 0) (x : Option ι → V) :
    (∑ i, addVal V (x i)) ≤ 1 + addVal V (Matrix.of fun i j => D j (x i)).det := by
  have h := addVal_le_iff_dvd.mpr (prod_dvd_uniformizer_mul_jacobian D hπ hDπ x)
  have hprod (s : Finset (Option ι)) : addVal V (∏ i ∈ s, x i) = ∑ i ∈ s, addVal V (x i) := by
    induction s using Finset.induction_on with
    | empty => exact addVal_one
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]
  simpa only [hprod Finset.univ, addVal_mul, addVal_uniformizer hπ] using h

end EnvelopeProperty.Char0
