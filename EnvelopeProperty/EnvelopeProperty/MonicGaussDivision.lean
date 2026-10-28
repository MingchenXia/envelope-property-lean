/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.WeightedPolynomialSeminorm
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Finset

/-! # Genuine bounded monic polynomial division without normalized unit norms -/
open scoped NNReal Polynomial
open Polynomial
noncomputable section
namespace EnvelopeProperty.MonicGaussDivision
variable {A : Type*} [SeminormedCommRing A]

/-- The entire original one-variable finite weighted coefficient maximum. -/
def gauss (r : ℝ≥0) (f : A[X]) : ℝ≥0 :=
  f.support.sup fun i => ‖f.coeff i‖₊ * r ^ i

/-- Every original coefficient has its actual weighted bound, including outside support. -/
theorem le_gauss (r : ℝ≥0) (f : A[X]) (i : ℕ) :
    ‖f.coeff i‖₊ * r ^ i ≤ gauss r f := by
  classical
  by_cases hi : i ∈ f.support
  · exact Finset.le_sup (f := fun i => ‖f.coeff i‖₊ * r ^ i) hi
  · simp only [notMem_support_iff.mp hi, nnnorm_zero, zero_mul]
    exact zero_le

/-- The full Gauss bound is precisely the family of all coefficient bounds. -/
theorem gauss_le_iff (r : ℝ≥0) (f : A[X]) (c : ℝ≥0) :
    gauss r f ≤ c ↔ ∀ i, ‖f.coeff i‖₊ * r ^ i ≤ c := by
  exact ⟨fun h i => (le_gauss r f i).trans h, fun h => Finset.sup_le fun i _ => h i⟩

/-- Actual one-variable coefficient identification with the existing weighted polynomial norm. -/
theorem gauss_eq_weighted (r : ℝ≥0) (f : A[X]) :
    gauss r f = WeightedPolynomial.gauss (fun _ : PUnit.{1} => r)
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f) := by
  apply le_antisymm
  · apply (gauss_le_iff r f _).mpr
    intro i
    simpa only [MvPolynomial.coeff_uniqueAlgEquiv_symm,
      Finsupp.single_eq_same, WeightedPolynomial.weight_single] using
      WeightedPolynomial.le_gauss (fun _ : PUnit.{1} => r)
        ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f) (Finsupp.single () i)
  · apply (WeightedPolynomial.gauss_le_iff _ _ _).mpr
    intro m
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.unique_single m,
      WeightedPolynomial.weight_single, Finsupp.single_eq_same]
    exact le_gauss r f (m default)

@[simp]
theorem gauss_zero (r : ℝ≥0) : gauss r (0 : A[X]) = 0 := by simp [gauss]

@[simp]
theorem gauss_neg (r : ℝ≥0) (f : A[X]) : gauss r (-f) = gauss r f := by
  simp only [gauss_eq_weighted, map_neg, WeightedPolynomial.gauss_neg]

variable [IsUltrametricDist A]

/-- The genuine ultrametric coefficient norm controls the entire original sum. -/
theorem gauss_add_le_max (r : ℝ≥0) (f g : A[X]) :
    gauss r (f + g) ≤ max (gauss r f) (gauss r g) := by
  simpa only [gauss_eq_weighted, map_add] using
    WeightedPolynomial.gauss_add_le_max (fun _ : PUnit.{1} => r)
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f)
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm g)

/-- Genuine finite convolution controls products without a multiplicative coefficient norm. -/
theorem gauss_mul_le (r : ℝ≥0) (hr : 0 < r) (f g : A[X]) :
    gauss r (f * g) ≤ gauss r f * gauss r g := by
  simpa only [gauss_eq_weighted, map_mul] using
    WeightedPolynomial.gauss_mul_le (fun _ : PUnit.{1} => r) (fun _ => hr)
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f)
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm g)

omit [IsUltrametricDist A] in
/-- The leading monomial shifts every coefficient exactly, with no norm-of-one factor. -/
theorem gauss_X_pow_mul (r : ℝ≥0) (q : A[X]) (d : ℕ) :
    gauss r (X ^ d * q) = r ^ d * gauss r q := by
  apply le_antisymm
  · apply (gauss_le_iff r _ _).mpr
    intro i
    rw [coeff_X_pow_mul']
    split_ifs with hi
    · rw [← Nat.sub_add_cancel hi, pow_add]
      simp only [Nat.add_sub_cancel_right]
      calc
        ‖q.coeff (i - d)‖₊ * (r ^ (i - d) * r ^ d) =
            r ^ d * (‖q.coeff (i - d)‖₊ * r ^ (i - d)) := by ring
        _ ≤ _ := mul_le_mul' le_rfl (le_gauss r q (i-d))
    · simp
  · rw [gauss, Finset.mul_sup₀]
    exact Finset.sup_le fun i _ => by
      have h := le_gauss r (X ^ d * q) (i+d)
      rw [Polynomial.coeff_X_pow_mul, pow_add] at h
      simpa only [mul_comm, mul_left_comm, mul_assoc] using h

omit [IsUltrametricDist A] in
/-- The original nonleading coefficient hypothesis bounds the WHOLE actual lower tail. -/
theorem gauss_eraseLead_le (r : ℝ≥0) (p : A[X])
    (hp : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    gauss r p.eraseLead ≤ r ^ p.natDegree := by
  apply (gauss_le_iff r _ _).mpr
  intro i
  rw [eraseLead_coeff]
  split_ifs with hi
  · simp
  · by_cases hil : i < p.natDegree
    · exact hp i hil
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), nnnorm_zero, zero_mul]
      exact zero_le

/-- Actual monicity controls multiplication without asserting that the divisor has norm r^d. -/
theorem gauss_monic_mul_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (q : A[X]) : gauss r (p*q) ≤ r ^ p.natDegree * gauss r q := by
  have he : p = X ^ p.natDegree + p.eraseLead := by
    simpa only [hp.leadingCoeff, C_1, one_mul, add_comm] using
      p.eraseLead_add_C_mul_X_pow.symm
  conv_lhs => rw [he, add_mul]
  exact (gauss_add_le_max r _ _).trans (max_le
    (by rw [gauss_X_pow_mul])
    ((gauss_mul_le r hr _ _).trans (mul_le_mul' (gauss_eraseLead_le r p hbound) le_rfl)))

omit [IsUltrametricDist A] in
/-- A POSITIVE full coefficient maximum has an actual highest attaining index. -/
theorem exists_highest_eq_gauss (r : ℝ≥0) (q : A[X]) (hq : 0 < gauss r q) :
    ∃ N, ‖q.coeff N‖₊ * r ^ N = gauss r q ∧
      ∀ j, N < j → ‖q.coeff j‖₊ * r ^ j < gauss r q := by
  classical
  have hne : q.support.Nonempty := by
    by_contra h
    have he : q.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [gauss, he] at hq
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup q.support hne (fun j => ‖q.coeff j‖₊ * r ^ j)
  let s := q.support.filter fun j => ‖q.coeff j‖₊ * r ^ j = gauss r q
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩
  refine ⟨s.max' hs, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, ?_⟩
  intro j hj
  apply lt_of_le_of_ne (le_gauss r q j)
  intro hje
  have hj0 : q.coeff j ≠ 0 := by
    intro hz
    simp only [hz, nnnorm_zero, zero_mul] at hje
    exact hq.ne' hje.symm
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨mem_support_iff.mpr hj0, hje⟩
  exact (not_lt_of_ge (Finset.le_max' s j hjs)) hj

/-- A highest maximal coefficient of q survives in the ACTUAL coefficient of p*q. -/
theorem nnnorm_coeff_monic_mul_eq (r : ℝ≥0) (hr : 0 < r) {p q : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (hq : 0 < gauss r q) (N : ℕ)
    (hN : ‖q.coeff N‖₊ * r ^ N = gauss r q)
    (hhigh : ∀ j, N < j → ‖q.coeff j‖₊ * r ^ j < gauss r q) :
    ‖(p*q).coeff (N + p.natDegree)‖₊ = ‖q.coeff N‖₊ := by
  classical
  have hqN : 0 < ‖q.coeff N‖₊ := by
    by_contra h
    have hz : ‖q.coeff N‖₊ = 0 := le_antisymm (le_of_not_gt h) zero_le
    rw [hz, zero_mul] at hN
    exact hq.ne' hN.symm
  rw [mul_comm p q, coeff_mul]
  have hsum := IsNonarchimedean.apply_sum_eq_of_lt
    (R := ℝ≥0) (f := (nnnorm : A → ℝ≥0))
    (fun a b => IsUltrametricDist.nnnorm_add_le_max a b)
    (fun a : A => (nnnorm_neg a).symm)
    (s := Finset.antidiagonal (N + p.natDegree))
    (l := fun k : ℕ × ℕ => q.coeff k.1 * p.coeff k.2)
    (k := (N, p.natDegree)) (Finset.mem_antidiagonal.mpr rfl)
  rw [hsum, coeff_natDegree, hp.leadingCoeff, mul_one]
  intro k hk hkn
  rw [coeff_natDegree, hp.leadingCoeff, mul_one]
  have hkadd : k.1 + k.2 = N + p.natDegree := Finset.mem_antidiagonal.mp hk
  by_cases hkgt : p.natDegree < k.2
  · rw [coeff_eq_zero_of_natDegree_lt hkgt, mul_zero, nnnorm_zero]
    exact hqN
  · have hklt : k.2 < p.natDegree := by
      have hneq : k.2 ≠ p.natDegree := by
        intro he
        have : k.1 = N := by omega
        exact hkn (Prod.ext this he)
      omega
    have hki : N < k.1 := by omega
    apply (mul_lt_mul_iff_left₀ (pow_pos hr (N+p.natDegree))).mp
    change ‖q.coeff k.1 * p.coeff k.2‖₊ * r ^ (N+p.natDegree) <
      ‖q.coeff N‖₊ * r ^ (N+p.natDegree)
    calc
      ‖q.coeff k.1 * p.coeff k.2‖₊ * r ^ (N+p.natDegree) ≤
          (‖q.coeff k.1‖₊ * ‖p.coeff k.2‖₊) * r ^ (N+p.natDegree) :=
        mul_le_mul' (nnnorm_mul_le _ _) le_rfl
      _ = (‖q.coeff k.1‖₊ * r ^ k.1) * (‖p.coeff k.2‖₊ * r ^ k.2) := by
        rw [← hkadd, pow_add]
        ring
      _ ≤ (‖q.coeff k.1‖₊ * r ^ k.1) * r ^ p.natDegree :=
        mul_le_mul' le_rfl (hbound k.2 hklt)
      _ < gauss r q * r ^ p.natDegree :=
        mul_lt_mul_of_pos_right (hhigh k.1 hki) (pow_pos hr _)
      _ = ‖q.coeff N‖₊ * r ^ (N+p.natDegree) := by rw [← hN, pow_add, mul_assoc]

/-- The original quotient part is bounded from below even in the presence of a lower remainder. -/
theorem mul_gauss_le_monic_mul_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (q s : A[X]) (hs : s.degree < (p.natDegree : WithBot ℕ)) :
    r ^ p.natDegree * gauss r q ≤ gauss r (p*q+s) := by
  by_cases hq : gauss r q = 0
  · simp only [hq, mul_zero]
    exact zero_le
  · obtain ⟨N, hN, hhigh⟩ := exists_highest_eq_gauss r q (pos_iff_ne_zero.mpr hq)
    have he : ‖(p*q+s).coeff (N+p.natDegree)‖₊ = ‖q.coeff N‖₊ := by
      rw [coeff_add, (degree_lt_iff_coeff_zero s p.natDegree).mp hs
        (N+p.natDegree) (by omega), add_zero]
      exact nnnorm_coeff_monic_mul_eq r hr hp hbound (pos_iff_ne_zero.mpr hq) N hN hhigh
    calc
      r ^ p.natDegree * gauss r q = ‖q.coeff N‖₊ * r ^ (N+p.natDegree) := by
        rw [← hN, pow_add]
        ring
      _ = ‖(p*q+s).coeff (N+p.natDegree)‖₊ * r ^ (N+p.natDegree) := by rw [he]
      _ ≤ _ := le_gauss r _ _

/-- Exact WHOLE joint norm for original monic division; no unit-norm or domain assumptions. -/
theorem gauss_monic_mul_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (q s : A[X]) (hs : s.degree < (p.natDegree : WithBot ℕ)) :
    gauss r (p*q+s) = max (r ^ p.natDegree * gauss r q) (gauss r s) := by
  have hq := mul_gauss_le_monic_mul_add r hr hp hbound q s hs
  have hs' : gauss r s ≤ gauss r (p*q+s) := by
    have he : s = (p*q+s) + -(p*q) := by ring
    calc
      gauss r s = gauss r ((p*q+s) + -(p*q)) := congrArg (gauss r) he
      _ ≤ max (gauss r (p*q+s)) (gauss r (-(p*q))) := gauss_add_le_max r _ _
      _ ≤ gauss r (p*q+s) := max_le le_rfl (by
        rw [gauss_neg]
        exact (gauss_monic_mul_le r hr hp hbound q).trans hq)
  exact le_antisymm
    ((gauss_add_le_max r _ _).trans (max_le_max (gauss_monic_mul_le r hr hp hbound q) le_rfl))
    (max_le hq hs')

/-- The quotient and remainder are the ACTUAL algebraic monic division of the original polynomial. -/
theorem gauss_div_modByMonic (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : A[X]) :
    gauss r f = max (r ^ p.natDegree * gauss r (f /ₘ p)) (gauss r (f %ₘ p)) := by
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    have hz : ∀ g : A[X], g = 0 := fun g => Subsingleton.elim _ _
    simp only [hz, gauss_zero, mul_zero, max_self]
  · let := h
    have hs : (f %ₘ p).degree < (p.natDegree : WithBot ℕ) :=
      (degree_modByMonic_lt f hp).trans_le p.degree_le_natDegree
    have he := gauss_monic_mul_add r hr hp hbound (f /ₘ p) (f %ₘ p) hs
    rwa [add_comm, modByMonic_add_div] at he

/-- The genuine original quotient obeys its sharp weighted coefficient estimate. -/
theorem gauss_divByMonic_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : A[X]) :
    gauss r (f /ₘ p) ≤ gauss r f / r ^ p.natDegree := by
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  rw [mul_comm, gauss_div_modByMonic r hr hp hbound f]
  exact le_max_left _ _

/-- The actual original remainder is contractive in the weighted coefficient seminorm. -/
theorem gauss_modByMonic_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : A[X]) : gauss r (f %ₘ p) ≤ gauss r f := by
  rw [gauss_div_modByMonic r hr hp hbound f]
  exact le_max_right _ _

end EnvelopeProperty.MonicGaussDivision
