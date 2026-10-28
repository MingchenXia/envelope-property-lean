/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumGauss
import EnvelopeProperty.Berkovich.SpectrumLocalization
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Genuine positive-radius Laurent Gauss seminorms

All values are produced by the actual localization of the polynomial Gauss
valuation. Arbitrary commutative coefficient rings and coefficient seminorms
are allowed; only the coordinate radius must be positive.
-/
open scoped Polynomial LaurentPolynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A : Type*} [CommRing A]

/-- The actual positive-radius polynomial Gauss valuation extends to the genuine Laurent localization. -/
def laurentGauss (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) : Spectrum A[T;T⁻¹] :=
  Away.lift A[T;T⁻¹] (X : A[X]) (gauss (ofValuation v) r) (by simpa using hr.ne')

@[simp]
theorem laurentGauss_val_toLaurent (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (p : A[X]) :
    (laurentGauss v r hr).val (Polynomial.toLaurent p) = gaussFun v r p :=
  Away.lift_val_algebraMap _ _ _ _ _

@[simp]
theorem laurentGauss_val_C (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (a : A) :
    (laurentGauss v r hr).val (LaurentPolynomial.C a) = v a := by
  rw [← Polynomial.toLaurent_C, laurentGauss_val_toLaurent, gaussFun_C]

@[simp]
theorem laurentGauss_val_T_nat (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (n : ℕ) :
    (laurentGauss v r hr).val (LaurentPolynomial.T n) = r ^ n := by
  rw [← Polynomial.toLaurent_X_pow, laurentGauss_val_toLaurent]
  change (gaussValuation v r) (X ^ n) = r ^ n
  rw [map_pow]
  change (gaussFun v r X) ^ n = r ^ n
  rw [gaussFun_X]

@[simp]
theorem laurentGauss_val_T_neg_nat (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (n : ℕ) :
    (laurentGauss v r hr).val (LaurentPolynomial.T (-(n : ℤ))) = (r ^ n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← laurentGauss_val_T_nat v r hr n, ← map_mul, ← LaurentPolynomial.T_add]
  simp

/-- The genuine original coordinate values are determined for ALL integer exponents. -/
theorem laurentGauss_val_T (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (n : ℤ) :
    (laurentGauss v r hr).val (LaurentPolynomial.T n) = r ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n =>
    change (laurentGauss v r hr).val (LaurentPolynomial.T (-((n+1 : ℕ) : ℤ))) =
      r ^ (-((n+1 : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast]
    exact laurentGauss_val_T_neg_nat v r hr (n+1)

/-- Whole original Laurent coefficients shift by the actual monomial multiplication. -/
theorem coeff_mul_T (f : A[T;T⁻¹]) (n i : ℤ) :
    (f * LaurentPolynomial.T n).coeff i = f.coeff (i-n) := by
  change (f * AddMonoidAlgebra.single n 1).coeff i = _
  simp only [AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

@[simp]
theorem coeff_toLaurent_nat (p : A[X]) (i : ℕ) :
    (Polynomial.toLaurent p).coeff i = p.coeff i := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply (f := (Nat.castEmbedding : ℕ ↪ ℤ))
    Nat.castEmbedding.injective p.toFinsupp.coeff i).trans (Polynomial.toFinsupp_apply p i)

/-- A negative original exponent has zero coefficient in an actual ordinary polynomial. -/
theorem coeff_toLaurent_of_neg (p : A[X]) (i : ℤ) (hi : i < 0) :
    (Polynomial.toLaurent p).coeff i = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n, hn⟩
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  change (n : ℤ) = i at hn
  omega

/-- EVERY original Laurent coefficient is bounded by its actual positive-radius Gauss value. -/
theorem le_laurentGauss_val (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r)
    (f : A[T;T⁻¹]) (i : ℤ) :
    v (f.coeff i) * r ^ i ≤ (laurentGauss v r hr).val f := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have hc : (Polynomial.toLaurent p).coeff (i+n) = f.coeff i := by
    rw [hp, coeff_mul_T]
    simp
  by_cases hi : 0 ≤ i+n
  · let m : ℕ := (i+n).toNat
    have hm : (m : ℤ) = i+n := Int.toNat_of_nonneg hi
    have hcm : p.coeff m = f.coeff i := by
      rw [← coeff_toLaurent_nat, hm]
      exact hc
    have hv : gaussFun v r p = (laurentGauss v r hr).val f * r ^ n := by
      rw [← laurentGauss_val_toLaurent v r hr p, hp, map_mul, laurentGauss_val_T_nat]
    apply (mul_le_mul_iff_left₀ (pow_pos hr n)).mp
    rw [← hv, mul_assoc, ← zpow_natCast, ← zpow_add₀ hr.ne', ← hm, zpow_natCast]
    rw [← hcm]
    exact le_gaussFun v r p m
  · have hzero : f.coeff i = 0 := by
      rw [← hc]
      exact coeff_toLaurent_of_neg p (i+n) (lt_of_not_ge hi)
    rw [hzero, map_zero, zero_mul]
    exact zero_le

/-- The full original Laurent expansion has exactly its genuine coefficient maximum value. -/
theorem laurentGauss_val_eq_sup (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r)
    (f : A[T;T⁻¹]) :
    (laurentGauss v r hr).val f = f.coeff.support.sup (fun i => v (f.coeff i) * r ^ i) := by
  classical
  apply le_antisymm
  · have hf : f = ∑ i ∈ f.coeff.support, LaurentPolynomial.C (f.coeff i) * LaurentPolynomial.T i := by
      simpa only [Finsupp.sum, LaurentPolynomial.single_eq_C_mul_T] using
        (AddMonoidAlgebra.sum_coeff_single f).symm
    calc
      (laurentGauss v r hr).val f = (laurentGauss v r hr).val
          (∑ i ∈ f.coeff.support, LaurentPolynomial.C (f.coeff i) * LaurentPolynomial.T i) := congrArg _ hf
      _ ≤ _ := (laurentGauss v r hr).val.map_sum_le fun i hi => by
        rw [map_mul, laurentGauss_val_C, laurentGauss_val_T]
        exact Finset.le_sup (f := fun i : ℤ => v (f.coeff i) * r ^ i) hi
  · exact Finset.sup_le fun i _ => le_laurentGauss_val v r hr f i

/-- Faithfulness follows from the ACTUAL original coefficient seminorm, without assuming a field. -/
theorem laurentGauss_val_eq_zero_iff (v : Valuation A ℝ≥0) (hv : ∀ a, v a = 0 ↔ a = 0)
    (r : ℝ≥0) (hr : 0 < r) (f : A[T;T⁻¹]) :
    (laurentGauss v r hr).val f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply LaurentPolynomial.ext
    intro i
    have hb : v (f.coeff i) * r ^ i ≤ 0 := by simpa only [h] using le_laurentGauss_val v r hr f i
    have hcoeff : v (f.coeff i) = 0 :=
      (mul_eq_zero.mp (le_zero_iff.mp hb)).resolve_right (zpow_ne_zero i hr.ne')
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using (hv _).mp hcoeff
  · rintro rfl
    exact map_zero _

/-- Every whole Laurent point has the actual integer-power coordinate values. -/
theorem laurent_val_T (x : Spectrum A[T;T⁻¹]) (i : ℤ) :
    x.val (LaurentPolynomial.T i) = (x.val (LaurentPolynomial.T 1)) ^ i := by
  have hnat (n : ℕ) : x.val (LaurentPolynomial.T (n : ℤ)) =
      (x.val (LaurentPolynomial.T 1)) ^ n := by
    rw [show LaurentPolynomial.T (n : ℤ) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) ^ n by
      simpa only [mul_one] using (LaurentPolynomial.T_pow 1 n).symm, map_pow]
  cases i with
  | ofNat n =>
    change x.val (LaurentPolynomial.T (n : ℤ)) = (x.val (LaurentPolynomial.T 1)) ^ (n : ℤ)
    rw [zpow_natCast]
    exact hnat n
  | negSucc n =>
    change x.val (LaurentPolynomial.T (-((n+1 : ℕ) : ℤ))) =
      (x.val (LaurentPolynomial.T 1)) ^ (-((n+1 : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast]
    apply eq_inv_of_mul_eq_one_left
    rw [← hnat (n+1), ← map_mul, ← LaurentPolynomial.T_add]
    simp

/-- The WHOLE original Laurent value at every annulus point is bounded by the true endpoint maximum. -/
theorem laurent_val_le_max_endpoint (v : Valuation A ℝ≥0) (ρ r : ℝ≥0)
    (hρ : 0 < ρ) (hr : 0 < r) (x : Spectrum A[T;T⁻¹])
    (hx : ∀ a, x.val (LaurentPolynomial.C a) = v a)
    (hρx : ρ ≤ x.val (LaurentPolynomial.T 1)) (hxr : x.val (LaurentPolynomial.T 1) ≤ r)
    (f : A[T;T⁻¹]) :
    x.val f ≤ max ((laurentGauss v ρ hρ).val f) ((laurentGauss v r hr).val f) := by
  classical
  have hf : f = ∑ i ∈ f.coeff.support, LaurentPolynomial.C (f.coeff i) * LaurentPolynomial.T i := by
    simpa only [Finsupp.sum, LaurentPolynomial.single_eq_C_mul_T] using
      (AddMonoidAlgebra.sum_coeff_single f).symm
  conv_lhs => rw [hf]
  apply x.val.map_sum_le
  intro i _
  rw [map_mul, hx, laurent_val_T]
  have ht : 0 < x.val (LaurentPolynomial.T 1) := hρ.trans_le hρx
  cases i with
  | ofNat n =>
    apply le_trans (b := v (f.coeff (n : ℤ)) * r ^ (n : ℤ))
    · change v (f.coeff (n : ℤ)) * (x.val (LaurentPolynomial.T 1)) ^ (n : ℤ) ≤
        v (f.coeff (n : ℤ)) * r ^ (n : ℤ)
      rw [zpow_natCast, zpow_natCast]
      exact mul_le_mul' le_rfl (pow_le_pow_left' hxr n)
    · exact (le_laurentGauss_val v r hr f n).trans (le_max_right _ _)
  | negSucc n =>
    apply le_trans (b := v (f.coeff (Int.negSucc n)) * ρ ^ (Int.negSucc n))
    · apply mul_le_mul' le_rfl
      rw [zpow_negSucc, zpow_negSucc]
      exact (inv_le_inv₀ (pow_pos ht _) (pow_pos hρ _)).mpr (pow_le_pow_left' hρx _)
    · exact (le_laurentGauss_val v ρ hρ f (Int.negSucc n)).trans (le_max_left _ _)

end EnvelopeProperty.Berkovich.Spectrum
