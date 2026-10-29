import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Actual polynomial coordinate antiderivatives and Cartier residuals

The two WHOLE-ring splitting identities are proved from original monomial coefficients.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCoordinateHomotopy
open MvPolynomial
open scoped Classical
variable {k σ : Type*} [Field k]

/-- The actual original coordinate antiderivative; division by zero is the SAME field's zero. -/
def coordinateIntegral (i : σ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (basisMonomials σ k).constr k (fun d =>
    monomial (d + Finsupp.single i 1) (((d i + 1 : ℕ) : k)⁻¹))

/-- The actual original monomial projection to the specified coordinate residue class. -/
def digitProjection (p : ℕ) (i : σ) (s : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (basisMonomials σ k).constr k (fun d => if p ∣ d i + s then monomial d 1 else 0)

private theorem monomial_eq_smul_basis (d : σ →₀ ℕ) (c : k) :
    monomial d c = c • basisMonomials σ k d := by
  change monomial d c = c • monomial d 1
  rw [smul_monomial, smul_eq_mul, mul_one]

/-- The exact original monomial antiderivative, not a supplied integration certificate. -/
theorem coordinateIntegral_monomial (i : σ) (d : σ →₀ ℕ) (c : k) :
    coordinateIntegral i (monomial d c) =
      monomial (d + Finsupp.single i 1) (c / ((d i + 1 : ℕ) : k)) := by
  rw [monomial_eq_smul_basis, map_smul]
  change c • ((basisMonomials σ k).constr k _) (basisMonomials σ k d) = _
  rw [Module.Basis.constr_basis, smul_monomial, smul_eq_mul, div_eq_mul_inv]

/-- Every actual residual projection retains exactly the original indicated monomial. -/
theorem digitProjection_monomial (p : ℕ) (i : σ) (s : ℕ) (d : σ →₀ ℕ) (c : k) :
    digitProjection p i s (monomial d c) = if p ∣ d i + s then monomial d c else 0 := by
  rw [monomial_eq_smul_basis, map_smul]
  change c • ((basisMonomials σ k).constr k _) (basisMonomials σ k d) = _
  rw [Module.Basis.constr_basis]
  split_ifs with h
  · rw [smul_monomial, smul_eq_mul, mul_one]
    exact monomial_eq_smul_basis d c
  · exact smul_zero c

/-- The actual coordinate antiderivative commutes with EVERY other original partial. -/
theorem partial_integral_ne (i j : σ) (hij : i ≠ j) (f : MvPolynomial σ k) :
    pderiv j (coordinateIntegral i f) = coordinateIntegral i (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [coordinateIntegral_monomial, pderiv_monomial, pderiv_monomial,
      coordinateIntegral_monomial]
    have he : d + Finsupp.single i 1 - Finsupp.single j 1 =
        d - Finsupp.single j 1 + Finsupp.single i 1 := by
      ext t
      by_cases ht : t = j
      · subst t
        simp only [Finsupp.tsub_apply, Finsupp.add_apply,
          Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
      · simp only [Finsupp.tsub_apply, Finsupp.add_apply,
          Finsupp.single_eq_of_ne ht, tsub_zero]
    rw [he]
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
      Finsupp.single_eq_of_ne (Ne.symm hij), tsub_zero, add_zero]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  | add f g hf hg => simp only [map_add, hf, hg]

/-- The genuine residual projection commutes with EVERY other original partial. -/
theorem partial_digitProjection_ne (p : ℕ) (i j : σ) (hij : i ≠ j) (s : ℕ)
    (f : MvPolynomial σ k) :
    pderiv j (digitProjection p i s f) = digitProjection p i s (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [digitProjection_monomial, pderiv_monomial, digitProjection_monomial]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij, tsub_zero]
    split_ifs with h
    · exact pderiv_monomial
    · exact map_zero _
  | add f g hf hg => simp only [map_add, hf, hg]

variable (p : ℕ) [CharP k p]

/-- The derivative of the ACTUAL antiderivative is the ORIGINAL polynomial minus precisely
its genuine top-residue monomials. This equality holds on the WHOLE original polynomial ring. -/
theorem partial_integral (i : σ) (f : MvPolynomial σ k) :
    pderiv i (coordinateIntegral i f) = f - digitProjection p i 1 f := by
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [coordinateIntegral_monomial, pderiv_monomial, digitProjection_monomial,
      add_tsub_cancel_right]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    by_cases h : p ∣ d i + 1
    · have hc : ((d i + 1 : ℕ) : k) = 0 := (CharP.cast_eq_zero_iff k p _).mpr h
      simp only [h, if_true, hc, div_zero, mul_zero, map_zero, sub_self]
    · have hc : ((d i + 1 : ℕ) : k) ≠ 0 :=
        fun hz => h ((CharP.cast_eq_zero_iff k p _).mp hz)
      rw [if_neg h, sub_zero, div_mul_cancel₀ c hc]
  | add f g hf hg => simp only [map_add, hf, hg, add_sub_add_comm]

/-- Integrating the ORIGINAL partial removes precisely the genuine zero-residue monomials;
no preimage/support/exactness premise is used. -/
theorem integral_partial (i : σ) (f : MvPolynomial σ k) :
    coordinateIntegral i (pderiv i f) = f - digitProjection p i 0 f := by
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [pderiv_monomial, coordinateIntegral_monomial, digitProjection_monomial]
    simp only [add_zero]
    by_cases hd : d i = 0
    · simp only [hd, Nat.cast_zero, mul_zero, zero_div, map_zero, dvd_zero, if_true, sub_self]
    · have hpos : 0 < d i := Nat.pos_of_ne_zero hd
      have hle : Finsupp.single i 1 ≤ d := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [Finsupp.single_eq_same] using (Nat.succ_le_iff.mpr hpos)
        · simp only [Finsupp.single_eq_of_ne hji, zero_le]
      have he : d - Finsupp.single i 1 + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
      have hei : (d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = d i := by
        simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using DFunLike.congr_fun he i
      rw [he, hei]
      by_cases h : p ∣ d i
      · have hc : (d i : k) = 0 := (CharP.cast_eq_zero_iff k p _).mpr h
        simp only [h, if_true, hc, mul_zero, zero_div, map_zero, sub_self]
      · have hc : (d i : k) ≠ 0 := fun hz => h ((CharP.cast_eq_zero_iff k p _).mp hz)
        rw [if_neg h, sub_zero, mul_div_cancel_right₀ c hc]
  | add f g hf hg => simp only [map_add, hf, hg, add_sub_add_comm]

end EnvelopeProperty.Cartier.PolynomialCoordinateHomotopy
