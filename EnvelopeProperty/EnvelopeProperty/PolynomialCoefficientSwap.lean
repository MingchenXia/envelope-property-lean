/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Whole interchange of polynomial coefficients and variables

Actual Mathlib optional-variable algebra isomorphisms give the entire coefficient
interchange over any commutative semiring. Genuine monomial and coefficient identities
prove that every homogeneous-component operator commutes with univariate coefficients.
No field, finite variable set or comparison certificate is assumed.
-/

open scoped Polynomial
open MvPolynomial
noncomputable section
namespace EnvelopeProperty
variable (R σ : Type*) [CommSemiring R]

/-- The actual whole-ring interchange of the univariate coefficient and multivariable variable roles. -/
def polynomialCoefficientSwap : MvPolynomial σ R[X] ≃ₐ[R] (MvPolynomial σ R)[X] :=
  (MvPolynomial.optionEquivRight R σ).symm.trans (MvPolynomial.optionEquivLeft R σ)

@[simp]
theorem polynomialCoefficientSwap_X (i : σ) :
    polynomialCoefficientSwap R σ (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i) := by
  change MvPolynomial.optionEquivLeft R σ ((MvPolynomial.optionEquivRight R σ).symm (MvPolynomial.X i)) = _
  rw [← MvPolynomial.optionEquivRight_X_some, AlgEquiv.symm_apply_apply,
    MvPolynomial.optionEquivLeft_X_some]

@[simp]
theorem polynomialCoefficientSwap_C (p : R[X]) :
    polynomialCoefficientSwap R σ (MvPolynomial.C p) = Polynomial.map MvPolynomial.C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have hC : polynomialCoefficientSwap R σ (MvPolynomial.C (Polynomial.C r)) =
        Polynomial.C (MvPolynomial.C r) := (polynomialCoefficientSwap R σ).commutes r
    have hX : polynomialCoefficientSwap R σ (MvPolynomial.C Polynomial.X) = Polynomial.X := by
      change MvPolynomial.optionEquivLeft R σ
        ((MvPolynomial.optionEquivRight R σ).symm (MvPolynomial.C Polynomial.X)) = _
      rw [← MvPolynomial.optionEquivRight_X_none, AlgEquiv.symm_apply_apply,
        MvPolynomial.optionEquivLeft_X_none]
    rw [hC, hX]

/-- The entire actual swapped monomial retains its whole coefficient polynomial. -/
theorem polynomialCoefficientSwap_monomial (m : σ →₀ ℕ) (p : R[X]) :
    polynomialCoefficientSwap R σ (MvPolynomial.monomial m p) =
      Polynomial.map MvPolynomial.C p * Polynomial.C (MvPolynomial.monomial m (1 : R)) := by
  rw [MvPolynomial.monomial_eq, map_mul, polynomialCoefficientSwap_C,
    MvPolynomial.monic_monomial_eq]
  congr 1
  simp only [Finsupp.prod, map_prod, map_pow, polynomialCoefficientSwap_X]

/-- Every actual univariate coefficient of a swapped monomial is the corresponding original homogeneous monomial. -/
theorem polynomialCoefficientSwap_monomial_coeff (m : σ →₀ ℕ) (p : R[X]) (i : ℕ) :
    (polynomialCoefficientSwap R σ (MvPolynomial.monomial m p)).coeff i =
      MvPolynomial.monomial m (p.coeff i) := by
  rw [polynomialCoefficientSwap_monomial]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]

/-- Genuine coefficient interchange commutes with EVERY actual homogeneous-component operator on the whole polynomial. -/
theorem polynomialCoefficientSwap_coeff_homogeneousComponent (F : MvPolynomial σ R[X])
    (d i : ℕ) :
    (polynomialCoefficientSwap R σ (MvPolynomial.homogeneousComponent d F)).coeff i =
      MvPolynomial.homogeneousComponent d ((polynomialCoefficientSwap R σ F).coeff i) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m p =>
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial p rfl),
      polynomialCoefficientSwap_monomial_coeff,
      MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.isHomogeneous_monomial (p.coeff i) rfl)]
    split_ifs <;> simp only [map_zero, Polynomial.coeff_zero, polynomialCoefficientSwap_monomial_coeff]
  | add F G hF hG => simp only [map_add, Polynomial.coeff_add, hF, hG]

end EnvelopeProperty
