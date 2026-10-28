/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsParameter
import EnvelopeProperty.PolynomialCoefficientSwap

/-!
# Coefficient preservation for the original relative parameter exchange

These lemmas use the original `MultiplierBaseIdeals.parameterEquiv` to
convert homogeneous relative polynomials over `k[t]` into actual ambient
polynomials whose individual `t`-coefficients have the same `x`-degree.
-/

open scoped Polynomial

noncomputable section

namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals

universe u

variable {k : Type u} [Field k] {M : ℕ}

/-- The inverse of the original parameter exchange is exactly the existing
whole native coefficient interchange. -/
theorem parameterEquiv_symm_eq_polynomialCoefficientSwap :
    (parameterEquiv (k := k) (M := M)).symm =
      polynomialCoefficientSwap k (Fin (M + 1)) := by
  rfl

/-- The original parameter exchange preserves each actual coefficient
indexed by the same parameter exponent and the same original multi-index. -/
theorem parameterEquiv_coeff_coeff (F : (MvPolynomial (Fin (M + 1)) k)[X])
    (α : Fin (M + 1) →₀ ℕ) (l : ℕ) :
    ((parameterEquiv F).coeff α).coeff l = (F.coeff l).coeff α := by
  classical
  induction F using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial n s =>
      rw [parameterEquiv_monomial]
      rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
      rw [mul_comm, Polynomial.C_mul_X_pow_eq_monomial]
      by_cases h : n = l <;> simp [Polynomial.coeff_monomial, h]

/-- A homogeneous relative section over the actual coefficient ring `k[t]`
gives the coefficient degree condition used by polynomial cone generators. -/
theorem parameterEquiv_symm_coeff_isHomogeneous
    {P : MvPolynomial (Fin (M + 1)) k[X]} {e : ℕ} (hP : P.IsHomogeneous e) (l : ℕ) :
    (((parameterEquiv (k := k) (M := M)).symm P).coeff l).IsHomogeneous e := by
  rw [parameterEquiv_symm_eq_polynomialCoefficientSwap]
  have hcomponent := polynomialCoefficientSwap_coeff_homogeneousComponent k (Fin (M + 1)) P e l
  rw [MvPolynomial.homogeneousComponent_eq_self hP] at hcomponent
  rw [hcomponent]
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- Homogeneity of the entire original relative polynomial gives the same
homogeneous degree for each actual parameter coefficient. -/
theorem parameterEquiv_coeff_isHomogeneous {F : (MvPolynomial (Fin (M + 1)) k)[X]}
    {e : ℕ} (hF : (parameterEquiv F).IsHomogeneous e) (l : ℕ) :
    (F.coeff l).IsHomogeneous e := by
  simpa only [AlgEquiv.symm_apply_apply] using parameterEquiv_symm_coeff_isHomogeneous hF l

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
