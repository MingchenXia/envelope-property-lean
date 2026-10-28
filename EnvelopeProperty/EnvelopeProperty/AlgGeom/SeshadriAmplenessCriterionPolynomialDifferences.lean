import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Actual polynomial differences, prior to geometric intersection construction. -/
noncomputable section
open Polynomial
namespace EnvelopeProperty.SeshadriAmplenessCriterion

def polynomialForwardDifference (p : ℚ[X]) : ℚ[X] := taylor 1 p - p

theorem polynomialForwardDifference_eval (p : ℚ[X]) (x : ℚ) :
    (polynomialForwardDifference p).eval x = p.eval (x + 1) - p.eval x := by
  rw [polynomialForwardDifference, eval_sub, taylor_eval]

theorem polynomialForwardDifference_natDegree_le (p : ℚ[X]) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) : (polynomialForwardDifference p).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hd : (hasseDeriv n p).natDegree ≤ 0 :=
    (natDegree_hasseDeriv_le p n).trans (by omega)
  rw [polynomialForwardDifference, coeff_sub, taylor_coeff,
    eq_C_of_natDegree_le_zero hd, eval_C, hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul, sub_self]

theorem polynomialForwardDifference_coeff (p : ℚ[X]) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) :
    (polynomialForwardDifference p).coeff d = (d + 1 : ℚ) * p.coeff (d + 1) := by
  have hd : (hasseDeriv d p).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le p d) (by omega)
  have he := eval_eq_sum_range' hd (1 : ℚ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one] at he
  rw [polynomialForwardDifference, coeff_sub, taylor_coeff, he,
    hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.add_comm 1 d, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
  ring

theorem polynomialForwardDifference_eq_zero_of_natDegree_le_zero (p : ℚ[X])
    (hp : p.natDegree ≤ 0) : polynomialForwardDifference p = 0 := by
  rw [eq_C_of_natDegree_le_zero hp, polynomialForwardDifference, taylor_C, sub_self]

def iteratedPolynomialForwardDifference : ℕ → ℚ[X] → ℚ[X]
  | 0, p => p
  | n + 1, p => iteratedPolynomialForwardDifference n (polynomialForwardDifference p)

theorem iteratedPolynomialForwardDifference_natDegree_le (d n : ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ n + d) :
    (iteratedPolynomialForwardDifference d p).natDegree ≤ n := by
  induction d generalizing p with
  | zero => exact hp.trans (by omega)
  | succ d ih =>
    apply ih
    exact polynomialForwardDifference_natDegree_le p (n + d) (by omega)

private theorem iteratedPolynomialForwardDifference_coeff_zero (d : ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ d) :
    (iteratedPolynomialForwardDifference d p).coeff 0 = (d.factorial : ℚ) * p.coeff d := by
  induction d generalizing p with
  | zero => simp [iteratedPolynomialForwardDifference]
  | succ d ih =>
    change (iteratedPolynomialForwardDifference d (polynomialForwardDifference p)).coeff 0 = _
    rw [ih _ (polynomialForwardDifference_natDegree_le p d hp),
      polynomialForwardDifference_coeff p d hp, Nat.factorial_succ]
    push_cast
    ring

theorem iteratedPolynomialForwardDifference_eq_C_factorial_mul_coeff (d : ℕ)
    (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    iteratedPolynomialForwardDifference d p = C ((d.factorial : ℚ) * p.coeff d) := by
  have hd : (iteratedPolynomialForwardDifference d p).natDegree ≤ 0 :=
    iteratedPolynomialForwardDifference_natDegree_le d 0 p (by simpa using hp)
  rw [eq_C_of_natDegree_le_zero hd, iteratedPolynomialForwardDifference_coeff_zero d p hp]

theorem iteratedPolynomialForwardDifference_eq_zero (d : ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ d) : iteratedPolynomialForwardDifference (d + 1) p = 0 := by
  induction d generalizing p with
  | zero =>
    change polynomialForwardDifference p = 0
    exact polynomialForwardDifference_eq_zero_of_natDegree_le_zero p hp
  | succ d ih =>
    change iteratedPolynomialForwardDifference (d + 1) (polynomialForwardDifference p) = 0
    exact ih _ (polynomialForwardDifference_natDegree_le p d hp)

#check @polynomialForwardDifference_eval
#print axioms polynomialForwardDifference_eval
#check @polynomialForwardDifference_natDegree_le
#print axioms polynomialForwardDifference_natDegree_le
#check @polynomialForwardDifference_coeff
#print axioms polynomialForwardDifference_coeff
#check @polynomialForwardDifference_eq_zero_of_natDegree_le_zero
#print axioms polynomialForwardDifference_eq_zero_of_natDegree_le_zero
#check @iteratedPolynomialForwardDifference_natDegree_le
#print axioms iteratedPolynomialForwardDifference_natDegree_le
#check @iteratedPolynomialForwardDifference_eq_C_factorial_mul_coeff
#print axioms iteratedPolynomialForwardDifference_eq_C_factorial_mul_coeff
#check @iteratedPolynomialForwardDifference_eq_zero
#print axioms iteratedPolynomialForwardDifference_eq_zero
end EnvelopeProperty.SeshadriAmplenessCriterion
