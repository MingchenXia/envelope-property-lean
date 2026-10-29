import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Seshadri Ampleness Criterion Polynomial Summation

Rational discrete polynomial integration for actual Euler differences. -/

noncomputable section
open Polynomial Finset
namespace EnvelopeProperty.SeshadriAmplenessCriterion

private def powerSumPolynomial (m : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (m + 1),
    C (bernoulli i * ((m + 1).choose i : ℚ) / (m + 1)) * X ^ (m + 1 - i)

private theorem powerSumPolynomial_eval (m n : ℕ) :
    (powerSumPolynomial m).eval (n : ℚ) = ∑ j ∈ Finset.range n, (j : ℚ) ^ m := by
  rw [sum_range_pow]
  simp only [powerSumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem powerSumPolynomial_natDegree (m : ℕ) :
    (powerSumPolynomial m).natDegree ≤ m + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)

/-- The actual rational polynomial for every finite partial sum of the
original rational polynomial, with the original natural argument. -/
def partialSumPolynomial (q : ℚ[X]) : ℚ[X] :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * powerSumPolynomial i

theorem partialSumPolynomial_eval (q : ℚ[X]) (n : ℕ) :
    (partialSumPolynomial q).eval (n : ℚ) = ∑ j ∈ Finset.range n, q.eval (j : ℚ) := by
  simp only [partialSumPolynomial, eval_finsetSum, eval_mul, eval_C]
  simp_rw [powerSumPolynomial_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (eval_eq_sum_range (p := q) (j : ℚ)).symm

theorem partialSumPolynomial_natDegree (q : ℚ[X]) :
    (partialSumPolynomial q).natDegree ≤ q.natDegree + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i < q.natDegree + 1 := Finset.mem_range.mp hi
  exact (natDegree_C_mul_le _ _).trans ((powerSumPolynomial_natDegree i).trans (by omega))

/-- An actual polynomial finite difference determines a polynomial for the
same original sequence at every natural number, including its initial value. -/
theorem exists_polynomial_of_polynomial_difference
    (f : ℕ → ℚ) (q : ℚ[X]) (d : ℕ) (hq : q.natDegree ≤ d)
    (h : ∀ n : ℕ, f (n + 1) - f n = q.eval (n : ℚ)) :
    ∃ p : ℚ[X], p.natDegree ≤ d + 1 ∧ ∀ n : ℕ, p.eval (n : ℚ) = f n := by
  refine ⟨C (f 0) + partialSumPolynomial q, ?_, ?_⟩
  · exact natDegree_add_le_of_degree_le (by simp)
      ((partialSumPolynomial_natDegree q).trans (by omega))
  · intro n
    simp only [eval_add, eval_C, partialSumPolynomial_eval]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn := h n
      linarith

#check @partialSumPolynomial_eval
#print axioms partialSumPolynomial_eval
#check @partialSumPolynomial_natDegree
#print axioms partialSumPolynomial_natDegree
#check @exists_polynomial_of_polynomial_difference
#print axioms exists_polynomial_of_polynomial_difference
end EnvelopeProperty.SeshadriAmplenessCriterion
