import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Instances.Rat

/-! Rational derivative tests control all real parameters of the genuine
intersection pencil. The geometric derivative identities are separate inputs
constructed in the intersection-polynomial module. -/

open Set Polynomial

namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmple

/-- Continuity of the original derivative polynomial extends its
nonnegative rational tests to every positive real parameter. -/
theorem polynomial_derivative_nonneg_of_positive_rational_tests
    (g : Polynomial ℝ)
    (hrat : ∀ q : ℚ, 0 < q → 0 ≤ g.derivative.eval (q : ℝ))
    {t : ℝ} (ht : 0 < t) : 0 ≤ g.derivative.eval t := by
  by_contra hn
  have hneg : g.derivative.eval t < 0 := lt_of_not_ge hn
  let U : Set ℝ := Ioi 0 ∩ {x | g.derivative.eval x < 0}
  have hU : IsOpen U := isOpen_Ioi.inter
    (isOpen_lt g.derivative.differentiable.continuous continuous_const)
  obtain ⟨q, hq⟩ :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_mem_open hU
      (show U.Nonempty from ⟨t, ht, hneg⟩)
  have hqpos : (0 : ℝ) < q := hq.1
  exact (not_lt_of_ge (hrat q (by exact_mod_cast hqpos))) hq.2

/-- Actual positive rational values and nonnegative rational derivative
values force strict positivity at every positive real pencil parameter. -/
theorem polynomial_pos_of_positive_rational_tests_and_derivative_nonneg
    (g : Polynomial ℝ)
    (hpos : ∀ q : ℚ, 0 < q → 0 < g.eval (q : ℝ))
    (hderiv : ∀ q : ℚ, 0 < q → 0 ≤ g.derivative.eval (q : ℝ)) :
    ∀ t : ℝ, 0 < t → 0 < g.eval t := by
  have hmono : MonotoneOn (fun x : ℝ => g.eval x) (Ioi 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      g.differentiable.continuous.continuousOn g.differentiable.differentiableOn (by
        intro x hx
        rw [Polynomial.deriv]
        exact polynomial_derivative_nonneg_of_positive_rational_tests g hderiv
          (by simpa only [interior_Ioi, Set.mem_Ioi] using hx))
  intro t ht
  obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  exact lt_of_lt_of_le (hpos q hq) (hmono hq0 ht hqt.le)

end EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
