import BingWangEntropy.SchemeRealManifold
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Complex-linear differentials of genuine scheme coordinate changes

Multiplication by `Complex.I` is a real continuous linear endomorphism
squaring to minus the identity. The derivatives of the actual analytic
scheme transitions commute with it, as proved from complex analyticity.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold
open scoped Topology

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual multiplication by the imaginary unit on the genuine coordinate model. -/
def smoothComplexModelJ (n : ℕ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  (Complex.I • ContinuousLinearMap.id ℂ (Fin n → ℂ)).restrictScalars ℝ

/-- The actual real endomorphism acts by complex multiplication by `I`. -/
theorem smoothComplexModelJ_apply (n : ℕ) (v : Fin n → ℂ) :
    smoothComplexModelJ n v = Complex.I • v := rfl

/-- Its genuine square is minus the identity on every vector. -/
theorem smoothComplexModelJ_square_apply (n : ℕ) (v : Fin n → ℂ) :
    smoothComplexModelJ n (smoothComplexModelJ n v) = -v := by
  simp [smoothComplexModelJ_apply, smul_smul, Complex.I_mul_I]

/-- The actual real continuous linear endomorphism squares to minus the identity. -/
theorem smoothComplexModelJ_square (n : ℕ) :
    (smoothComplexModelJ n).comp (smoothComplexModelJ n) =
      -ContinuousLinearMap.id ℝ (Fin n → ℂ) := by
  ext v
  exact congrFun (smoothComplexModelJ_square_apply n v) _

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual real derivative is the scalar restriction of the actual complex derivative. -/
theorem schemeAnalyticCoordinateTransition_real_fderiv (p q : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateTransition f n p q).source),
      fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) t =
        (fderiv ℂ (schemeAnalyticCoordinateTransition f n p q) t).restrictScalars ℝ := by
  let := schemeAnalyticPointTopology f
  intro t ht
  exact ((schemeAnalyticCoordinateTransition_analyticOnNhd f n p q t ht).differentiableAt).fderiv_restrictScalars ℝ

/-- Actual transition derivatives preserve multiplication by the imaginary unit. -/
theorem schemeAnalyticCoordinateTransition_fderiv_commutes_J
    (p q : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateTransition f n p q).source)
      (v : Fin n → ℂ),
      fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) t (smoothComplexModelJ n v) =
        smoothComplexModelJ n (fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) t v) := by
  let := schemeAnalyticPointTopology f
  intro t ht v
  rw [schemeAnalyticCoordinateTransition_real_fderiv f n p q t ht]
  change (fderiv ℂ (schemeAnalyticCoordinateTransition f n p q) t) (Complex.I • v) =
    Complex.I • (fderiv ℂ (schemeAnalyticCoordinateTransition f n p q) t) v
  exact map_smul _ _ _

end

end BingWangEntropy
