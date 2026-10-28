import BingWangEntropy.SchemeAnalyticManifold
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# The actual underlying real manifold of a smooth complex scheme

Restriction of scalars applies to the already derived analytic transitions.
The same genuine charts therefore give native real manifolds in every order,
with the expected real dimension of the actual tangent fibers.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold
open scoped Topology

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Every genuine complex chart transition has every real differentiability order. -/
theorem schemeAnalyticCoordinateTransition_real_contDiffOn
    (p q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    ContDiffOn ℝ k (schemeAnalyticCoordinateTransition f n p q)
      (schemeAnalyticCoordinateTransition f n p q).source := by
  let := schemeAnalyticPointTopology f
  exact (schemeAnalyticCoordinateTransition_contDiffOn f n p q k).restrict_scalars ℝ

/-- Actual forward and inverse transitions lie in the native real groupoid. -/
theorem schemeAnalyticCoordinateTransition_mem_real_contDiffGroupoid
    (p q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    schemeAnalyticCoordinateTransition f n p q ∈
      contDiffGroupoid k 𝓘(ℝ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology f
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      schemeAnalyticCoordinateTransition_real_contDiffOn f n p q k
  · have h := schemeAnalyticCoordinateTransition_real_contDiffOn f n q p k
    have ht : (schemeAnalyticCoordinateTransition f n p q).target =
        (schemeAnalyticCoordinateTransition f n q p).source :=
      congrArg (fun e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) => e.source)
        (schemeAnalyticCoordinateTransition_symm f n p q)
    simpa only [contDiffPregroupoid, mfld_simps, schemeAnalyticCoordinateTransition_symm, ht] using h

/-- The actual scheme-derived charts satisfy the real compatibility condition. -/
theorem smoothSchemeReal_hasGroupoid (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    HasGroupoid (SchemeComplexPoint f) (contDiffGroupoid k 𝓘(ℝ, Fin n → ℂ)) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  constructor
  intro e e' he he'
  change e ∈ Set.range (schemeAnalyticCoordinateChart f n) at he
  change e' ∈ Set.range (schemeAnalyticCoordinateChart f n) at he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  exact schemeAnalyticCoordinateTransition_mem_real_contDiffGroupoid f n p q k

/-- The actual analytic points of a smooth complex scheme form a native real manifold. -/
theorem smoothSchemeReal_isManifold (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    IsManifold 𝓘(ℝ, Fin n → ℂ) k (SchemeComplexPoint f) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_hasGroupoid f n k
  exact IsManifold.mk' 𝓘(ℝ, Fin n → ℂ) k (SchemeComplexPoint f)

/-- The genuine complex coordinate model has real dimension twice its complex dimension. -/
theorem smoothSchemeReal_model_finrank : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [finrank_real_of_complex]
  simp

/-- Actual real tangent fibers have the expected dimension. -/
theorem smoothSchemeReal_tangent_finrank (x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) x) = 2 * n := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  change Module.finrank ℝ (Fin n → ℂ) = 2 * n
  exact smoothSchemeReal_model_finrank n

end

end BingWangEntropy
