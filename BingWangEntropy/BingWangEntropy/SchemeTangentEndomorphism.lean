import BingWangEntropy.SchemeTangentComplex
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smoothness of the genuine native tangent imaginary endomorphism

The actual real tangent imaginary operator has constant conjugated coordinates
in every genuine native tangent trivialization. It is therefore a genuine
smooth section of the native endomorphism bundle.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff Bundle

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual tangent Hom coordinates conjugate the imaginary operator to the literal constant model map. -/
theorem smoothSchemeTangentJ_inCoordinates (p x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    x ∈ (schemeAnalyticCoordinateChart f n p).source →
    ContinuousLinearMap.inCoordinates (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ))
      (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p x p x
        (smoothSchemeTangentJ f n x) = smoothComplexModelJ n := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n ∞
  intro hx
  let e := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
  have he : x ∈ e.baseSet := hx
  rw [ContinuousLinearMap.inCoordinates_eq he he]
  ext v : 1
  change (e.continuousLinearEquivAt ℝ x he)
    (smoothSchemeTangentJ f n x ((e.continuousLinearEquivAt ℝ x he).symm v)) =
      smoothComplexModelJ n v
  calc
    _ = smoothComplexModelJ n ((e.continuousLinearEquivAt ℝ x he)
        ((e.continuousLinearEquivAt ℝ x he).symm v)) :=
      smoothSchemeReal_tangent_trivialization_J f n p x hx _
    _ = _ := by rw [(e.continuousLinearEquivAt ℝ x he).apply_symm_apply]

/-- The actual imaginary fiber maps form a smooth section of the actual native real tangent Hom bundle. -/
theorem smoothSchemeTangentJ_hom_contMDiff :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    ContMDiff 𝓘(ℝ, Fin n → ℂ)
      (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))) ∞
        (fun x => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) x
          (smoothSchemeTangentJ f n x)) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n ∞
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_const.congr_of_eventuallyEq
  filter_upwards [(schemeAnalyticCoordinateChart f n p).open_source.mem_nhds
    (schemeAnalyticCoordinateChart_point_mem_source f n p)] with x hx
  exact smoothSchemeTangentJ_inCoordinates f n p x hx

end

end BingWangEntropy
