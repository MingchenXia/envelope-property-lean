import BingWangEntropy.SchemeComplexStructure
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Genuine tangent bundles and the native imaginary endomorphism

The derived scheme manifolds supply native smooth real and complex tangent
bundles. Their genuine chart changes are actual transition derivatives.
The imaginary action is compatible with these native tangent changes.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff Bundle

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The genuine complex tangent bundle of the actual derived scheme manifold is native smooth. -/
theorem smoothSchemeComplex_tangent_contMDiffVectorBundle :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n ∞
    ContMDiffVectorBundle ∞ (Fin n → ℂ)
      (TangentSpace 𝓘(ℂ, Fin n → ℂ) : SchemeComplexPoint f → Type _)
      𝓘(ℂ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n ∞
  infer_instance

/-- The genuine real tangent bundle of the same actual point manifold is native smooth. -/
theorem smoothSchemeReal_tangent_contMDiffVectorBundle :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    ContMDiffVectorBundle ∞ (Fin n → ℂ)
      (TangentSpace 𝓘(ℝ, Fin n → ℂ) : SchemeComplexPoint f → Type _)
      𝓘(ℝ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n ∞
  infer_instance

/-- The actual complex tangent fiber has the actual complex relative dimension. -/
theorem smoothSchemeComplex_tangent_finrank (x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    Module.finrank ℂ (TangentSpace 𝓘(ℂ, Fin n → ℂ) x) = n := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  change Module.finrank ℂ (Fin n → ℂ) = n
  simp

/-- A genuine produced coordinate chart is an actual native atlas index. -/
def smoothSchemeCoordinateAtlasIndex (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    atlas (Fin n → ℂ) (SchemeComplexPoint f) :=
  letI := schemeAnalyticPointTopology f
  letI := smoothSchemeComplexChartedSpace f n
  ⟨schemeAnalyticCoordinateChart f n p, Set.mem_range_self p⟩

/-- The literal native index contains exactly the actual produced chart. -/
theorem smoothSchemeCoordinateAtlasIndex_val (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    (smoothSchemeCoordinateAtlasIndex f n p).val = schemeAnalyticCoordinateChart f n p := rfl

/-- The actual native complex tangent change is the true complex derivative of the actual transition. -/
theorem smoothSchemeComplex_tangent_coordChange (p q x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n 1
    (tangentBundleCore 𝓘(ℂ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
      (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x =
        fderiv ℂ (schemeAnalyticCoordinateTransition f n p q)
          (schemeAnalyticCoordinateChart f n p x) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n 1
  simp only [tangentBundleCore_coordChange, mfld_simps, fderivWithin_univ]
  rfl

/-- The actual native real tangent change is the true real derivative of the same actual transition. -/
theorem smoothSchemeReal_tangent_coordChange (p q x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n 1
    (tangentBundleCore 𝓘(ℝ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
      (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x =
        fderiv ℝ (schemeAnalyticCoordinateTransition f n p q)
          (schemeAnalyticCoordinateChart f n p x) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n 1
  simp only [tangentBundleCore_coordChange, mfld_simps, fderivWithin_univ]
  rfl

/-- An actual base overlap point gives a true coordinate transition source point. -/
theorem smoothSchemeCoordinateTransition_mem_source (p q x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    x ∈ (schemeAnalyticCoordinateChart f n p).source ∩
      (schemeAnalyticCoordinateChart f n q).source →
    schemeAnalyticCoordinateChart f n p x ∈
      (schemeAnalyticCoordinateTransition f n p q).source := by
  let := schemeAnalyticPointTopology f
  intro hx
  constructor
  · exact (schemeAnalyticCoordinateChart f n p).map_source hx.1
  · change (schemeAnalyticCoordinateChart f n p).symm
      (schemeAnalyticCoordinateChart f n p x) ∈ (schemeAnalyticCoordinateChart f n q).source
    rw [(schemeAnalyticCoordinateChart f n p).left_inv hx.1]
    exact hx.2

/-- The actual native real tangent change is the restriction of the actual complex change on genuine overlaps. -/
theorem smoothScheme_tangent_coordChange_restrictScalars (p q x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n 1
    letI := smoothSchemeReal_isManifold f n 1
    x ∈ (schemeAnalyticCoordinateChart f n p).source ∩
      (schemeAnalyticCoordinateChart f n q).source →
    (tangentBundleCore 𝓘(ℝ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
      (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x =
        ((tangentBundleCore 𝓘(ℂ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
          (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x).restrictScalars ℝ := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n 1
  let := smoothSchemeReal_isManifold f n 1
  intro hx
  rw [smoothSchemeReal_tangent_coordChange, smoothSchemeComplex_tangent_coordChange]
  exact schemeAnalyticCoordinateTransition_real_fderiv f n p q _
    (smoothSchemeCoordinateTransition_mem_source f n p q x hx)

/-- The literal imaginary action on the actual native real tangent fiber. -/
def smoothSchemeTangentJ (x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℂ) x :=
  smoothComplexModelJ n

/-- Actual tangent multiplication by the imaginary unit squares to minus the identity. -/
theorem smoothSchemeTangentJ_square_apply (x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x,
      smoothSchemeTangentJ f n x (smoothSchemeTangentJ f n x v) = -v :=
  smoothComplexModelJ_square_apply n

/-- Actual native real tangent chart changes commute with the actual imaginary action on every genuine overlap. -/
theorem smoothSchemeReal_tangent_coordChange_commutes_J (p q x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n 1
    x ∈ (schemeAnalyticCoordinateChart f n p).source ∩
      (schemeAnalyticCoordinateChart f n q).source →
    ∀ v : Fin n → ℂ,
      (tangentBundleCore 𝓘(ℝ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
        (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x
          (smoothComplexModelJ n v) =
      smoothComplexModelJ n
        ((tangentBundleCore 𝓘(ℝ, Fin n → ℂ) (SchemeComplexPoint f)).coordChange
          (smoothSchemeCoordinateAtlasIndex f n p) (smoothSchemeCoordinateAtlasIndex f n q) x v) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n 1
  intro hx v
  rw [smoothSchemeReal_tangent_coordChange]
  exact schemeAnalyticCoordinateTransition_fderiv_commutes_J f n p q _
    (smoothSchemeCoordinateTransition_mem_source f n p q x hx) v

/-- The actual native complex tangent bundle preserves smooth sections under the imaginary action. -/
theorem smoothSchemeComplex_tangentJ_section_contMDiff :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n ∞
    ∀ (s : (x : SchemeComplexPoint f) → TangentSpace 𝓘(ℂ, Fin n → ℂ) x),
      ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) ∞
        (fun x => TotalSpace.mk' (Fin n → ℂ) x (s x)) →
      ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) ∞
        (fun x => TotalSpace.mk' (Fin n → ℂ) x (Complex.I • s x)) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n ∞
  intro s hs
  exact hs.const_smul_section

/-- Actual native real tangent trivializations preserve the imaginary action on their genuine source. -/
theorem smoothSchemeReal_tangent_trivialization_J (p x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    x ∈ (schemeAnalyticCoordinateChart f n p).source →
    ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x,
      (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
        (TotalSpace.mk' (Fin n → ℂ) x (smoothSchemeTangentJ f n x v))).2 =
      smoothComplexModelJ n
        (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
          (TotalSpace.mk' (Fin n → ℂ) x v)).2 := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n ∞
  intro hx v
  simp only [TangentBundle.trivializationAt_apply, mfld_simps, fderivWithin_univ]
  change fderiv ℝ (schemeAnalyticCoordinateTransition f n x p)
    (schemeAnalyticCoordinateChart f n x x) (smoothComplexModelJ n v) =
    smoothComplexModelJ n (fderiv ℝ (schemeAnalyticCoordinateTransition f n x p)
      (schemeAnalyticCoordinateChart f n x x) v)
  exact schemeAnalyticCoordinateTransition_fderiv_commutes_J f n x p _
    (smoothSchemeCoordinateTransition_mem_source f n x p x
      ⟨schemeAnalyticCoordinateChart_point_mem_source f n x, hx⟩) v

/-- Actual native real smooth tangent sections remain smooth under the genuine imaginary action. -/
theorem smoothSchemeReal_tangentJ_section_contMDiff :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    ∀ (s : (x : SchemeComplexPoint f) → TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, Fin n → ℂ)) ∞
        (fun x => TotalSpace.mk' (Fin n → ℂ) x (s x)) →
      ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, Fin n → ℂ)) ∞
        (fun x => TotalSpace.mk' (Fin n → ℂ) x (smoothSchemeTangentJ f n x (s x))) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeReal_isManifold f n ∞
  intro s hs p
  have hsp := hs p
  rw [contMDiffAt_section p] at hsp ⊢
  have hJ := (smoothComplexModelJ n).contMDiffAt.comp p hsp
  apply hJ.congr_of_eventuallyEq
  filter_upwards [(schemeAnalyticCoordinateChart f n p).open_source.mem_nhds
    (schemeAnalyticCoordinateChart_point_mem_source f n p)] with x hx
  exact smoothSchemeReal_tangent_trivialization_J f n p x hx (s x)

/-- Smooth actual coordinate-valued maps restrict from complex to real scalars. -/
theorem smoothScheme_coordinateMap_contMDiffAt_restrictScalars
    (g : SchemeComplexPoint f → (Fin n → ℂ)) (p : SchemeComplexPoint f) (k : ℕ∞ω) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) k g p →
      ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) k g p := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  intro hg
  rw [contMDiffAt_iff] at hg ⊢
  refine ⟨hg.1, ?_⟩
  simpa only [mfld_simps] using hg.2.restrict_scalars ℝ

/-- On actual sources the actual real and complex tangent trivializations have literally equal fiber coordinates. -/
theorem smoothScheme_tangent_trivialization_restrictScalars (p x : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n ∞
    letI := smoothSchemeReal_isManifold f n ∞
    x ∈ (schemeAnalyticCoordinateChart f n p).source →
    ∀ v : Fin n → ℂ,
      (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
        (TotalSpace.mk' (Fin n → ℂ) x v)).2 =
      (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℂ, Fin n → ℂ)) p
        (TotalSpace.mk' (Fin n → ℂ) x v)).2 := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n ∞
  let := smoothSchemeReal_isManifold f n ∞
  intro hx v
  simp only [TangentBundle.trivializationAt_apply, mfld_simps, fderivWithin_univ]
  change fderiv ℝ (schemeAnalyticCoordinateTransition f n x p)
    (schemeAnalyticCoordinateChart f n x x) v =
    fderiv ℂ (schemeAnalyticCoordinateTransition f n x p)
      (schemeAnalyticCoordinateChart f n x x) v
  rw [schemeAnalyticCoordinateTransition_real_fderiv f n x p _
    (smoothSchemeCoordinateTransition_mem_source f n x p x
      ⟨schemeAnalyticCoordinateChart_point_mem_source f n x, hx⟩)]
  rfl

/-- The very same actual complex smooth tangent section is smooth in the actual real tangent bundle. -/
theorem smoothScheme_tangentSection_contMDiff_restrictScalars :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeComplex_isManifold f n ∞
    letI := smoothSchemeReal_isManifold f n ∞
    ∀ (s : (x : SchemeComplexPoint f) → TangentSpace 𝓘(ℂ, Fin n → ℂ) x),
      ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) ∞
        (fun x => TotalSpace.mk' (Fin n → ℂ) x (s x)) →
      ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, Fin n → ℂ)) ∞
        (fun x => (⟨x, s x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℂ) (SchemeComplexPoint f))) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_isManifold f n ∞
  let := smoothSchemeReal_isManifold f n ∞
  intro s hs p
  have hsp := hs p
  rw [contMDiffAt_section p] at hsp ⊢
  have hr := smoothScheme_coordinateMap_contMDiffAt_restrictScalars f n _ p ∞ hsp
  apply hr.congr_of_eventuallyEq
  filter_upwards [(schemeAnalyticCoordinateChart f n p).open_source.mem_nhds
    (schemeAnalyticCoordinateChart_point_mem_source f n p)] with x hx
  exact smoothScheme_tangent_trivialization_restrictScalars f n p x hx (s x)

end

end BingWangEntropy
