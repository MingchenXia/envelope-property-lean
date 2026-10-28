import BingWangEntropy.SchemeStandardSmoothCharts
import BingWangEntropy.StandardSmoothComplexCharts
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Actual analytic coordinates on genuine complex scheme points

Native smoothness supplies the genuine affine neighborhood and finite
submersive presentation. Its actual inverse-function chart is composed with
its actual scheme-point open chart and a complex-linear finite-index
transport. The resulting point-indexed charts construct the native charted
space; analytic compatibility on global overlaps is a separate producer.
-/

open CategoryTheory AlgebraicGeometry Algebra
open scoped Topology

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The genuine presentation dimension proof gives an actual complex-linear
homeomorphism to the uniform `n`-coordinate model. -/
def standardSmoothComplexModelEquiv (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    (Fin (standardSmoothComplexChartPresentation f n p).2.dimension → ℂ) ≃L[ℂ] (Fin n → ℂ) := by
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n ↦ ℂ)
    (finCongr (standardSmoothComplexChartPresentation_dimension f n p))

/-- The uniform model transport reads the actual old index corresponding
to the proved dimension equality. -/
theorem standardSmoothComplexModelEquiv_apply (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ∀ (t : Fin (standardSmoothComplexChartPresentation f n p).2.dimension → ℂ) (i : Fin n),
      standardSmoothComplexModelEquiv f n p t i =
        t ((finCongr (standardSmoothComplexChartPresentation_dimension f n p)).symm i) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro t i
  rfl

/-- The inverse uniform model transport reads the actual corresponding
new index, and is a genuine continuous complex-linear map. -/
theorem standardSmoothComplexModelEquiv_symm_apply (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ∀ (t : Fin n → ℂ) (i : Fin (standardSmoothComplexChartPresentation f n p).2.dimension),
      (standardSmoothComplexModelEquiv f n p).symm t i =
        t (finCongr (standardSmoothComplexChartPresentation_dimension f n p) i) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro t i
  rfl

/-- Actual affine open charts and actual submersive analytic charts produce
uniform dimension-`n` coordinates on the actual global scheme-point carrier. -/
def schemeAnalyticCoordinateChart (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    OpenPartialHomeomorph (SchemeComplexPoint f) (Fin n → ℂ) := by
  letI := schemeAnalyticPointTopology f
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact ((standardSmoothComplexPointOpenChart f n p).trans
    (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
      (standardSmoothComplexAlgebraPoint f n p))).trans
        (standardSmoothComplexModelEquiv f n p).toHomeomorph.toOpenPartialHomeomorph

/-- Its source is the actual affine source intersected with the actual
inverse-function source; the uniform linear transport imposes no extra domain. -/
theorem schemeAnalyticCoordinateChart_source (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    (schemeAnalyticCoordinateChart f n p).source =
      (standardSmoothComplexPointOpenChart f n p).source ∩
        (standardSmoothComplexPointOpenChart f n p) ⁻¹'
          (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
            (standardSmoothComplexAlgebraPoint f n p)).source := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  simp only [schemeAnalyticCoordinateChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

/-- Every actual original scheme point belongs to the genuine source of
its produced uniform analytic coordinate chart. -/
theorem schemeAnalyticCoordinateChart_point_mem_source (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    p ∈ (schemeAnalyticCoordinateChart f n p).source := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  rw [schemeAnalyticCoordinateChart_source]
  refine ⟨standardSmoothComplexPointOpenChart_point_mem_source f n p, ?_⟩
  change standardSmoothComplexPointOpenChart f n p p ∈
    (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
      (standardSmoothComplexAlgebraPoint f n p)).source
  rw [standardSmoothComplexPointOpenChart_point]
  exact submersiveAnalyticComplexPointChart_point_mem_source _ _

/-- The actual uniform coordinate source lies in the genuine affine
scheme open immersion, enabling principal refinement of global overlaps. -/
theorem schemeAnalyticCoordinateChart_source_subset_affine (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    (schemeAnalyticCoordinateChart f n p).source ⊆
      {q | schemeComplexPointImage f q ∈ Set.range (standardSmoothComplexAffineChart f n p).val.map} := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro q hq
  have hsource := Eq.mp (congrArg (fun S : Set (SchemeComplexPoint f) ↦ q ∈ S)
    (schemeAnalyticCoordinateChart_source f n p)) hq
  exact Eq.mp (congrArg (fun S : Set (SchemeComplexPoint f) ↦ q ∈ S)
    (standardSmoothComplexPointOpenChart_source f n p)) hsource.1


/-- On its genuine source the uniform chart reads literal evaluations
at the actual free generators of the actual affine coordinate ring. -/
theorem schemeAnalyticCoordinateChart_apply (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ (q : SchemeComplexPoint f) (_hq : q ∈ (schemeAnalyticCoordinateChart f n p).source)
      (i : Fin n),
      schemeAnalyticCoordinateChart f n p q i =
        standardSmoothComplexPointOpenChart f n p q
          (standardSmoothComplexChartFreeGenerator f n p i) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro q hq i
  have hsource := Eq.mp (congrArg (fun S : Set (SchemeComplexPoint f) ↦ q ∈ S)
    (schemeAnalyticCoordinateChart_source f n p)) hq
  change standardSmoothComplexModelEquiv f n p
    (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
      (standardSmoothComplexAlgebraPoint f n p) (standardSmoothComplexPointOpenChart f n p q)) i = _
  rw [standardSmoothComplexModelEquiv_apply]
  exact submersiveAnalyticComplexPointChart_apply _ _ _ hsource.2 _

/-- The original point is sent to its actual vector of free-generator
evaluations; there is no coordinate-value assumption. -/
theorem schemeAnalyticCoordinateChart_point (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    schemeAnalyticCoordinateChart f n p p =
      standardSmoothComplexChartCoordinates f n p (standardSmoothComplexAlgebraPoint f n p) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  ext i
  rw [schemeAnalyticCoordinateChart_apply f n p p
    (schemeAnalyticCoordinateChart_point_mem_source f n p) i,
    standardSmoothComplexPointOpenChart_point]
  rfl

/-- The actual uniform target is exactly the inverse linear-model preimage
of the actual shrunk analytic inverse-function target. -/
theorem schemeAnalyticCoordinateChart_target (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    (schemeAnalyticCoordinateChart f n p).target =
      (standardSmoothComplexModelEquiv f n p).symm ⁻¹'
        (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
          (standardSmoothComplexAlgebraPoint f n p)).target := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  simp only [schemeAnalyticCoordinateChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    standardSmoothComplexPointOpenChart_target, Set.preimage_univ, Set.inter_univ,
    Set.univ_inter]
  rfl

/-- The raw inverse coordinate point is the literal actual algebra evaluation
point from the genuine submersive chart, after inverse complex-linear transport. -/
def schemeAnalyticCoordinateChartInverseAlgebraPoint (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    (Fin n → ℂ) → ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring :=
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  fun t ↦ (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
    (standardSmoothComplexAlgebraPoint f n p)).symm
      ((standardSmoothComplexModelEquiv f n p).symm t)

/-- The inverse global coordinate chart applies the actual affine scheme
open chart inverse to precisely that literal inverse algebra point. -/
theorem schemeAnalyticCoordinateChart_symm (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ t : Fin n → ℂ,
      (schemeAnalyticCoordinateChart f n p).symm t =
        (standardSmoothComplexPointOpenChart f n p).symm
          (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro t
  rfl

/-- The actual inverse is literally the Spec map of its actual algebra
evaluation, followed by the actual chosen affine open immersion. -/
theorem schemeAnalyticCoordinateChart_symm_val (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ t : Fin n → ℂ,
      ((schemeAnalyticCoordinateChart f n p).symm t).val =
        Spec.map (CommRingCat.ofHom
          (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t).toRingHom) ≫
            (standardSmoothComplexAffineChart f n p).val.map := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro t
  rw [schemeAnalyticCoordinateChart_symm]
  exact standardSmoothComplexPointOpenChart_symm_val f n p _

/-- The actual inverse algebra point maps to the literal actual global
scheme point defined by the inverse uniform coordinate chart. -/
theorem schemeAnalyticCoordinateChart_inverseAlgebraPoint_map (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ t : Fin n → ℂ,
      complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val
        (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t) =
          (schemeAnalyticCoordinateChart f n p).symm t := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro t
  rw [schemeAnalyticCoordinateChart_symm, standardSmoothComplexPointOpenChart_symm]

/-- Every genuine uniform-source point is the Spec of its actual lifted
affine evaluation followed by the literal chosen affine open immersion. -/
theorem schemeAnalyticCoordinateChart_source_point_fac (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ (q : SchemeComplexPoint f) (_hq : q ∈ (schemeAnalyticCoordinateChart f n p).source),
      Spec.map (CommRingCat.ofHom (standardSmoothComplexPointOpenChart f n p q).toRingHom) ≫
        (standardSmoothComplexAffineChart f n p).val.map = q.val := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro q hq
  have hsource := Eq.mp (congrArg (fun S : Set (SchemeComplexPoint f) ↦ q ∈ S)
    (schemeAnalyticCoordinateChart_source f n p)) hq
  exact (standardSmoothComplexPointOpenChart_symm_val f n p _).symm.trans
    (congrArg Subtype.val ((standardSmoothComplexPointOpenChart f n p).left_inv hsource.1))

/-- Every actual regular function of the actual affine chart evaluates
analytically on the inverse throughout the entire actual uniform target. -/
theorem schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ a : (standardSmoothComplexAffineChart f n p).val.ring,
      AnalyticOnNhd ℂ (fun t ↦ schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t a)
        (schemeAnalyticCoordinateChart f n p).target := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro a t ht
  have ht' := Eq.mp (congrArg (fun S : Set (Fin n → ℂ) ↦ t ∈ S)
    (schemeAnalyticCoordinateChart_target f n p)) ht
  exact (submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd
    (standardSmoothComplexChartPresentation f n p).2 (standardSmoothComplexAlgebraPoint f n p) a
      _ ht').comp ((standardSmoothComplexModelEquiv f n p).symm.toContinuousLinearMap.analyticAt t)

/-- The inverse algebra point is explicitly the actual submersive analytic
inverse evaluated at the inverse uniform complex-linear coordinates. -/
theorem schemeAnalyticCoordinateChartInverseAlgebraPoint_eq (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ∀ t : Fin n → ℂ,
      schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t =
        (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
          (standardSmoothComplexAlgebraPoint f n p)).symm
            ((standardSmoothComplexModelEquiv f n p).symm t) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro t
  rfl

/-- Inverse evaluation of the actual coordinate vector of a genuine source
point recovers its actual affine algebra point. -/
theorem schemeAnalyticCoordinateChartInverseAlgebraPoint_apply (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ (q : SchemeComplexPoint f) (_hq : q ∈ (schemeAnalyticCoordinateChart f n p).source),
      schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
        (schemeAnalyticCoordinateChart f n p q) = standardSmoothComplexPointOpenChart f n p q := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro q hq
  have hsource := Eq.mp (congrArg (fun S : Set (SchemeComplexPoint f) ↦ q ∈ S)
    (schemeAnalyticCoordinateChart_source f n p)) hq
  change (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
    (standardSmoothComplexAlgebraPoint f n p)).symm
      ((standardSmoothComplexModelEquiv f n p).symm
        (standardSmoothComplexModelEquiv f n p
          (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
            (standardSmoothComplexAlgebraPoint f n p) (standardSmoothComplexPointOpenChart f n p q)))) = _
  rw [(standardSmoothComplexModelEquiv f n p).symm_apply_apply]
  exact (submersiveAnalyticComplexPointChart (standardSmoothComplexChartPresentation f n p).2
    (standardSmoothComplexAlgebraPoint f n p)).left_inv hsource.2

/-- On the entire actual uniform target the inverse point evaluates each
actual chosen free generator to the corresponding original coordinate. -/
theorem schemeAnalyticCoordinateChart_inverse_freeGenerator (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateChart f n p).target) (i : Fin n),
      schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t
        (standardSmoothComplexChartFreeGenerator f n p i) = t i := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro t ht i
  have hsource := (schemeAnalyticCoordinateChart f n p).mapsTo_symm ht
  have hpoint := schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f n p
    ((schemeAnalyticCoordinateChart f n p).symm t) hsource
  rw [(schemeAnalyticCoordinateChart f n p).right_inv ht] at hpoint
  rw [hpoint]
  have hforward := schemeAnalyticCoordinateChart_apply f n p
    ((schemeAnalyticCoordinateChart f n p).symm t) hsource i
  rw [(schemeAnalyticCoordinateChart f n p).right_inv ht] at hforward
  exact hforward.symm

/-- Genuine smooth scheme points with their actual analytic topology carry
the native charted-space structure, produced from the derived point-indexed
uniform analytic charts. No atlas is supplied as an input. -/
@[instance_reducible] def smoothSchemeComplexChartedSpace (n : ℕ) [SmoothOfRelativeDimension n f] :
    letI := schemeAnalyticPointTopology f
    ChartedSpace (Fin n → ℂ) (SchemeComplexPoint f) := by
  letI := schemeAnalyticPointTopology f
  exact {
    atlas := Set.range (schemeAnalyticCoordinateChart f n)
    chartAt := schemeAnalyticCoordinateChart f n
    mem_chart_source := schemeAnalyticCoordinateChart_point_mem_source f n
    chart_mem_atlas := fun p ↦ ⟨p, rfl⟩ }

/-- The native atlas consists of precisely the produced actual point-indexed
charts of genuine smooth complex scheme points. -/
theorem smoothSchemeComplexChartedSpace_atlas (n : ℕ) [SmoothOfRelativeDimension n f] :
    letI := schemeAnalyticPointTopology f
    (smoothSchemeComplexChartedSpace f n).atlas =
      Set.range (schemeAnalyticCoordinateChart f n) := by
  let := schemeAnalyticPointTopology f
  rfl

/-- The native chart at any actual scheme point is its produced genuine
uniform coordinate chart. -/
theorem smoothSchemeComplexChartedSpace_chartAt (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    (smoothSchemeComplexChartedSpace f n).chartAt p = schemeAnalyticCoordinateChart f n p := by
  let := schemeAnalyticPointTopology f
  rfl

/-- The genuine point-indexed sources cover the entire actual scheme-point
carrier, by each point's derived source-membership theorem. -/
theorem schemeAnalyticCoordinateChart_sources_cover (n : ℕ) [SmoothOfRelativeDimension n f] :
    letI := schemeAnalyticPointTopology f
    (⋃ p : SchemeComplexPoint f, (schemeAnalyticCoordinateChart f n p).source) = Set.univ := by
  let := schemeAnalyticPointTopology f
  apply Set.eq_univ_of_forall
  intro p
  exact Set.mem_iUnion.mpr ⟨p, schemeAnalyticCoordinateChart_point_mem_source f n p⟩

end
end BingWangEntropy
