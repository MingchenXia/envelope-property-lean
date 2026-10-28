import BingWangEntropy.SchemeAnalyticCoordinates
import BingWangEntropy.SchemeAnalyticOverlapAlgebra
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Genuine analytic compatibility of smooth complex scheme charts

Actual scheme chart overlaps admit genuine principal refinements. Evaluation
of each free generator on such a refinement is a true fraction of regular
functions from the other chart, with a denominator nonzero at the actual
overlap point. This proves analytic compatibility of the derived charts.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold
open scoped Topology

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual affine scheme point corresponding to a uniform inverse algebra point. -/
def schemeAnalyticCoordinateAffineInversePoint (p : SchemeComplexPoint f) :
    (Fin n → ℂ) → ComplexAffineChartPoint f (standardSmoothComplexAffineChart f n p).val :=
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  fun t => (affineSchemePointHomeomorphOfStructure
    ((standardSmoothComplexAffineChart f n p).val.map ≫ f)).symm
      (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t)

/-- The actual affine point read by a genuine uniform source chart. -/
def schemeAnalyticCoordinateAffineSourcePoint (p : SchemeComplexPoint f) :
    SchemeComplexPoint f → ComplexAffineChartPoint f (standardSmoothComplexAffineChart f n p).val :=
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  fun z => (affineSchemePointHomeomorphOfStructure
    ((standardSmoothComplexAffineChart f n p).val.map ≫ f)).symm
      (standardSmoothComplexPointOpenChart f n p z)

/-- The actual inverse affine point represents exactly the actual global chart inverse. -/
theorem schemeAnalyticCoordinateAffineInversePoint_map (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    ∀ t : Fin n → ℂ,
      complexAffineChartPointMap f (standardSmoothComplexAffineChart f n p).val
        (schemeAnalyticCoordinateAffineInversePoint f n p t) =
          (schemeAnalyticCoordinateChart f n p).symm t := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro t
  exact schemeAnalyticCoordinateChart_inverseAlgebraPoint_map f n p t

/-- On the actual source, the actual affine lift represents the same global point. -/
theorem schemeAnalyticCoordinateAffineSourcePoint_map (p : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    ∀ (z : SchemeComplexPoint f) (_hz : z ∈ (schemeAnalyticCoordinateChart f n p).source),
      complexAffineChartPointMap f (standardSmoothComplexAffineChart f n p).val
        (schemeAnalyticCoordinateAffineSourcePoint f n p z) = z := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro z hz
  apply Subtype.ext
  exact (complexAffineAlgebraPointMap_val f (standardSmoothComplexAffineChart f n p).val
    (standardSmoothComplexPointOpenChart f n p z)).trans
      (schemeAnalyticCoordinateChart_source_point_fac f n p z hz)

/-- The native actual coordinate change on its genuine source and target. -/
def schemeAnalyticCoordinateTransition (p q : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) :=
  letI := schemeAnalyticPointTopology f
  (schemeAnalyticCoordinateChart f n p).symm.trans (schemeAnalyticCoordinateChart f n q)

/-- Each true coordinate-change germ is an actual regular-function fraction
with a denominator nonzero at the actual overlap point. -/
theorem schemeAnalyticCoordinateTransition_fractionGerm (p q : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateTransition f n p q).source)
      (i : Fin n),
      ∃ r : (standardSmoothComplexAffineChart f n p).val.ring,
      ∃ k : ℕ, ∃ b : (standardSmoothComplexAffineChart f n p).val.ring,
        schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t r ≠ 0 ∧
        (fun u => schemeAnalyticCoordinateTransition f n p q u i) =ᶠ[𝓝 t]
          (fun u => schemeAnalyticCoordinateChartInverseAlgebraPoint f n p u b /
            schemeAnalyticCoordinateChartInverseAlgebraPoint f n p u r ^ k) := by
  let := schemeAnalyticPointTopology f
  let c := (standardSmoothComplexAffineChart f n q).val
  let d := (standardSmoothComplexAffineChart f n p).val
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  intro t ht i
  change t ∈ (schemeAnalyticCoordinateChart f n p).target ∧
    (schemeAnalyticCoordinateChart f n p).symm t ∈ (schemeAnalyticCoordinateChart f n q).source at ht
  let x := schemeAnalyticCoordinateAffineSourcePoint f n q
    ((schemeAnalyticCoordinateChart f n p).symm t)
  let y := schemeAnalyticCoordinateAffineInversePoint f n p t
  have hxy : complexAffineChartPointMap f d y = complexAffineChartPointMap f c x :=
    (schemeAnalyticCoordinateAffineInversePoint_map f n p t).trans
      (schemeAnalyticCoordinateAffineSourcePoint_map f n q _ ht.2).symm
  obtain ⟨r, hr, z, _, _, hden⟩ := exists_complexAffine_common_overlap_point f c d x y hxy
  let a : c.ring := standardSmoothComplexChartFreeGenerator f n q i
  obtain ⟨k, b, hab⟩ := complexAffine_overlap_ringMap_fraction c d r hr a
  have hnz : schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t r ≠ 0 := by
    simpa [d, y, schemeAnalyticCoordinateAffineInversePoint] using hden
  refine ⟨r, k, b, hnz, ?_⟩
  have hsource : ∀ᶠ u in 𝓝 t, (schemeAnalyticCoordinateChart f n p).symm u ∈
      (schemeAnalyticCoordinateChart f n q).source :=
    Filter.Tendsto.eventually ((schemeAnalyticCoordinateChart f n p).continuousAt_symm ht.1)
      ((schemeAnalyticCoordinateChart f n q).open_source.mem_nhds ht.2)
  have hU : IsOpen {v : ℂ | v ≠ 0} := isClosed_singleton.isOpen_compl
  have hnonzero : ∀ᶠ u in 𝓝 t,
      schemeAnalyticCoordinateChartInverseAlgebraPoint f n p u r ≠ 0 :=
    Filter.Tendsto.eventually (p := fun v : ℂ => v ≠ 0)
      (schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p r t ht.1).continuousAt
      (hU.mem_nhds hnz)
  filter_upwards [hsource, hnonzero] with u hu hru
  let xu := schemeAnalyticCoordinateAffineSourcePoint f n q
    ((schemeAnalyticCoordinateChart f n p).symm u)
  let yu := schemeAnalyticCoordinateAffineInversePoint f n p u
  have hxyu : complexAffineChartPointMap f d yu = complexAffineChartPointMap f c xu :=
    (schemeAnalyticCoordinateAffineInversePoint_map f n p u).trans
      (schemeAnalyticCoordinateAffineSourcePoint_map f n q _ hu).symm
  have hdu : affineSchemePointHomeomorphOfStructure (d.map ≫ f) yu r ≠ 0 := by
    simpa [d, yu, schemeAnalyticCoordinateAffineInversePoint] using hru
  have hfrac := complexAffine_common_overlap_eval_fraction f c d r hr xu yu hxyu hdu a k b hab
  calc
    schemeAnalyticCoordinateTransition f n p q u i =
        standardSmoothComplexPointOpenChart f n q
          ((schemeAnalyticCoordinateChart f n p).symm u) a :=
      schemeAnalyticCoordinateChart_apply f n q _ hu i
    _ = affineSchemePointHomeomorphOfStructure (c.map ≫ f) xu a := by
      simp [c, xu, schemeAnalyticCoordinateAffineSourcePoint]
    _ = affineSchemePointHomeomorphOfStructure (d.map ≫ f) yu b /
        affineSchemePointHomeomorphOfStructure (d.map ≫ f) yu r ^ k := hfrac
    _ = _ := by simp [d, yu, schemeAnalyticCoordinateAffineInversePoint]

/-- Genuine regular fraction germs prove global analytic compatibility throughout the actual overlap. -/
theorem schemeAnalyticCoordinateTransition_analyticOnNhd (p q : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    AnalyticOnNhd ℂ (schemeAnalyticCoordinateTransition f n p q)
      (schemeAnalyticCoordinateTransition f n p q).source := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  intro t ht
  apply AnalyticAt.pi
  intro i
  obtain ⟨r, k, b, hnz, hfrac⟩ := schemeAnalyticCoordinateTransition_fractionGerm f n p q t ht i
  have hp : t ∈ (schemeAnalyticCoordinateChart f n p).target := ht.1
  have hb := schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p b t hp
  have hr := schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p r t hp
  exact (hb.div (hr.pow k) (pow_ne_zero k hnz)).congr hfrac.symm

/-- Actual global chart transitions have every differentiability order on their actual open source. -/
theorem schemeAnalyticCoordinateTransition_contDiffOn (p q : SchemeComplexPoint f)
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    ContDiffOn ℂ k (schemeAnalyticCoordinateTransition f n p q)
      (schemeAnalyticCoordinateTransition f n p q).source := by
  let := schemeAnalyticPointTopology f
  exact (schemeAnalyticCoordinateTransition_analyticOnNhd f n p q).contDiffOn
    (schemeAnalyticCoordinateTransition f n p q).open_source.uniqueDiffOn

/-- The actual reverse global coordinate transition is the native inverse partial homeomorphism. -/
theorem schemeAnalyticCoordinateTransition_symm (p q : SchemeComplexPoint f) :
    letI := schemeAnalyticPointTopology f
    (schemeAnalyticCoordinateTransition f n p q).symm =
      schemeAnalyticCoordinateTransition f n q p := by
  let := schemeAnalyticPointTopology f
  rfl

/-- Genuine analytic compatibility places the actual transition in the native differentiable groupoid. -/
theorem schemeAnalyticCoordinateTransition_mem_contDiffGroupoid
    (p q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    schemeAnalyticCoordinateTransition f n p q ∈
      contDiffGroupoid k 𝓘(ℂ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology f
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      schemeAnalyticCoordinateTransition_contDiffOn f n p q k
  · have h := schemeAnalyticCoordinateTransition_contDiffOn f n q p k
    have ht : (schemeAnalyticCoordinateTransition f n p q).target =
        (schemeAnalyticCoordinateTransition f n q p).source :=
      congrArg (fun e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) => e.source)
        (schemeAnalyticCoordinateTransition_symm f n p q)
    simpa only [contDiffPregroupoid, mfld_simps, schemeAnalyticCoordinateTransition_symm, ht] using h

/-- The atlas produced by native scheme smoothness satisfies actual compatibility in every order. -/
theorem smoothSchemeComplex_hasGroupoid (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    HasGroupoid (SchemeComplexPoint f) (contDiffGroupoid k 𝓘(ℂ, Fin n → ℂ)) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  constructor
  intro e e' he he'
  change e ∈ Set.range (schemeAnalyticCoordinateChart f n) at he
  change e' ∈ Set.range (schemeAnalyticCoordinateChart f n) at he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  exact schemeAnalyticCoordinateTransition_mem_contDiffGroupoid f n p q k

/-- Actual smooth complex schemes are native manifolds in their actual analytic point topology. -/
theorem smoothSchemeComplex_isManifold (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    IsManifold 𝓘(ℂ, Fin n → ℂ) k (SchemeComplexPoint f) := by
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  let := smoothSchemeComplex_hasGroupoid f n k
  exact IsManifold.mk' 𝓘(ℂ, Fin n → ℂ) k (SchemeComplexPoint f)

end

end BingWangEntropy
