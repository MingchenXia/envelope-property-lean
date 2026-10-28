import SGPT.Okounkov.SchemeAnalyticMorphismTopology
import SGPT.Okounkov.SchemeAnalyticTNManifold
import BingWangEntropy.NativeProjectiveAnalyticMorphismGerms
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# The same arbitrary smooth-scheme morphism in the native analytic atlases

Actual affine source refinements let the original morphism's coordinate
functions be read as literal regular pullbacks. Existing arbitrary-affine
coordinate evaluation analyticity then proves the same point map holomorphic.
Neither projectivity nor an externally supplied analytic map is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy Filter Manifold
open TranscendentalNakamaye.FirstPass
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]

local instance morphismSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance morphismTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

/-- The literal original point map in the existing source and target coordinates. -/
def schemeMorphismCoordinateMap (p : SchemeComplexPoint (h ≫ f)) (q : SchemeComplexPoint f) :
    (Fin n → ℂ) → (Fin m → ℂ) :=
  fun t => schemeAnalyticCoordinateChart f m q
    (schemeComplexPointMap (h ≫ f) f h rfl ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t))

/-- The genuine source-target domain of the same original coordinate expression. -/
def schemeMorphismCoordinateDomain (p : SchemeComplexPoint (h ≫ f)) (q : SchemeComplexPoint f) :
    Set (Fin n → ℂ) :=
  (schemeAnalyticCoordinateChart (h ≫ f) n p).target ∩
    (fun t => schemeComplexPointMap (h ≫ f) f h rfl
      ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t)) ⁻¹'
      (schemeAnalyticCoordinateChart f m q).source

private theorem schemeMorphismCoordinateDomain_eventually
    (p : SchemeComplexPoint (h ≫ f)) (q : SchemeComplexPoint f)
    (t : Fin n → ℂ) (ht : t ∈ schemeMorphismCoordinateDomain f h n m p q) :
    ∀ᶠ u in 𝓝 t, u ∈ schemeMorphismCoordinateDomain f h n m p q := by
  have hcont := (schemeComplexPointMap_continuous f h).continuousAt.comp
    ((schemeAnalyticCoordinateChart (h ≫ f) n p).continuousAt_symm ht.1)
  exact Filter.inter_mem ((schemeAnalyticCoordinateChart (h ≫ f) n p).open_target.mem_nhds ht.1)
    (Filter.Tendsto.eventually hcont ((schemeAnalyticCoordinateChart f m q).open_source.mem_nhds ht.2))

/-- Openness is derived on genuine chart targets, without totalized-inverse continuity. -/
theorem schemeMorphismCoordinateDomain_isOpen
    (p : SchemeComplexPoint (h ≫ f)) (q : SchemeComplexPoint f) :
    IsOpen (schemeMorphismCoordinateDomain f h n m p q) :=
  isOpen_iff_mem_nhds.mpr fun t ht => schemeMorphismCoordinateDomain_eventually f h n m p q t ht

/-- Every original chart point belongs to the domain centered at it and its literal image. -/
theorem schemeMorphismCoordinateDomain_point_mem (p : SchemeComplexPoint (h ≫ f)) :
    schemeAnalyticCoordinateChart (h ≫ f) n p p ∈
      schemeMorphismCoordinateDomain f h n m p (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  have hp := schemeAnalyticCoordinateChart_point_mem_source (h ≫ f) n p
  refine ⟨(schemeAnalyticCoordinateChart (h ≫ f) n p).map_source hp, ?_⟩
  change schemeComplexPointMap (h ≫ f) f h rfl
    ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm
      (schemeAnalyticCoordinateChart (h ≫ f) n p p)) ∈
        (schemeAnalyticCoordinateChart f m (schemeComplexPointMap (h ≫ f) f h rfl p)).source
  rw [(schemeAnalyticCoordinateChart (h ≫ f) n p).left_inv hp]
  exact schemeAnalyticCoordinateChart_point_mem_source f m _

/-- The same original arbitrary scheme morphism has analytic actual coordinate expressions. -/
theorem schemeMorphismCoordinateMap_analyticOnNhd
    (p : SchemeComplexPoint (h ≫ f)) (q : SchemeComplexPoint f) :
    AnalyticOnNhd ℂ (schemeMorphismCoordinateMap f h n m p q)
      (schemeMorphismCoordinateDomain f h n m p q) := by
  intro t ht
  let d := (standardSmoothComplexAffineChart f m q).val
  let y := schemeAnalyticCoordinateAffineSourcePoint f m q
    (schemeComplexPointMap (h ≫ f) f h rfl ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t))
  have hy : complexAffineChartPointMap f d y =
      schemeComplexPointMap (h ≫ f) f h rfl
        ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t) :=
    schemeAnalyticCoordinateAffineSourcePoint_map f m q _ ht.2
  have hgeo : h (schemeComplexPointImage (h ≫ f)
      ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t)) ∈ Set.range d.map := by
    refine ⟨y.val default, ?_⟩
    simpa only [complexAffineChartPointMap, schemeComplexPointMap, schemeComplexPointImage,
      Scheme.Hom.comp_apply] using congrArg (fun r : SchemeComplexPoint f => r.val default) hy
  obtain ⟨c, hc, l, hl⟩ := exists_schemeMorphism_affine_source f h d
    ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm t) hgeo
  have hrange : (schemeAnalyticCoordinateChart (h ≫ f) n p).symm t ∈
      Set.range (complexAffineChartPointMap (h ≫ f) c) := by
    rw [complexAffineChartPointMap_range]
    exact hc
  obtain ⟨z, hz⟩ := hrange
  let := affinePointFieldAlgebra (c.map ≫ (h ≫ f))
  let := affinePointFieldAlgebra (d.map ≫ f)
  have himage : ∀ᶠ u in 𝓝 t,
      schemeMorphismAffinePointMap f h c d l hl
          (nativeSchemeCoordinateAffineLift (h ≫ f) n p c z u) =
        schemeAnalyticCoordinateAffineSourcePoint f m q
          (schemeComplexPointMap (h ≫ f) f h rfl
            ((schemeAnalyticCoordinateChart (h ≫ f) n p).symm u)) := by
    filter_upwards [schemeMorphismCoordinateDomain_eventually f h n m p q t ht,
      nativeSchemeCoordinateAffineLift_eventually_map (h ≫ f) n p c z t ht.1 hz] with u hu hsource
    apply complexAffineChartPointMap_injective f d
    exact (schemeMorphismAffinePointMap_fac f h c d l hl _).trans
      ((congrArg (schemeComplexPointMap (h ≫ f) f h rfl) hsource).trans
        (schemeAnalyticCoordinateAffineSourcePoint_map f m q _ hu.2).symm)
  apply AnalyticAt.pi
  intro j
  let a : d.ring := standardSmoothComplexChartFreeGenerator f m q j
  have ha := nativeSchemeCoordinateAffineLift_eval_analyticAt (h ≫ f) n p c z t ht.1 hz
    ((Spec.preimage l).hom a)
  apply ha.congr
  filter_upwards [schemeMorphismCoordinateDomain_eventually f h n m p q t ht, himage]
    with u hu hpoint
  rw [← schemeMorphismAffinePointMap_eval f h c d l hl, hpoint]
  simpa [d, schemeAnalyticCoordinateAffineSourcePoint, schemeMorphismCoordinateMap] using
    (schemeAnalyticCoordinateChart_apply f m q _ hu.2 j).symm

local instance morphismSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance morphismTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m

/-- Complex smoothness in every order for the SAME map and the SAME native TN atlases. -/
theorem schemeComplexPointMap_contMDiff (k : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) k
      (schemeComplexPointMap (h ≫ f) f h rfl) := by
  let : IsManifold 𝓘(ℂ, ComplexModel n) k (SchemeComplexPoint (h ≫ f)) :=
    schemeAnalyticTN_isManifold (h ≫ f) n k
  let : IsManifold 𝓘(ℂ, ComplexModel m) k (SchemeComplexPoint f) :=
    schemeAnalyticTN_isManifold f m k
  rw [contMDiff_iff]
  refine ⟨schemeComplexPointMap_continuous f h, ?_⟩
  intro p q
  have hSmooth : ContDiffOn ℂ k
      (fun z : ComplexModel n => (schemeCoordinateModelEquiv m).symm
        (schemeMorphismCoordinateMap f h n m p q (schemeCoordinateModelEquiv n z)))
      ((schemeCoordinateModelEquiv n) ⁻¹' schemeMorphismCoordinateDomain f h n m p q) := by
    intro z hz
    have hOld := schemeMorphismCoordinateMap_analyticOnNhd f h n m p q
      (schemeCoordinateModelEquiv n z) hz
    have hL : AnalyticAt ℂ (schemeCoordinateModelEquiv n) z :=
      (schemeCoordinateModelEquiv n).toContinuousLinearMap.analyticAt z
    have hInv : AnalyticAt ℂ (schemeCoordinateModelEquiv m).symm
        (schemeMorphismCoordinateMap f h n m p q (schemeCoordinateModelEquiv n z)) :=
      (schemeCoordinateModelEquiv m).symm.toContinuousLinearMap.analyticAt _
    have hComp := AnalyticAt.comp
      (f := (schemeCoordinateModelEquiv n : ComplexModel n → (Fin n → ℂ)))
      (g := schemeMorphismCoordinateMap f h n m p q) (x := z) hOld hL
    have hTot := AnalyticAt.comp
      (f := fun w : ComplexModel n =>
        schemeMorphismCoordinateMap f h n m p q (schemeCoordinateModelEquiv n w))
      (g := ((schemeCoordinateModelEquiv m).symm : (Fin m → ℂ) → ComplexModel m))
      (x := z) hInv hComp
    exact hTot.contDiffAt.contDiffWithinAt
  simp only [mfld_simps]
  change ContDiffOn ℂ k
    (fun x => schemeAnalyticTNChart f m q (schemeComplexPointMap (h ≫ f) f h rfl
      ((schemeAnalyticTNChart (h ≫ f) n p).symm x)))
    ((schemeAnalyticTNChart (h ≫ f) n p).target ∩
      (fun x => schemeComplexPointMap (h ≫ f) f h rfl
        ((schemeAnalyticTNChart (h ≫ f) n p).symm x)) ⁻¹'
        (schemeAnalyticTNChart f m q).source)
  simpa only [mfld_simps, schemeAnalyticTNChart,
    schemeMorphismCoordinateMap, schemeMorphismCoordinateDomain, Function.comp_def,
    Set.preimage, Set.ofPred_and, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm] using hSmooth

end SGPT.Okounkov
