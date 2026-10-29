import EnvelopeProperty.ComplexGeometry.Schemes.NativeProjectiveAnalyticPrincipalRefinement
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticManifold
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAffineEvaluationGerms

/-!
# Actual closed-immersion coordinate germs on native complex scheme points

The coordinate expression uses the literal SchemeComplexPoint map and the
already constructed uniform scheme charts. Actual principal-overlap fractions
prove its analyticity and produce a genuine ambient retraction germ.
-/

open Algebra CategoryTheory AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

/-- The genuine inverse affine open chart on actual scheme points, with an actual default point. -/
def nativeComplexAffinePointOpenChart {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) (z : ComplexAffineChartPoint f c) :
    let := schemeAnalyticPointTopology f
    OpenPartialHomeomorph (SchemeComplexPoint f) (ComplexAffineChartPoint f c) := by
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAffineChartPoint f c) := ⟨z⟩
  exact ((complexAffineChartPointMap_isOpenEmbedding f c).toOpenPartialHomeomorph
    (complexAffineChartPointMap f c)).symm

/-- Its true source is the actual affine chart point image. -/
theorem nativeComplexAffinePointOpenChart_source {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) (z : ComplexAffineChartPoint f c) :
    let := schemeAnalyticPointTopology f
    (nativeComplexAffinePointOpenChart f c z).source = Set.range (complexAffineChartPointMap f c) := by
  let := schemeAnalyticPointTopology f
  simp only [nativeComplexAffinePointOpenChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

/-- The inverse of the native inverse chart is literally the actual affine point map. -/
theorem nativeComplexAffinePointOpenChart_symm {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) (z : ComplexAffineChartPoint f c) :
    let := schemeAnalyticPointTopology f
    (nativeComplexAffinePointOpenChart f c z).symm = complexAffineChartPointMap f c := by
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAffineChartPoint f c) := ⟨z⟩
  exact (complexAffineChartPointMap_isOpenEmbedding f c).toOpenPartialHomeomorph_apply _

section InverseAffineGerms

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (p : SchemeComplexPoint f) (c : ComplexAffineChart X) (z : ComplexAffineChartPoint f c)

/-- Actual affine lifts of actual inverse uniform coordinates. -/
def nativeSchemeCoordinateAffineLift :
    let := schemeAnalyticPointTopology f
    (Fin n → ℂ) → ComplexAffineChartPoint f c :=
  let := schemeAnalyticPointTopology f
  fun u => nativeComplexAffinePointOpenChart f c z ((schemeAnalyticCoordinateChart f n p).symm u)

/-- The actual affine lifts represent the actual inverse points on a derived neighborhood. -/
theorem nativeSchemeCoordinateAffineLift_eventually_map :
    let := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateChart f n p).target)
      (_hz : complexAffineChartPointMap f c z = (schemeAnalyticCoordinateChart f n p).symm t),
      (fun u => complexAffineChartPointMap f c (nativeSchemeCoordinateAffineLift f n p c z u))
        =ᶠ[𝓝 t] (fun u => (schemeAnalyticCoordinateChart f n p).symm u) := by
  let := schemeAnalyticPointTopology f
  dsimp only
  intro t ht hz
  have hs : (schemeAnalyticCoordinateChart f n p).symm t ∈
      (nativeComplexAffinePointOpenChart f c z).source := by
    rw [nativeComplexAffinePointOpenChart_source]
    exact ⟨z, hz⟩
  have hnear := Filter.Tendsto.eventually
    ((schemeAnalyticCoordinateChart f n p).continuousAt_symm ht)
    ((nativeComplexAffinePointOpenChart f c z).open_source.mem_nhds hs)
  filter_upwards [hnear] with u hu
  rw [← nativeComplexAffinePointOpenChart_symm f c z]
  exact (nativeComplexAffinePointOpenChart f c z).left_inv hu

/-- Genuine affine fraction transfer derives analyticity of every lifted regular evaluation. -/
theorem nativeSchemeCoordinateAffineLift_eval_analyticAt :
    let := schemeAnalyticPointTopology f
    let := affinePointFieldAlgebra (c.map ≫ f)
    ∀ (t : Fin n → ℂ) (_ht : t ∈ (schemeAnalyticCoordinateChart f n p).target)
      (_hz : complexAffineChartPointMap f c z = (schemeAnalyticCoordinateChart f n p).symm t)
      (b : c.ring),
      AnalyticAt ℂ (fun u => affineSchemePointHomeomorphOfStructure (c.map ≫ f)
        (nativeSchemeCoordinateAffineLift f n p c z u) b) t := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra (c.map ≫ f)
  let d := (standardSmoothComplexAffineChart f n p).val
  let := affinePointFieldAlgebra (d.map ≫ f)
  dsimp only
  intro t ht hz b
  apply complexAffineEvaluation_analyticAt f c d n
    (nativeSchemeCoordinateAffineLift f n p c z)
    (schemeAnalyticCoordinateAffineInversePoint f n p) t
  · filter_upwards [nativeSchemeCoordinateAffineLift_eventually_map f n p c z t ht hz]
      with u hu
    exact (schemeAnalyticCoordinateAffineInversePoint_map f n p u).trans hu.symm
  · intro a
    change AnalyticAt ℂ (fun u => affineSchemePointHomeomorphOfStructure (d.map ≫ f)
      (schemeAnalyticCoordinateAffineInversePoint f n p u) a) t
    simpa [d, schemeAnalyticCoordinateAffineInversePoint] using
      schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p a t ht

end InverseAffineGerms

section ClosedImmersionCoordinates

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
  (n m : ℕ) [SmoothOfRelativeDimension n (i ≫ f)] [SmoothOfRelativeDimension m f]

/-- The literal actual scheme-point map in the actual uniform free-generator coordinates. -/
def nativeClosedImmersionCoordinateMap (p : SchemeComplexPoint (i ≫ f))
    (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    (Fin n → ℂ) → (Fin m → ℂ) :=
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  fun t => schemeAnalyticCoordinateChart f m q
    (schemeComplexPointMap (i ≫ f) f i rfl ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm t))

/-- The true open source-target chart domain of the actual point map. -/
def nativeClosedImmersionCoordinateDomain (p : SchemeComplexPoint (i ≫ f))
    (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    Set (Fin n → ℂ) :=
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  (schemeAnalyticCoordinateChart (i ≫ f) n p).target ∩
    (fun t => schemeComplexPointMap (i ≫ f) f i rfl
      ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm t)) ⁻¹'
      (schemeAnalyticCoordinateChart f m q).source

/-- Actual continuity derives neighborhood membership in the genuine coordinate domain. -/
theorem nativeClosedImmersionCoordinateDomain_eventually (p : SchemeComplexPoint (i ≫ f))
    (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    ∀ t ∈ nativeClosedImmersionCoordinateDomain f i n m p q,
      ∀ᶠ u in 𝓝 t, u ∈ nativeClosedImmersionCoordinateDomain f i n m p q := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  dsimp only
  intro t ht
  have hcont := (closedImmersionComplexPointMap_continuous f i).continuousAt.comp
    ((schemeAnalyticCoordinateChart (i ≫ f) n p).continuousAt_symm ht.1)
  exact Filter.inter_mem ((schemeAnalyticCoordinateChart (i ≫ f) n p).open_target.mem_nhds ht.1)
    (Filter.Tendsto.eventually hcont ((schemeAnalyticCoordinateChart f m q).open_source.mem_nhds ht.2))

/-- The derived actual coordinate domain is genuinely open. -/
theorem nativeClosedImmersionCoordinateDomain_isOpen (p : SchemeComplexPoint (i ≫ f))
    (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    IsOpen (nativeClosedImmersionCoordinateDomain f i n m p q) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  exact isOpen_iff_mem_nhds.mpr (fun t ht =>
    nativeClosedImmersionCoordinateDomain_eventually f i n m p q t ht)

omit [IsClosedImmersion i] in
/-- The actual point belongs to the domain for charts centered at it and its literal image. -/
theorem nativeClosedImmersionCoordinateDomain_point_mem (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    schemeAnalyticCoordinateChart (i ≫ f) n p p ∈
      nativeClosedImmersionCoordinateDomain f i n m p (schemeComplexPointMap (i ≫ f) f i rfl p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  have hp := schemeAnalyticCoordinateChart_point_mem_source (i ≫ f) n p
  refine ⟨(schemeAnalyticCoordinateChart (i ≫ f) n p).map_source hp, ?_⟩
  change schemeComplexPointMap (i ≫ f) f i rfl
    ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm
      (schemeAnalyticCoordinateChart (i ≫ f) n p p)) ∈
      (schemeAnalyticCoordinateChart f m (schemeComplexPointMap (i ≫ f) f i rfl p)).source
  rw [(schemeAnalyticCoordinateChart (i ≫ f) n p).left_inv hp]
  exact schemeAnalyticCoordinateChart_point_mem_source f m _

/-- Genuine affine lifts map to the actual target source-chart points on a derived neighborhood. -/
theorem nativeClosedImmersionCoordinateAffineLift_eventually_image
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let d := (standardSmoothComplexAffineChart f m q).val
    let e := closedImmersionAffineSourceChart i d
    ∀ (t : Fin n → ℂ) (_ht : t ∈ nativeClosedImmersionCoordinateDomain f i n m p q)
      (z : ComplexAffineChartPoint (i ≫ f) e)
      (_hz : complexAffineChartPointMap (i ≫ f) e z =
        (schemeAnalyticCoordinateChart (i ≫ f) n p).symm t),
      ∀ᶠ u in 𝓝 t,
        closedImmersionAffineChartPointMap f i d
          (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z u) =
        schemeAnalyticCoordinateAffineSourcePoint f m q
          (schemeComplexPointMap (i ≫ f) f i rfl
            ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm u)) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let d := (standardSmoothComplexAffineChart f m q).val
  let e := closedImmersionAffineSourceChart i d
  dsimp only
  intro t ht z hz
  filter_upwards [nativeClosedImmersionCoordinateDomain_eventually f i n m p q t ht,
    nativeSchemeCoordinateAffineLift_eventually_map (i ≫ f) n p e z t ht.1 hz]
    with u hu hzu
  apply complexAffineChartPointMap_injective f d
  exact (congrFun (closedImmersionAffineChartPointMap_fac f i d)
    (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z u)).symm.trans
      ((congrArg (schemeComplexPointMap (i ≫ f) f i rfl) hzu).trans
        (schemeAnalyticCoordinateAffineSourcePoint_map f m q _ hu.2).symm)

/-- The literal closed-immersion coordinate map is analytic on its genuine open domain. -/
theorem nativeClosedImmersionCoordinateMap_analyticOnNhd
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    AnalyticOnNhd ℂ (nativeClosedImmersionCoordinateMap f i n m p q)
      (nativeClosedImmersionCoordinateDomain f i n m p q) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let c := (standardSmoothComplexAffineChart (i ≫ f) n p).val
  let d := (standardSmoothComplexAffineChart f m q).val
  let e := closedImmersionAffineSourceChart i d
  let := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
  dsimp only
  intro t ht
  let x := schemeAnalyticCoordinateAffineInversePoint (i ≫ f) n p t
  let y := schemeAnalyticCoordinateAffineSourcePoint f m q
    (schemeComplexPointMap (i ≫ f) f i rfl ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm t))
  have hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y :=
    (congrArg (schemeComplexPointMap (i ≫ f) f i rfl)
      (schemeAnalyticCoordinateAffineInversePoint_map (i ≫ f) n p t)).trans
        (schemeAnalyticCoordinateAffineSourcePoint_map f m q _ ht.2).symm
  obtain ⟨z, hz, _⟩ := exists_closedImmersionAffineSourceChartPoint f i c d x y hxy
  have hzglobal : complexAffineChartPointMap (i ≫ f) e z =
      (schemeAnalyticCoordinateChart (i ≫ f) n p).symm t :=
    hz.trans (schemeAnalyticCoordinateAffineInversePoint_map (i ≫ f) n p t)
  apply AnalyticAt.pi
  intro j
  let a : d.ring := standardSmoothComplexChartFreeGenerator f m q j
  have ha := nativeSchemeCoordinateAffineLift_eval_analyticAt (i ≫ f) n p e z t ht.1
    hzglobal ((Spec.preimage (closedImmersionAffineChartMap i d)).hom a)
  apply ha.congr
  filter_upwards [nativeClosedImmersionCoordinateDomain_eventually f i n m p q t ht,
    nativeClosedImmersionCoordinateAffineLift_eventually_image f i n m p q t ht z hzglobal]
    with u hu himage
  rw [← closedImmersionAffineChartPointMap_eval, himage]
  simpa [d, schemeAnalyticCoordinateAffineSourcePoint, nativeClosedImmersionCoordinateMap] using
    (schemeAnalyticCoordinateChart_apply f m q _ hu.2 j).symm

/-- Every complex smoothness order holds for the actual coordinate expression on its true domain. -/
theorem nativeClosedImmersionCoordinateMap_contDiffOn
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    ContDiffOn ℂ k (nativeClosedImmersionCoordinateMap f i n m p q)
      (nativeClosedImmersionCoordinateDomain f i n m p q) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  exact (nativeClosedImmersionCoordinateMap_analyticOnNhd f i n m p q).contDiffOn
    (nativeClosedImmersionCoordinateDomain_isOpen f i n m p q).uniqueDiffOn

/-- Actual principal fraction lifts produce an analytic left-inverse germ of the literal coordinate map. -/
theorem exists_nativeClosedImmersionCoordinateRetraction_germ
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ nativeClosedImmersionCoordinateDomain f i n m p q),
      ∃ H : (Fin m → ℂ) → (Fin n → ℂ),
        AnalyticAt ℂ H (nativeClosedImmersionCoordinateMap f i n m p q t) ∧
        (fun u => H (nativeClosedImmersionCoordinateMap f i n m p q u)) =ᶠ[𝓝 t] id := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let c := (standardSmoothComplexAffineChart (i ≫ f) n p).val
  let d := (standardSmoothComplexAffineChart f m q).val
  let e := closedImmersionAffineSourceChart i d
  let := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
  dsimp only
  intro t ht
  let x := schemeAnalyticCoordinateAffineInversePoint (i ≫ f) n p t
  let y := schemeAnalyticCoordinateAffineSourcePoint f m q
    (schemeComplexPointMap (i ≫ f) f i rfl ((schemeAnalyticCoordinateChart (i ≫ f) n p).symm t))
  have hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y :=
    (congrArg (schemeComplexPointMap (i ≫ f) f i rfl)
      (schemeAnalyticCoordinateAffineInversePoint_map (i ≫ f) n p t)).trans
        (schemeAnalyticCoordinateAffineSourcePoint_map f m q _ ht.2).symm
  obtain ⟨z, hz, _, r, hr, N, R, B, hR, hB, hden, hRden⟩ :=
    exists_closedImmersion_ambient_common_fraction_lifts f i c d x y hxy
      (fun j : Fin n => standardSmoothComplexChartFreeGenerator (i ≫ f) n p j)
  have hzglobal : complexAffineChartPointMap (i ≫ f) e z =
      (schemeAnalyticCoordinateChart (i ≫ f) n p).symm t :=
    hz.trans (schemeAnalyticCoordinateAffineInversePoint_map (i ≫ f) n p t)
  let H : (Fin m → ℂ) → (Fin n → ℂ) := fun v j =>
    schemeAnalyticCoordinateChartInverseAlgebraPoint f m q v (B j) /
      schemeAnalyticCoordinateChartInverseAlgebraPoint f m q v R ^ N
  have htarget : nativeClosedImmersionCoordinateMap f i n m p q t ∈
      (schemeAnalyticCoordinateChart f m q).target :=
    (schemeAnalyticCoordinateChart f m q).map_source ht.2
  have hRtarget : schemeAnalyticCoordinateChartInverseAlgebraPoint f m q
      (nativeClosedImmersionCoordinateMap f i n m p q t) R ≠ 0 := by
    change schemeAnalyticCoordinateChartInverseAlgebraPoint f m q
      (schemeAnalyticCoordinateChart f m q _) R ≠ 0
    rw [schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f m q _ ht.2]
    simpa [d, y, schemeAnalyticCoordinateAffineSourcePoint] using hRden
  refine ⟨H, ?_, ?_⟩
  · apply AnalyticAt.pi
    intro j
    exact (schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f m q (B j) _ htarget).div
      ((schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f m q R _ htarget).pow N)
      (pow_ne_zero N hRtarget)
  · have hmaps := nativeSchemeCoordinateAffineLift_eventually_map (i ≫ f) n p e z t ht.1 hzglobal
    have hzt : nativeSchemeCoordinateAffineLift (i ≫ f) n p e z t = z := by
      apply complexAffineChartPointMap_injective (i ≫ f) e
      exact hmaps.eq_of_nhds.trans hzglobal.symm
    have hdenAt : affineSchemePointHomeomorphOfStructure (e.map ≫ (i ≫ f))
        (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z t) r ≠ 0 := by
      rw [hzt]
      exact hden
    have hnonzero : ∀ᶠ u in 𝓝 t, affineSchemePointHomeomorphOfStructure (e.map ≫ (i ≫ f))
        (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z u) r ≠ 0 :=
      Filter.Tendsto.eventually (p := fun v : ℂ => v ≠ 0)
        (nativeSchemeCoordinateAffineLift_eval_analyticAt (i ≫ f) n p e z t ht.1 hzglobal r).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hdenAt)
    filter_upwards [nativeClosedImmersionCoordinateDomain_eventually f i n m p q t ht,
      hmaps, hnonzero,
      nativeClosedImmersionCoordinateAffineLift_eventually_image f i n m p q t ht z hzglobal]
      with u hu hmap hru himage
    ext j
    have hshared : complexAffineChartPointMap (i ≫ f) e
        (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z u) =
        complexAffineChartPointMap (i ≫ f) c
          (schemeAnalyticCoordinateAffineInversePoint (i ≫ f) n p u) :=
      hmap.trans (schemeAnalyticCoordinateAffineInversePoint_map (i ≫ f) n p u).symm
    have heval := closedImmersion_ambient_common_fraction_eval f i c d r hr
      (schemeAnalyticCoordinateAffineInversePoint (i ≫ f) n p u)
      (nativeSchemeCoordinateAffineLift (i ≫ f) n p e z u) hshared hru
      (standardSmoothComplexChartFreeGenerator (i ≫ f) n p j) N R (B j) hR (hB j)
    rw [himage] at heval
    have hread := schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f m q _ hu.2
    have hsource := schemeAnalyticCoordinateChart_inverse_freeGenerator (i ≫ f) n p u hu.1 j
    change schemeAnalyticCoordinateChartInverseAlgebraPoint f m q
        (schemeAnalyticCoordinateChart f m q _) (B j) /
      schemeAnalyticCoordinateChartInverseAlgebraPoint f m q
        (schemeAnalyticCoordinateChart f m q _) R ^ N = u j
    rw [hread]
    simpa [c, d, schemeAnalyticCoordinateAffineInversePoint,
      schemeAnalyticCoordinateAffineSourcePoint, hsource] using heval.symm

/-- Differentiating the actual retraction germ produces a complex derivative left inverse. -/
theorem exists_nativeClosedImmersionCoordinateMap_fderiv_leftInverse
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ nativeClosedImmersionCoordinateDomain f i n m p q),
      ∃ L : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ),
        L.comp (fderiv ℂ (nativeClosedImmersionCoordinateMap f i n m p q) t) =
          ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  dsimp only
  intro t ht
  obtain ⟨H, hH, heq⟩ := exists_nativeClosedImmersionCoordinateRetraction_germ f i n m p q t ht
  have hT := (nativeClosedImmersionCoordinateMap_analyticOnNhd f i n m p q t ht).differentiableAt
  have hcomp := hH.differentiableAt.hasFDerivAt.comp t hT.hasFDerivAt
  exact ⟨_, (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id t)⟩

/-- The actual closed-immersion coordinate derivative is injective at every genuine overlap point. -/
theorem nativeClosedImmersionCoordinateMap_fderiv_injective
    (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    ∀ (t : Fin n → ℂ) (_ht : t ∈ nativeClosedImmersionCoordinateDomain f i n m p q),
      Function.Injective (fderiv ℂ (nativeClosedImmersionCoordinateMap f i n m p q) t) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  dsimp only
  intro t ht
  obtain ⟨L, hL⟩ := exists_nativeClosedImmersionCoordinateMap_fderiv_leftInverse f i n m p q t ht
  intro v w hvw
  have hv := congrArg (fun A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => A v) hL
  have hw := congrArg (fun A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => A w) hL
  change _ = v at hv
  change _ = w at hw
  exact hv.symm.trans ((congrArg L hvw).trans hw)

end ClosedImmersionCoordinates

end

end ComplexSchemes
