import SGPT.Okounkov.SchemeNativeHolomorphicGerm
import BingWangEntropy.NativeProjectiveAnalyticMorphismGerms
import BingWangEntropy.NativeProjectiveFano
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Actual arbitrary-affine evaluation on the original analytic point space

The native arbitrary-affine fraction-germ theorem supplies analyticity. The
existing SAME preferred centered-germ equivalence returns actual original
holomorphic germs and literal original-point function readbacks. Original
stalk-map compatibility and section-divisor gluing are subsequent links.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Set
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open TranscendentalNakamaye.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- Literal regular evaluation through the actual inverse affine point chart. -/
def schemeAffineRegularEvaluation (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) (q : SchemeComplexPoint f) : ℂ :=
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra (c.map ≫ f)
  affineSchemePointHomeomorphOfStructure (c.map ≫ f)
    (nativeComplexAffinePointOpenChart f c z q) a

/-- The actual affine lift at its SAME original point evaluates literally. -/
theorem schemeAffineRegularEvaluation_point (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    schemeAffineRegularEvaluation f c z a (complexAffineChartPointMap f c z) =
      affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  let := schemeAnalyticPointTopology f
  let := affinePointFieldAlgebra (c.map ≫ f)
  have hs : complexAffineChartPointMap f c z ∈ (nativeComplexAffinePointOpenChart f c z).source := by
    rw [nativeComplexAffinePointOpenChart_source]
    exact ⟨z, rfl⟩
  have hinv : nativeComplexAffinePointOpenChart f c z (complexAffineChartPointMap f c z) = z := by
    apply complexAffineChartPointMap_injective f c
    rw [← nativeComplexAffinePointOpenChart_symm f c z]
    exact (nativeComplexAffinePointOpenChart f c z).left_inv hs
  change affineSchemePointHomeomorphOfStructure (c.map ≫ f)
    (nativeComplexAffinePointOpenChart f c z (complexAffineChartPointMap f c z)) a = _
  rw [hinv]

variable (n : ℕ) [SmoothOfRelativeDimension n f]
  (c : ComplexAffineChart X) (z : ComplexAffineChartPoint f c)

local instance affineEvaluationTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

private def affineCenteredEvaluation (a : c.ring) (w : Fin n → ℂ) : ℂ :=
  affineSchemePointHomeomorphOfStructure (c.map ≫ f)
    (nativeSchemeCoordinateAffineLift f n (complexAffineChartPointMap f c z) c z
      (w + schemeCoordinateCenter f n (complexAffineChartPointMap f c z))) a

private theorem affineCenteredEvaluation_analytic (a : c.ring) :
    AnalyticAt ℂ (affineCenteredEvaluation f n c z a) 0 := by
  let p := complexAffineChartPointMap f c z
  let e := schemeAnalyticCoordinateChart f n p
  have ht : schemeCoordinateCenter f n p ∈ e.target :=
    e.map_source (schemeAnalyticCoordinateChart_point_mem_source f n p)
  have hp : complexAffineChartPointMap f c z = e.symm (schemeCoordinateCenter f n p) :=
    (e.left_inv (schemeAnalyticCoordinateChart_point_mem_source f n p)).symm
  have ha := nativeSchemeCoordinateAffineLift_eval_analyticAt f n p c z
    (schemeCoordinateCenter f n p) ht hp a
  have htr : AnalyticAt ℂ
      (fun w : Fin n → ℂ => w + schemeCoordinateCenter f n p) 0 :=
    analyticAt_id.add analyticAt_const
  change AnalyticAt ℂ
    ((fun u => affineSchemePointHomeomorphOfStructure (c.map ≫ f)
      (nativeSchemeCoordinateAffineLift f n p c z u) a) ∘
        (fun w : Fin n → ℂ => w + schemeCoordinateCenter f n p)) 0
  apply AnalyticAt.comp (x := (0 : Fin n → ℂ)) ?_ htr
  simpa only [zero_add] using ha

private def affineCoordinateEvaluationGerm : c.ring →+* HolGerm (Fin n → ℂ) where
  toFun a := HolGerm.mk (affineCenteredEvaluation f n c z a)
    ((affineCenteredEvaluation_analytic f n c z a).eventually_analyticAt.mono
      fun _ h => h.differentiableAt)
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => map_mul _ a b
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => map_zero _
  map_add' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => map_add _ a b

local instance affineEvaluationCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance affineEvaluationManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

namespace SmoothSchemeGerms

variable [IsSeparated f] [QuasiCompact f]

/-- Actual arbitrary-affine evaluations manufacture ORIGINAL holomorphic germs. -/
def affineRegularGerm :
    c.ring →+* NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z) := by
  exact (schemeNativeCoordinateGermEquiv f n (complexAffineChartPointMap f c z)).toRingHom.comp
    (affineCoordinateEvaluationGerm f n c z)

/-- WHOLE original-germ readback is the literal original affine evaluation function. -/
theorem affineRegularGerm_source (a : c.ring) :
    ((affineRegularGerm f n c z a :
      NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z)) :
        Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) =
      (schemeAffineRegularEvaluation f c z a : Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) := by
  apply Germ.coe_eq.mpr
  let p := complexAffineChartPointMap f c z
  change (fun q : SchemeComplexPoint f => affineCenteredEvaluation f n c z a
    (schemeCoordinateModelEquiv n
      ((schemeCoordinateModelEquiv n).symm (schemeAnalyticCoordinateChart f n p q) -
        (schemeCoordinateModelEquiv n).symm (schemeAnalyticCoordinateChart f n p p)))) =ᶠ[𝓝 p] _
  filter_upwards [(schemeAnalyticCoordinateChart f n p).open_source.mem_nhds
    (schemeAnalyticCoordinateChart_point_mem_source f n p)] with q hq
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  change schemeAffineRegularEvaluation f c z a ((schemeAnalyticCoordinateChart f n p).symm
    (schemeAnalyticCoordinateChart f n p q - schemeAnalyticCoordinateChart f n p p +
      schemeAnalyticCoordinateChart f n p p)) = schemeAffineRegularEvaluation f c z a q
  rw [sub_add_cancel, (schemeAnalyticCoordinateChart f n p).left_inv hq]

private theorem holomorphicAt_of_nativeGerm {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] {p : M} (g : NativeHolGerm d M p)
    (h : M → ℂ) (heq : (g : Germ (𝓝 p) ℂ) = (h : Germ (𝓝 p) ℂ)) :
    HolomorphicAt d h p := by
  obtain ⟨r, hr, hrg⟩ := g.property
  have hh : r =ᶠ[𝓝 p] h := Germ.coe_eq.mp (hrg.trans heq)
  filter_upwards [hr, hh.eventually_nhds] with q hq hlocal
  exact hq.congr_of_eventuallyEq (Filter.EventuallyEq.symm hlocal)

/-- Every point in the TRUE affine source has a neighborhood-holomorphic literal evaluation. -/
theorem affineRegularEvaluation_holomorphicAt_source (a : c.ring)
    (p : SchemeComplexPoint f) (hp : p ∈ Set.range (complexAffineChartPointMap f c)) :
    HolomorphicAt n (schemeAffineRegularEvaluation f c z a) p := by
  obtain ⟨w, rfl⟩ := hp
  have hw := holomorphicAt_of_nativeGerm (affineRegularGerm f n c w a)
    (schemeAffineRegularEvaluation f c w a) (affineRegularGerm_source f n c w a)
  have hs : complexAffineChartPointMap f c w ∈ (nativeComplexAffinePointOpenChart f c z).source := by
    rw [nativeComplexAffinePointOpenChart_source]
    exact ⟨w, rfl⟩
  have heq : schemeAffineRegularEvaluation f c z a =ᶠ[𝓝 (complexAffineChartPointMap f c w)]
      schemeAffineRegularEvaluation f c w a := by
    filter_upwards [(nativeComplexAffinePointOpenChart f c z).open_source.mem_nhds hs] with q hq
    have hqw : q ∈ (nativeComplexAffinePointOpenChart f c w).source := by
      rw [nativeComplexAffinePointOpenChart_source] at hq ⊢
      exact hq
    have hpoints : nativeComplexAffinePointOpenChart f c z q =
        nativeComplexAffinePointOpenChart f c w q := by
      apply complexAffineChartPointMap_injective f c
      calc
        _ = q := by
          rw [← nativeComplexAffinePointOpenChart_symm f c z]
          exact (nativeComplexAffinePointOpenChart f c z).left_inv hq
        _ = _ := by
          rw [← nativeComplexAffinePointOpenChart_symm f c w]
          exact ((nativeComplexAffinePointOpenChart f c w).left_inv hqw).symm
    exact congrArg (fun y => affineSchemePointHomeomorphOfStructure (c.map ≫ f) y a) hpoints
  filter_upwards [hw, heq.eventually_nhds] with q hq heqq
  exact hq.congr_of_eventuallyEq heqq

/-- Evaluation reads the SAME original affine algebra point, without a point-match premise. -/
theorem affineRegularGerm_eval (a : c.ring) :
    NativeHolGerm.eval (affineRegularGerm f n c z a) =
      affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  have h := congrArg (Germ.valueRingHom : Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ →+* ℂ)
    (affineRegularGerm_source f n c z a)
  exact h.trans (schemeAffineRegularEvaluation_point f c z a)

/-- Literal structural constants remain the literal ORIGINAL constant germs. -/
theorem affineRegularGerm_scalar (b : ℂ) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    affineRegularGerm f n c z (algebraMap ℂ c.ring b) =
      NativeHolGerm.constHom b := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  change schemeNativeCoordinateGermEquiv f n (complexAffineChartPointMap f c z)
    (affineCoordinateEvaluationGerm f n c z (algebraMap ℂ c.ring b)) = _
  rw [← schemeNativeCoordinateGermEquiv_const f n (complexAffineChartPointMap f c z) b]
  apply congrArg (schemeNativeCoordinateGermEquiv f n (complexAffineChartPointMap f c z))
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun w =>
    (affineSchemePointHomeomorphOfStructure (c.map ≫ f)
      (nativeSchemeCoordinateAffineLift f n (complexAffineChartPointMap f c z) c z
        (w + schemeCoordinateCenter f n (complexAffineChartPointMap f c z)))).commutes b

end SmoothSchemeGerms

variable (E : ClosedProjectiveEmbedding f)

/-- Compatibility interface for a closed projective embedding; the proof uses only separated/QC. -/
def schemeAffineNativeRegularGerm :
    c.ring →+* NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z) := by
  letI := E.isSeparated
  letI := E.quasiCompact
  exact SmoothSchemeGerms.affineRegularGerm f n c z

/-- The legacy projective interface retains the exact whole affine evaluation germ. -/
theorem schemeAffineNativeRegularGerm_source (a : c.ring) :
    ((schemeAffineNativeRegularGerm f n c z E a :
      NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z)) :
        Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) =
      (schemeAffineRegularEvaluation f c z a : Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineRegularGerm_source f n c z a

include E in
/-- Compatibility holomorphy for the same original affine evaluation. -/
theorem schemeAffineRegularEvaluation_holomorphicAt_source (a : c.ring)
    (p : SchemeComplexPoint f) (hp : p ∈ Set.range (complexAffineChartPointMap f c)) :
    HolomorphicAt n (schemeAffineRegularEvaluation f c z a) p := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineRegularEvaluation_holomorphicAt_source f n c z a p hp

/-- The legacy map preserves the same literal point evaluation. -/
theorem schemeAffineNativeRegularGerm_eval (a : c.ring) :
    NativeHolGerm.eval (schemeAffineNativeRegularGerm f n c z E a) =
      affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineRegularGerm_eval f n c z a

/-- The legacy map preserves the original scalar germs. -/
theorem schemeAffineNativeRegularGerm_scalar (b : ℂ) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    schemeAffineNativeRegularGerm f n c z E (algebraMap ℂ c.ring b) =
      NativeHolGerm.constHom b := by
  let := E.isSeparated
  let := E.quasiCompact
  let := affinePointFieldAlgebra (c.map ≫ f)
  exact SmoothSchemeGerms.affineRegularGerm_scalar f n c z b

end SGPT.Okounkov
