import EnvelopeProperty.ComplexGeometry.Germs.SchemeAnalyticComplexManifold
import EnvelopeProperty.ComplexGeometry.Germs.NativeHolomorphicGermRing

/-!
# Actual scheme regular functions in the original manifold germ ring

The already manufactured separated quasi-compact smooth scheme the manifold
has the SAME preferred transported chart. The existing original chart germ
equivalence and actual PiLp germ pullback identify its actual original germs,
with literal original affine-point evaluation readback on the true source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open scoped Topology Manifold

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance nativeSchemePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance nativeSchemePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n

local instance nativeSchemePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

variable (p : SchemeComplexPoint f)

local instance nativeSchemeAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- Actual coordinate germs become actual ORIGINAL germs through the SAME
preferred transported chart, with no newly supplied manifold instance. -/
def schemeNativeCoordinateGermEquiv :
    HolGerm (Fin n → ℂ) ≃+* NativeHolGerm n (SchemeComplexPoint f) p :=
  (schemeCoordinateModelGermEquiv n).trans (NativeHolGerm.chartEquiv p).symm

/-- The original point evaluation is preserved by the genuine comparison. -/
theorem schemeNativeCoordinateGermEquiv_eval (g : HolGerm (Fin n → ℂ)) :
    NativeHolGerm.eval (schemeNativeCoordinateGermEquiv f n p g) = HolGerm.eval g := by
  rw [← NativeHolGerm.eval_chartEquiv]
  change HolGerm.eval ((NativeHolGerm.chartEquiv p)
    ((NativeHolGerm.chartEquiv p).symm (schemeCoordinateModelGermEquiv n g))) = _
  rw [RingEquiv.apply_symm_apply, schemeCoordinateModelGermEquiv_eval]

/-- Whole literal complex constant germs are preserved. -/
theorem schemeNativeCoordinateGermEquiv_const (c : ℂ) :
    schemeNativeCoordinateGermEquiv f n p (HolGerm.constHom c) =
      NativeHolGerm.constHom c := by
  apply (NativeHolGerm.chartEquiv p).injective
  change (NativeHolGerm.chartEquiv p)
    ((NativeHolGerm.chartEquiv p).symm
      (schemeCoordinateModelGermEquiv n (HolGerm.constHom c))) = _
  rw [RingEquiv.apply_symm_apply, schemeCoordinateModelGermEquiv_const]
  rfl

/-- The actual affine regular map now lands in actual ORIGINAL germs. -/
def schemeNativeRegularGerm :
    SchemeCoordinateAffineRing f n p →+* NativeHolGerm n (SchemeComplexPoint f) p :=
  (schemeNativeCoordinateGermEquiv f n p).toRingHom.comp (schemeCoordinateRegularGerm f n p)

/-- Whole preferred-chart readback retains the already proved actual germ. -/
theorem schemeNativeRegularGerm_chart (a : SchemeCoordinateAffineRing f n p) :
    NativeHolGerm.chartEquiv p (schemeNativeRegularGerm f n p a) =
      schemeCoordinateModelGermEquiv n (schemeCoordinateRegularGerm f n p a) := by
  exact (NativeHolGerm.chartEquiv p).apply_symm_apply _

/-- Actual native evaluation recovers the SAME original affine algebra point. -/
theorem schemeNativeRegularGerm_eval (a : SchemeCoordinateAffineRing f n p) :
    NativeHolGerm.eval (schemeNativeRegularGerm f n p a) =
      standardSmoothComplexAlgebraPoint f n p a := by
  exact (schemeNativeCoordinateGermEquiv_eval f n p _).trans
    (schemeCoordinateRegularGerm_eval f n p a)

/-- As a germ on the ORIGINAL point space, the produced element is literal
evaluation at that SAME point's actual affine lift on the true chart source. -/
theorem schemeNativeRegularGerm_source (a : SchemeCoordinateAffineRing f n p) :
    ((schemeNativeRegularGerm f n p a : NativeHolGerm n (SchemeComplexPoint f) p) :
      Germ (𝓝 p) ℂ) =
        (fun q : SchemeComplexPoint f => standardSmoothComplexPointOpenChart f n p q a) := by
  apply Germ.coe_eq.mpr
  change (fun q : SchemeComplexPoint f => schemeCoordinateRegularRepresentative f n p a
    (schemeCoordinateModelEquiv n
      ((schemeCoordinateModelEquiv n).symm (schemeAnalyticCoordinateChart f n p q) -
        (schemeCoordinateModelEquiv n).symm (schemeAnalyticCoordinateChart f n p p)))) =ᶠ[𝓝 p] _
  filter_upwards [(schemeAnalyticCoordinateChart f n p).open_source.mem_nhds
    (schemeAnalyticCoordinateChart_point_mem_source f n p)] with q hq
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact schemeCoordinateRegularRepresentative_source f n p a q hq

/-- The actual ORIGINAL scheme stalk maps to the actual ORIGINAL analytic stalk. -/
def schemeNativeStalkGerm :
    X.presheaf.stalk (schemeComplexPointImage f p) →+*
      NativeHolGerm n (SchemeComplexPoint f) p :=
  (schemeNativeCoordinateGermEquiv f n p).toRingHom.comp
    (schemeCoordinateStalkRegularGerm f n p)

/-- Every actual original affine regular element has the SAME original germ. -/
theorem schemeNativeStalkGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeNativeStalkGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p) a)) =
        schemeNativeRegularGerm f n p a := by
  change schemeNativeCoordinateGermEquiv f n p
    (schemeCoordinateStalkRegularGerm f n p _) = _
  rw [schemeCoordinateStalkRegularGerm_regular]
  rfl

/-- Every actual original local fraction retains its literal residue. -/
theorem schemeNativeStalkGerm_eval_mk' (a : SchemeCoordinateAffineRing f n p)
    (s : (schemeCoordinatePointIdeal f n p).primeCompl) :
    NativeHolGerm.eval (schemeNativeStalkGerm f n p
      (schemeCoordinateStalkEquiv f n p
        (IsLocalization.mk' (SchemeCoordinateLocalRing f n p) a s))) =
      standardSmoothComplexAlgebraPoint f n p a / standardSmoothComplexAlgebraPoint f n p s := by
  exact (schemeNativeCoordinateGermEquiv_eval f n p _).trans
    (schemeCoordinateStalkRegularGerm_eval_mk' f n p a s)

/-- Actual original localness is retained by the genuine germ equivalence. -/
instance schemeNativeStalkGerm_isLocalHom : IsLocalHom (schemeNativeStalkGerm f n p) := by
  unfold schemeNativeStalkGerm
  let e := schemeNativeCoordinateGermEquiv f n p
  let : IsLocalHom e.toRingHom := by
    refine ⟨fun a ha => ?_⟩
    have h := ha.map e.symm.toRingHom
    change IsUnit (e.symm (e a)) at h
    rwa [RingEquiv.symm_apply_apply] at h
  exact RingHom.isLocalHom_comp e.toRingHom (schemeCoordinateStalkRegularGerm f n p)

/-- Genuine original integrality supplies native affine-germ injectivity. -/
theorem schemeNativeRegularGerm_injective [IsIntegral X] :
    Function.Injective (schemeNativeRegularGerm f n p) :=
  (schemeNativeCoordinateGermEquiv f n p).injective.comp
    (schemeCoordinateRegularGerm_injective f n p)

/-- Genuine original integrality supplies actual ORIGINAL stalk injectivity. -/
theorem schemeNativeStalkGerm_injective [IsIntegral X] :
    Function.Injective (schemeNativeStalkGerm f n p) :=
  (schemeNativeCoordinateGermEquiv f n p).injective.comp
    (schemeCoordinateStalkRegularGerm_injective f n p)

end HolomorphicGerms
