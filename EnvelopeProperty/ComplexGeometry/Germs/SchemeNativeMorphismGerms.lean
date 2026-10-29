import EnvelopeProperty.ComplexGeometry.Germs.SchemeAnalyticMorphism
import EnvelopeProperty.ComplexGeometry.Germs.NativeHolomorphicGermRing

/-!
# Actual native holomorphic germ pullback of the original scheme morphism

The original scheme point map is proved holomorphic internally. Its actual
native germ pullback acts on arbitrary holomorphic germs and is local; no
analytic-map, coefficient readback or flatness certificate is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open ComplexGeometry.Pluripotential.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance morphismGermSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance morphismGermTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance morphismGermSourceCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticComplexChartedSpace (h ≫ f) n
local instance morphismGermTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f m
local instance morphismGermSourceManifold : IsComplexManifold n (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticComplex_isComplexManifold (h ≫ f) n
local instance morphismGermTargetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f m

/-- The same original algebraic morphism gives its actual native analytic germ pullback. -/
def schemeMorphismNativeGermPullback (p : SchemeComplexPoint (h ≫ f)) :
    NativeHolGerm m (SchemeComplexPoint f) (schemeComplexPointMap (h ≫ f) f h rfl p) →+*
      NativeHolGerm n (SchemeComplexPoint (h ≫ f)) p :=
  NativeHolGerm.comap (schemeComplexPointMap (h ≫ f) f h rfl)
    (schemeComplexPointMap_contMDiff f h n m ∞) p

/-- Pullback retains the whole original holomorphic function germ, not just its value. -/
theorem schemeMorphismNativeGermPullback_mk (p : SchemeComplexPoint (h ≫ f))
    (g : SchemeComplexPoint f → ℂ)
    (hg : HolomorphicAt m g (schemeComplexPointMap (h ≫ f) f h rfl p)) :
    ((schemeMorphismNativeGermPullback f h n m p (NativeHolGerm.mk g hg) :
      NativeHolGerm n (SchemeComplexPoint (h ≫ f)) p) : Germ (𝓝 p) ℂ) =
        (g ∘ schemeComplexPointMap (h ≫ f) f h rfl : Germ (𝓝 p) ℂ) := rfl

/-- Actual point evaluation commutes with the same original native pullback. -/
theorem schemeMorphismNativeGermPullback_eval (p : SchemeComplexPoint (h ≫ f))
    (g : NativeHolGerm m (SchemeComplexPoint f) (schemeComplexPointMap (h ≫ f) f h rfl p)) :
    NativeHolGerm.eval (schemeMorphismNativeGermPullback f h n m p g) = NativeHolGerm.eval g :=
  NativeHolGerm.eval_comap (schemeComplexPointMap (h ≫ f) f h rfl)
    (schemeComplexPointMap_contMDiff f h n m ∞) p g

/-- The actual native pullback is local, with no global integrality assumption. -/
instance schemeMorphismNativeGermPullback_isLocalHom (p : SchemeComplexPoint (h ≫ f)) :
    IsLocalHom (schemeMorphismNativeGermPullback f h n m p) where
  map_nonunit g hg := by
    apply (NativeHolGerm.isUnit_iff_eval_ne_zero g).mpr
    rw [← schemeMorphismNativeGermPullback_eval f h n m p g]
    exact (NativeHolGerm.isUnit_iff_eval_ne_zero _).mp hg

end HolomorphicGerms
