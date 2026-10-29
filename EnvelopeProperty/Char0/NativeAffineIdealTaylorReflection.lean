import EnvelopeProperty.Char0.NativeAffineIdealWeight

/-! # The whole original affine ideal under its actual native Taylor square -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open ComplexGeometry.Pluripotential

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineIdealTaylorReflection

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance reflectionTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance reflectionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance reflectionManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- The ENTIRE original affine native coefficient map has precisely its SAME
actual affine formal Taylor map, through the actual original stalk. -/
theorem taylor_comp_nativeMap (x : SchemeComplexPoint f) :
    (NativeHolGerm.taylor x).comp (NativeAffineIdealWeight.nativeMap f n x) =
      schemeAffineNativeFormal f n x := rfl

/-- ANY native germ belongs to the whole original affine ideal extension iff
its actual Taylor series belongs to the SAME original formal ideal extension. -/
theorem mem_map_nativeMap_iff_taylor (x : SchemeComplexPoint f) (K : Ideal R)
    (g : NativeHolGerm n (SchemeComplexPoint f) x) :
    g ∈ K.map (NativeAffineIdealWeight.nativeMap f n x) ↔
      NativeHolGerm.taylor x g ∈ K.map (schemeAffineNativeFormal f n x) := by
  have h := NativeHolGerm.mem_ideal_iff_taylor x
    (K.map (NativeAffineIdealWeight.nativeMap f n x)) g
  simpa only [Ideal.map_map, taylor_comp_nativeMap] using h

end EnvelopeProperty.Char0.NativeAffineIdealTaylorReflection
