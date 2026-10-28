import SGPT.Okounkov.SchemeNativeStalkNaturality
import SGPT.Okounkov.NativeHolomorphicGermCoordinates

/-! # Literal centered coordinates of the original native scheme-morphism germ pullback -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open TranscendentalNakamaye.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance morphismCoordinateGermSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance morphismCoordinateGermTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance morphismCoordinateGermSourceCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance morphismCoordinateGermTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m
local instance morphismCoordinateGermSourceManifold : IsComplexManifold n (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance morphismCoordinateGermTargetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f m

/-- The SAME original point map, centered in its actual existing preferred native charts. -/
def schemeMorphismCenteredCoordinateMap (p : SchemeComplexPoint (h ≫ f)) :
    ComplexModel n → ComplexModel m :=
  NativeHolGerm.centeredCoordinateMap (k := n) (n := m)
    (schemeComplexPointMap (h ≫ f) f h rfl) p

omit [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] [IsSeparated f] [QuasiCompact f] in
/-- The literal centered coordinate map fixes0 internally. -/
theorem schemeMorphismCenteredCoordinateMap_zero (p : SchemeComplexPoint (h ≫ f)) :
    schemeMorphismCenteredCoordinateMap f h n m p 0 = 0 :=
  NativeHolGerm.centeredCoordinateMap_zero _ _

/-- The existing actual holomorphy of the original scheme map gives genuine coordinate holomorphy. -/
theorem schemeMorphismCenteredCoordinateMap_holomorphic (p : SchemeComplexPoint (h ≫ f)) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (schemeMorphismCenteredCoordinateMap f h n m p) z :=
  NativeHolGerm.centeredCoordinateMap_holomorphic _
    (schemeComplexPointMap_contMDiff f h n m ∞) p

/-- WHOLE native holomorphic germ pullback is actual composition in the SAME preferred centered charts. -/
theorem schemeMorphismNativeGermPullback_chart (p : SchemeComplexPoint (h ≫ f))
    (g : NativeHolGerm m (SchemeComplexPoint f) (schemeComplexPointMap (h ≫ f) f h rfl p)) :
    NativeHolGerm.chartEquiv p (schemeMorphismNativeGermPullback f h n m p g) =
      HironakaHolomorphicJetChartInvariance.compAlgHom
        (schemeMorphismCenteredCoordinateMap f h n m p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f h n m p)
        (schemeMorphismCenteredCoordinateMap_zero f h n m p)
        (NativeHolGerm.chartEquiv (schemeComplexPointMap (h ≫ f) f h rfl p) g) :=
  NativeHolGerm.chartEquiv_comap _ (schemeComplexPointMap_contMDiff f h n m ∞) p g

/-- The ENTIRE original algebraic stalk square now commutes in the actual centered coordinate models. -/
theorem schemeNativeStalkGerm_naturality_chart (p : SchemeComplexPoint (h ≫ f))
    (a : Y.presheaf.stalk
      (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p))) :
    NativeHolGerm.chartEquiv p (schemeNativeStalkGerm (h ≫ f) n p
      ((h.stalkMap (schemeComplexPointImage (h ≫ f) p)).hom a)) =
      HironakaHolomorphicJetChartInvariance.compAlgHom
        (schemeMorphismCenteredCoordinateMap f h n m p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f h n m p)
        (schemeMorphismCenteredCoordinateMap_zero f h n m p)
        (NativeHolGerm.chartEquiv (schemeComplexPointMap (h ≫ f) f h rfl p)
          (schemeNativeStalkGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p) a)) := by
  rw [schemeNativeStalkGerm_naturality f h n m p a]
  exact schemeMorphismNativeGermPullback_chart f h n m p _

end SGPT.Okounkov
