import EnvelopeProperty.Char0.NativeAffineOpenJacobian
import EnvelopeProperty.Char0.NativeMultiplierGermTransform

/-! # Whole native pullback through the SAME original global and restricted morphisms -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineOpenGermComposition

open CategoryTheory AlgebraicGeometry BingWangEntropy SGPT.Okounkov Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open HolomorphicMaps HolomorphicIdealSheaves
open NativeAffineOpenJacobian SGPT.Okounkov.NativeOpenJacobian
open scoped Topology Manifold ContDiff

private theorem transport_mk {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] {x y : M} (h : x = y)
    (F : M → ℂ) (hF : HolomorphicAt m F x) :
    (h ▸ NativeHolGerm.mk F hF : NativeHolGerm m M y) =
      NativeHolGerm.mk F (h ▸ hF) := by
  cases h
  rfl

variable {R B : Type} [CommRing R] [CommRing B] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R))
  (c : Spec (.of B) ⟶ Y) [IsOpenImmersion c] (n m : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension m f]
  [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)]

local instance baseAffine : IsAffineHom f := isAffineHom_of_isAffine f
local instance sourceAffine : IsAffineHom ((c ≫ π) ≫ f) := isAffineHom_of_isAffine _
private instance sourceSmooth : SmoothOfRelativeDimension n ((c ≫ π) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := c) (n := 0) (m := n) (π ≫ f))

local instance baseTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance globalTopology : TopologicalSpace (SchemeComplexPoint (π ≫ f)) := schemeAnalyticPointTopology _
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint ((c ≫ π) ≫ f)) := schemeAnalyticPointTopology _
local instance baseCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f m
local instance globalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (π ≫ f)) := schemeAnalyticTNChartedSpace _ n
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint ((c ≫ π) ≫ f)) := schemeAnalyticTNChartedSpace _ n
local instance baseManifold : IsComplexManifold m (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f m
local instance globalManifold : IsComplexManifold n (SchemeComplexPoint (π ≫ f)) := schemeAnalyticTN_isComplexManifold _ n
local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint ((c ≫ π) ≫ f)) := schemeAnalyticTN_isComplexManifold _ n

omit [IsOpenImmersion c] [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] in
/-- The SAME original whole base point is obtained through the global map or its actual affine restriction. -/
theorem basePoint_comp (q : SchemeComplexPoint ((c ≫ π) ≫ f)) :
    schemeComplexPointMap (π ≫ f) f π rfl (affineOpenPointMap f π c q) =
      schemeComplexPointMap ((c ≫ π) ≫ f) f (c ≫ π) rfl q := by
  apply Subtype.ext
  exact Category.assoc q.val c π

/-- EVERY whole original native germ has the SAME actual iterated and direct restricted pullback. -/
theorem nativePullback_comp (q : SchemeComplexPoint ((c ≫ π) ≫ f))
    (g : NativeHolGerm m (SchemeComplexPoint f)
      (schemeComplexPointMap ((c ≫ π) ≫ f) f (c ≫ π) rfl q)) :
    NativeHolGerm.comap (affineOpenPointMap f π c)
      (schemeComplexPointMap_contMDiff_of_structure (π ≫ f) ((c ≫ π) ≫ f)
        c (Category.assoc c π f).symm n ∞) q
      (schemeMorphismNativeGermPullback f π n m (affineOpenPointMap f π c q)
        ((basePoint_comp f π c q).symm ▸ g)) =
      schemeMorphismNativeGermPullback f (c ≫ π) n m q g := by
  obtain ⟨F, hF, rfl⟩ := NativeHolGerm.exists_eq_mk g
  rw [transport_mk ((basePoint_comp f π c q).symm) F hF]
  apply Subtype.ext
  change ((fun z => F (schemeComplexPointMap (π ≫ f) f π rfl (affineOpenPointMap f π c z))) :
      Germ (𝓝 q) ℂ) =
    ((fun z => F (schemeComplexPointMap ((c ≫ π) ≫ f) f (c ≫ π) rfl z)) : Germ (𝓝 q) ℂ)
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => congrArg F (basePoint_comp f π c z)

/-- The actual affine-open centered whole-germ map reads exactly the direct original composite pullback. -/
theorem centeredNativePullback_comp (q : SchemeComplexPoint ((c ≫ π) ≫ f))
    (g : NativeHolGerm m (SchemeComplexPoint f)
      (schemeComplexPointMap ((c ≫ π) ≫ f) f (c ≫ π) rfl q)) :
    affineOpenGermPullback f π c n q
      (NativeHolGerm.chartEquiv (affineOpenPointMap f π c q)
        (schemeMorphismNativeGermPullback f π n m (affineOpenPointMap f π c q)
          ((basePoint_comp f π c q).symm ▸ g))) =
      NativeHolGerm.chartEquiv q (schemeMorphismNativeGermPullback f (c ≫ π) n m q g) := by
  exact (NativeHolGerm.chartEquiv_comap (affineOpenPointMap f π c)
    (schemeComplexPointMap_contMDiff_of_structure (π ≫ f) ((c ≫ π) ≫ f)
      c (Category.assoc c π f).symm n ∞) q _).symm.trans
    (congrArg (NativeHolGerm.chartEquiv q) (nativePullback_comp f π c n m q g))

/-- An arbitrary original-base germ uses only its natural original fibre equality;
the global-versus-direct composition transport is derived internally. -/
theorem centeredNativePullback_comp_fiber (x : SchemeComplexPoint f)
    (g : NativeHolGerm m (SchemeComplexPoint f) x)
    (q : SchemeComplexPoint ((c ≫ π) ≫ f))
    (hq : schemeComplexPointMap ((c ≫ π) ≫ f) f (c ≫ π) rfl q = x) :
    affineOpenGermPullback f π c n q
      (NativeHolGerm.chartEquiv (affineOpenPointMap f π c q)
        (schemeMorphismNativeGermPullback f π n m (affineOpenPointMap f π c q)
          (((basePoint_comp f π c q).trans hq).symm ▸ g))) =
      NativeHolGerm.chartEquiv q (schemeMorphismNativeGermPullback f (c ≫ π) n m q (hq.symm ▸ g)) := by
  cases hq
  exact centeredNativePullback_comp f π c n m q g

end EnvelopeProperty.Char0.NativeAffineOpenGermComposition
