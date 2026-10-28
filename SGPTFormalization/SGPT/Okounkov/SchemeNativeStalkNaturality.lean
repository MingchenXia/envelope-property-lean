import SGPT.Okounkov.SchemeComplexPointStalkEvaluation
import SGPT.Okounkov.SchemeNativeMorphismGerms

/-!
# Whole original-stalk naturality for the actual smooth scheme morphism

Nearby holomorphic representatives of actual regular sections and canonical
complex-point evaluation prove equality of entire native germs. Naturality
is manufactured for every element of the original algebraic stalk.
-/

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

local instance stalkNatSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance stalkNatTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance stalkNatSourceCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance stalkNatTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m
local instance stalkNatSourceManifold : IsComplexManifold n (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance stalkNatTargetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f m

/-- The actual native pullback commutes with the original map on the ENTIRE algebraic stalk. -/
theorem schemeNativeStalkGerm_naturality (p : SchemeComplexPoint (h ≫ f))
    (a : Y.presheaf.stalk
      (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p))) :
    schemeNativeStalkGerm (h ≫ f) n p ((h.stalkMap (schemeComplexPointImage (h ≫ f) p)).hom a) =
      schemeMorphismNativeGermPullback f h n m p
        (schemeNativeStalkGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p) a) := by
  let F := schemeComplexPointMap (h ≫ f) f h rfl
  obtain ⟨U, hpU, r, rfl⟩ := Y.presheaf.exists_germ_eq a
  obtain ⟨VY, hVY, hpY, hVYU, HY, hHY, hYread⟩ :=
    SmoothSchemeGerms.regularSection_locally_holomorphic f m U r (F p) hpU
  obtain ⟨VX, hVX, hpX, hVXU, HX, hHX, hXread⟩ :=
    SmoothSchemeGerms.regularSection_locally_holomorphic (h ≫ f) n (h ⁻¹ᵁ U)
      (h.app U r) p hpU
  have hHYhol : HolomorphicAt m HY (F p) := by
    filter_upwards [hVY.mem_nhds hpY] with q hq
    exact (hHY q hq).mdifferentiableAt (hVY.mem_nhds hq)
  have hYgerm : schemeNativeStalkGerm f m (F p)
      (Y.presheaf.germ U (schemeComplexPointImage f (F p)) hpU r) =
        NativeHolGerm.mk HY hHYhol := by
    apply Subtype.ext
    exact hYread (F p) hpY hpU
  apply Subtype.ext
  erw [h.germ_stalkMap_apply]

  rw [hXread p hpX hpU, hYgerm, schemeMorphismNativeGermPullback_mk]
  apply Germ.coe_eq.mpr
  have hcont : Continuous F := schemeComplexPointMap_continuous f h
  filter_upwards [hVX.mem_nhds hpX, hcont.continuousAt.preimage_mem_nhds (hVY.mem_nhds hpY)]
    with q hqX hqY
  have hqU : schemeComplexPointImage f (F q) ∈ U := hVYU hqY
  have ex := congrArg (Germ.valueRingHom : Germ (𝓝 q) ℂ →+* ℂ)
    (hXread q hqX hqU)
  change NativeHolGerm.eval (schemeNativeStalkGerm (h ≫ f) n q
    (X.presheaf.germ (h ⁻¹ᵁ U) (schemeComplexPointImage (h ≫ f) q) hqU (h.app U r))) = HX q at ex
  rw [schemeNativeStalkGerm_eval] at ex
  have ey := congrArg (Germ.valueRingHom : Germ (𝓝 (F q)) ℂ →+* ℂ)
    (hYread (F q) hqY hqU)
  change NativeHolGerm.eval (schemeNativeStalkGerm f m (F q)
    (Y.presheaf.germ U (schemeComplexPointImage f (F q)) hqU r)) = HY (F q) at ey
  rw [schemeNativeStalkGerm_eval] at ey
  change HX q = HY (F q)
  calc
    HX q = schemeComplexPointStalkEval (h ≫ f) q
        (X.presheaf.germ (h ⁻¹ᵁ U) (schemeComplexPointImage (h ≫ f) q) hqU (h.app U r)) := ex.symm
    _ = schemeComplexPointStalkEval f (F q)
        (Y.presheaf.germ U (schemeComplexPointImage f (F q)) hqU r) := by
      erw [← h.germ_stalkMap_apply]
      exact (congrArg (fun k : Y.presheaf.stalk (schemeComplexPointImage f (F q)) →+* ℂ =>
        k (Y.presheaf.germ U (schemeComplexPointImage f (F q)) hqU r))
          (schemeComplexPointStalkEval_comp (h ≫ f) f h rfl q)).symm
    _ = HY (F q) := ey

/-- Equality of the two actual ring maps, with no coefficient-only restriction. -/
theorem schemeNativeStalkGerm_naturality_hom (p : SchemeComplexPoint (h ≫ f)) :
    (schemeNativeStalkGerm (h ≫ f) n p).comp
      (h.stalkMap (schemeComplexPointImage (h ≫ f) p)).hom =
        (schemeMorphismNativeGermPullback f h n m p).comp
          (schemeNativeStalkGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p)) := by
  apply RingHom.ext
  intro a
  exact schemeNativeStalkGerm_naturality f h n m p a

end SGPT.Okounkov
