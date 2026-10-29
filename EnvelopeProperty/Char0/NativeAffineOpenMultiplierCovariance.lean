import EnvelopeProperty.Char0.NativeAffineOpenJacobian
import EnvelopeProperty.Char0.NativeMultiplierGermTransform
import EnvelopeProperty.ComplexGeometry.Pluripotential.LocalHolomorphicInverse

/-! # Whole native multiplier ideals under the actual original affine-open pullback -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineOpenMultiplierCovariance

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter MeasureTheory
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms HolomorphicGerms.NativeOpenJacobian NativeMultiplierGermTransform
open HolomorphicMaps HironakaHolomorphicJetChartInvariance HolomorphicGermJacobian
open WeightedHolomorphicGermIdealIntegralClosure
open scoped Topology Manifold ContDiff ENNReal

section Scheme

variable {Y Z : Scheme} (fY : Y ⟶ Spec (.of ℂ)) (fZ : Z ⟶ Spec (.of ℂ))
  (j : Z ⟶ Y) (hj : j ≫ fY = fZ) [IsOpenImmersion j] (n : ℕ)
  [SmoothOfRelativeDimension n fY] [SmoothOfRelativeDimension n fZ]
  [IsSeparated fY] [QuasiCompact fY] [IsSeparated fZ] [QuasiCompact fZ]

local instance targetTopology : TopologicalSpace (SchemeComplexPoint fY) :=
  schemeAnalyticPointTopology fY
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint fZ) :=
  schemeAnalyticPointTopology fZ
local instance targetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fY) :=
  schemeAnalyticComplexChartedSpace fY n
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fZ) :=
  schemeAnalyticComplexChartedSpace fZ n
local instance targetManifold : IsComplexManifold n (SchemeComplexPoint fY) :=
  schemeAnalyticComplex_isComplexManifold fY n
local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint fZ) :=
  schemeAnalyticComplex_isComplexManifold fZ n

/-- The actual original open immersion in its SAME preferred centered native charts. -/
def openCoordinateMap (q : SchemeComplexPoint fZ) : ComplexModel n → ComplexModel n :=
  NativeHolGerm.centeredCoordinateMap (schemeComplexPointMap fZ fY j hj) q

omit [IsOpenImmersion j] in
private theorem openCoordinateMap_holomorphic (q : SchemeComplexPoint fZ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (openCoordinateMap fY fZ j hj n q) z :=
  NativeHolGerm.centeredCoordinateMap_holomorphic _
    (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) q

omit [IsOpenImmersion j] [IsSeparated fY] [QuasiCompact fY] [IsSeparated fZ] [QuasiCompact fZ] in
private theorem openCoordinateMap_zero (q : SchemeComplexPoint fZ) :
    openCoordinateMap fY fZ j hj n q 0 = 0 :=
  NativeHolGerm.centeredCoordinateMap_zero _ _

/-- The actual open inverse gives a genuine local holomorphic equivalence with the LITERAL forward map. -/
theorem exists_openLocalHolomorphicEquiv (q : SchemeComplexPoint fZ) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
      Φ.toFun = openCoordinateMap fY fZ j hj n q ∧ Φ.toFun 0 = 0 := by
  have hu := schemeOpenImmersion_jacobianGerm_isUnit fY fZ j hj n q
  have hdet : (fderiv ℂ (openCoordinateMap fY fZ j hj n q) 0).toLinearMap.det ≠ 0 := by
    have hne := (HolGerm.isUnit_iff_eval_ne_zero _).mp hu
    change Germ.valueRingHom ((jacobianGerm _ _ : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) ≠ 0 at hne
    rw [jacobianGerm_source] at hne
    exact hne
  have hinj : Function.Injective (fderiv ℂ (openCoordinateMap fY fZ j hj n q) 0) := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.mp
    (openCoordinateMap_holomorphic fY fZ j hj n q)
  obtain ⟨Φ, _, hfun, _⟩ := exists_localHolomorphicEquivAt hUo h0U
    (fun z hz => (hU hz).differentiableWithinAt) hinj
  exact ⟨Φ, hfun, by rw [hfun, openCoordinateMap_zero]⟩

omit [IsOpenImmersion j] [IsSeparated fY] [QuasiCompact fY] [IsSeparated fZ] [QuasiCompact fZ] in
private theorem centeredWeight_openMap_eventually
    (w : SchemeComplexPoint fY → EReal) (q : SchemeComplexPoint fZ) :
    centeredWeight (fun z => w (schemeComplexPointMap fZ fY j hj z)) q =ᶠ[𝓝 (0 : ComplexModel n)]
      fun z => centeredWeight w (schemeComplexPointMap fZ fY j hj q)
        (openCoordinateMap fY fZ j hj n q z) := by
  let b := schemeComplexPointMap fZ fY j hj
  let e := complexChartAt (n := n) q
  let d := complexChartAt (n := n) (b q)
  have hb := schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞
  have ha : Tendsto (fun z : ComplexModel n => z + e.val q) (𝓝 0) (𝓝 (e.val q)) := by
    simpa only [zero_add] using (continuous_add_const (e.val q)).tendsto (0 : ComplexModel n)
  have hnear := ha.eventually ((coordinateDomain_isOpen hb e d).mem_nhds
    (mem_coordinateDomain (mem_complexChartAt_source q) (mem_complexChartAt_source (b q))))
  filter_upwards [hnear] with z hz
  change w (b (e.val.symm (z + e.val q))) =
    w (d.val.symm ((d.val (b (e.val.symm (z + e.val q))) - d.val (b q)) + d.val (b q)))
  rw [sub_add_cancel, d.val.left_inv hz.2]

/-- Literal volume integrability is preserved by the ACTUAL original open map, for every test function. -/
theorem multiplierIntegrableAt_openCoordinates_iff
    {w : SchemeComplexPoint fY → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    (q : SchemeComplexPoint fZ) (G : ComplexModel n → ℂ) (c : ℝ) :
    MultiplierIntegrableAt (centeredWeight w (schemeComplexPointMap fZ fY j hj q)) c G 0 volume ↔
      MultiplierIntegrableAt (centeredWeight (fun z => w (schemeComplexPointMap fZ fY j hj z)) q)
        c (G ∘ openCoordinateMap fY fZ j hj n q) 0 volume := by
  obtain ⟨Φ, hfun, h0⟩ := exists_openLocalHolomorphicEquiv fY fZ j hj n q
  have hb := schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞
  have hwS := centeredWeight_quasiPSH
    (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hb hw) q
  have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    (f := G ∘ openCoordinateMap fY fZ j hj n q) (c := c) Φ hwS
  rw [h0] at hcov
  have hInv : Tendsto Φ.invFun (𝓝 (0 : ComplexModel n)) (𝓝 0) := by
    simpa only [local_invFun_zero Φ h0] using
      (local_invFun_holomorphic Φ h0).self_of_nhds.continuousAt.tendsto
  have h0tar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hright : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      openCoordinateMap fY fZ j hj n q (Φ.invFun z) = z := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0tar] with z hz
    rw [← hfun]
    exact Φ.right_inv z hz
  have hwEq := (centeredWeight_openMap_eventually fY fZ j hj n w q).comp_tendsto hInv
  have hweight : (fun z => centeredWeight
      (fun a => w (schemeComplexPointMap fZ fY j hj a)) q (Φ.invFun z)) =ᶠ[𝓝 (0 : ComplexModel n)]
      centeredWeight w (schemeComplexPointMap fZ fY j hj q) := by
    filter_upwards [hwEq, hright] with z hz hr
    exact hz.trans (congrArg (centeredWeight w (schemeComplexPointMap fZ fY j hj q)) hr)
  have htest : (fun z => (G ∘ openCoordinateMap fY fZ j hj n q) (Φ.invFun z)) =ᶠ[𝓝 (0 : ComplexModel n)] G :=
    hright.mono fun z hz => congrArg G hz
  exact ⟨fun h => hcov.mp (h.congr hweight.symm htest.symm),
    fun h => (hcov.mpr h).congr hweight htest⟩

/-- Every WHOLE holomorphic germ retains multiplier membership under the SAME actual open pullback. -/
theorem weightedGermIdeal_openPullback_iff
    {w : SchemeComplexPoint fY → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    {c : ℝ} (hc : 0 < c) (q : SchemeComplexPoint fZ) (g : HolGerm (ComplexModel n)) :
    g ∈ weightedGermIdeal hc
      (centeredWeight_quasiPSH hw (schemeComplexPointMap fZ fY j hj q)) volume ↔
      compAlgHom (openCoordinateMap fY fZ j hj n q)
        (openCoordinateMap_holomorphic fY fZ j hj n q) (openCoordinateMap_zero fY fZ j hj n q) g ∈
        weightedGermIdeal hc
          (centeredWeight_quasiPSH (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
            (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) hw) q) volume := by
  obtain ⟨G, hG, rfl⟩ := HolGerm.exists_eq_mk g
  rw [compAlgHom_mk]
  rw [mem_weightedGermIdeal_iff_source hc
    (centeredWeight_quasiPSH hw (schemeComplexPointMap fZ fY j hj q)) _ G rfl]
  rw [mem_weightedGermIdeal_iff_source hc
    (centeredWeight_quasiPSH (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) hw) q) _
      (G ∘ openCoordinateMap fY fZ j hj n q) rfl]
  exact multiplierIntegrableAt_openCoordinates_iff fY fZ j hj n hw q G c

/-- The ENTIRE original native multiplier ideal is preserved by the actual native open-immersion germ map. -/
theorem nativeMultiplierIdeal_openPullback_iff
    {w : SchemeComplexPoint fY → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    {c : ℝ} (hc : 0 < c) (q : SchemeComplexPoint fZ)
    (g : NativeHolGerm n (SchemeComplexPoint fY) (schemeComplexPointMap fZ fY j hj q)) :
    g ∈ nativeMultiplierIdeal hw c hc (schemeComplexPointMap fZ fY j hj q) ↔
      NativeHolGerm.comap (schemeComplexPointMap fZ fY j hj)
        (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) q g ∈
        nativeMultiplierIdeal (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
          (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) hw) c hc q := by
  change NativeHolGerm.chartEquiv _ g ∈ weightedGermIdeal hc
      (centeredWeight_quasiPSH hw (schemeComplexPointMap fZ fY j hj q)) volume ↔
    NativeHolGerm.chartEquiv _ _ ∈ weightedGermIdeal hc
      (centeredWeight_quasiPSH (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
        (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) hw) q) volume
  rw [NativeHolGerm.chartEquiv_comap]
  exact weightedGermIdeal_openPullback_iff fY fZ j hj n hw hc q _

/-- Equality of WHOLE actual native ideals under the original open pullback, in every dimension. -/
theorem nativeMultiplierIdeal_eq_comap_openPullback
    {w : SchemeComplexPoint fY → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    {c : ℝ} (hc : 0 < c) (q : SchemeComplexPoint fZ) :
    nativeMultiplierIdeal hw c hc (schemeComplexPointMap fZ fY j hj q) =
      (nativeMultiplierIdeal (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
        (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) hw) c hc q).comap
        (NativeHolGerm.comap (schemeComplexPointMap fZ fY j hj)
          (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) q) := by
  ext g
  exact nativeMultiplierIdeal_openPullback_iff fY fZ j hj n hw hc q g

end Scheme

section AffineSource

variable {B : Type} [CommRing B] {Y : Scheme}
  (f : Y ⟶ Spec (.of ℂ)) (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

private instance affineSourceSmooth : SmoothOfRelativeDimension n (j ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := j) (n := 0) (m := n) f)

local instance affineSourceStructuralAffine : IsAffineHom (j ≫ f) := isAffineHom_of_isAffine _
local instance affineTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance affineSourceTopology : TopologicalSpace (SchemeComplexPoint (j ≫ f)) :=
  schemeAnalyticPointTopology (j ≫ f)
local instance affineTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance affineSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (j ≫ f)) :=
  schemeAnalyticComplexChartedSpace (j ≫ f) n
local instance affineTargetManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n
local instance affineSourceManifold : IsComplexManifold n (SchemeComplexPoint (j ≫ f)) :=
  schemeAnalyticComplex_isComplexManifold (j ≫ f) n

/-- The original affine open INTERNALLY supplies all source geometric inputs for whole native covariance. -/
theorem schemeNativeMultiplierIdeal_affineOpen_iff
    {w : SchemeComplexPoint f → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    {c : ℝ} (hc : 0 < c) (q : SchemeComplexPoint (j ≫ f))
    (g : NativeHolGerm n (SchemeComplexPoint f) (schemeComplexPointMap (j ≫ f) f j rfl q)) :
    g ∈ nativeMultiplierIdeal hw c hc (schemeComplexPointMap (j ≫ f) f j rfl q) ↔
      schemeMorphismNativeGermPullback f j n n q g ∈
        nativeMultiplierIdeal (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
          (schemeComplexPointMap_contMDiff f j n n ∞) hw) c hc q :=
  nativeMultiplierIdeal_openPullback_iff f (j ≫ f) j rfl n hw hc q g

/-- The WHOLE ideal equality for the literal original scheme-morphism native pullback. -/
theorem schemeNativeMultiplierIdeal_eq_comap_affineOpen
    {w : SchemeComplexPoint f → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    {c : ℝ} (hc : 0 < c) (q : SchemeComplexPoint (j ≫ f)) :
    nativeMultiplierIdeal hw c hc (schemeComplexPointMap (j ≫ f) f j rfl q) =
      (nativeMultiplierIdeal (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
        (schemeComplexPointMap_contMDiff f j n n ∞) hw) c hc q).comap
        (schemeMorphismNativeGermPullback f j n n q) := by
  ext g
  exact schemeNativeMultiplierIdeal_affineOpen_iff f j n hw hc q g

end AffineSource

end EnvelopeProperty.Char0.NativeAffineOpenMultiplierCovariance
