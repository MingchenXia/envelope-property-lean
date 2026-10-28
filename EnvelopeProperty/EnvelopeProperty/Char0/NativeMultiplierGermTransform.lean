import SGPT.Okounkov.NativeHolomorphicGermCoordinates
import TranscendentalNakamaye.Pending.AnalyticModificationJacobianMultiplierGerms
import TranscendentalNakamaye.Pending.ManifoldAdaptedMultiplierGermTransport
import TranscendentalNakamaye.Pending.WeightedHolomorphicGermIdealIntegralClosure
import TranscendentalNakamaye.Pending.ZeroDimensionalQuasiPshMultiplierIdeals
import TranscendentalNakamaye.Pending.HolomorphicGermJacobian

/-! # Whole native multiplier germs under the same actual analytic modification -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace EnvelopeProperty.Char0.NativeMultiplierGermTransform

open Set Filter MeasureTheory SGPT.Okounkov
open TranscendentalNakamaye TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open HolomorphicIdealSheaves HolomorphicMaps DivisorialChangeOfVariables HolomorphicGermJacobian
open AnalyticModificationLocalDiscrepancy WeightedHolomorphicGermIdealIntegralClosure
open scoped Topology Manifold ContDiff ENNReal

section Positive
variable {m : ℕ} {X Y : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]
  {π : Y → X}

/-- The arbitrary ORIGINAL holomorphic test is transformed over every point of the same fibre. -/
theorem multiplierIdeal_mem_iff_fiber_positive (hπ : IsAnalyticModification (n := m+1) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m+1) u)
    {c : ℝ} (hc : 0 < c) (x : X) (F : X → ℂ) (hF : HolomorphicAt (m+1) F x) :
    (multiplierIdeal (n := m+1) c u).mem x F ↔
      ∀ y : Y, π y = x → MultiplierIntegrableAt
        (chartFunction (fun q => u (π q)) (complexChartAt (n := m+1) y)) c
        (fun z => F (π ((complexChartAt (n := m+1) y).val.symm z)) *
          complexJacobian (coordinateMap π (complexChartAt (n := m+1) y)
            (complexChartAt (n := m+1) x)) z)
        ((complexChartAt (n := m+1) y).val y) volume := by
  let d := complexChartAt (n := m+1) x
  let g : ComplexModel (m+1) → ℂ := fun z => F (d.val.symm z)
  have hg : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ g z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source (n := m+1) x) hF
  have hw := hu d (d.val x) (d.val.map_source (mem_complexChartAt_source x))
  have hbase := AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x hc hw hg
  change (HolomorphicAt (m+1) F x ∧ _) ↔ _
  rw [and_iff_right hF]
  refine hbase.trans (forall_congr' fun y => forall_congr' fun hy => ?_)
  let e := complexChartAt (n := m+1) y
  have hD := coordinateDomain_isOpen hπ.1 e d
  have hyD : e.val y ∈ coordinateDomain π e d := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hy]
    exact mem_complexChartAt_source x
  have hweight : (fun z => chartFunction u d (coordinateMap π e d z)) =ᶠ[𝓝 (e.val y)]
      chartFunction (fun q => u (π q)) e := by
    filter_upwards [hD.mem_nhds hyD] with z hz
    exact congrArg u (d.val.left_inv hz.2)
  have htest : (fun z => g (coordinateMap π e d z) * complexJacobian (coordinateMap π e d) z)
      =ᶠ[𝓝 (e.val y)] fun z => F (π (e.val.symm z)) * complexJacobian (coordinateMap π e d) z := by
    filter_upwards [hD.mem_nhds hyD] with z hz
    exact congrArg (fun q => F q * complexJacobian (coordinateMap π e d) z) (d.val.left_inv hz.2)
  exact ⟨fun h => h.congr hweight htest,fun h => h.congr hweight.symm htest.symm⟩
end Positive

section AnyDimension
variable {n : ℕ} {X Y : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {π : Y → X}

private theorem potential_ne_bot_dim_zero {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := 0) u) (x : X) : u x ≠ ⊥ := by
  let e := complexChartAt (n := 0) x
  obtain ⟨y,hy,hfin⟩ := hu.2 x e.val.source e.val.open_source (mem_complexChartAt_source x)
  have he : y = x := e.val.injOn hy (mem_complexChartAt_source x) (Subsingleton.elim _ _)
  simpa only [he] using hfin

/-- All dimensions, with the actual zero-dimensional full-stalk case proved separately. -/
theorem multiplierIdeal_mem_iff_fiber (hπ : IsAnalyticModification (n := n) π)
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) (x : X) (F : X → ℂ) (hF : HolomorphicAt n F x) :
    (multiplierIdeal (n := n) c u).mem x F ↔
      ∀ y : Y, π y = x → MultiplierIntegrableAt
        (chartFunction (fun q => u (π q)) (complexChartAt (n := n) y)) c
        (fun z => F (π ((complexChartAt (n := n) y).val.symm z)) *
          complexJacobian (coordinateMap π (complexChartAt (n := n) y)
            (complexChartAt (n := n) x)) z)
        ((complexChartAt (n := n) y).val y) volume := by
  cases n with
  | succ m => exact multiplierIdeal_mem_iff_fiber_positive hπ hu.1 hc x F hF
  | zero =>
    have hpull : IsGlobalQuasiPshPotential (n := 0) (fun q => u (π q)) :=
      ⟨GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu.1,
        fun y U _ hy => ⟨y,hy,potential_ne_bot_dim_zero hu (π y)⟩⟩
    have htarget := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hu hc x F).mpr hF
    refine iff_of_true htarget ?_
    intro y _
    let e := complexChartAt (n := 0) y
    let T : ComplexModel 0 → ℂ := fun z => F (π (e.val.symm z)) *
      complexJacobian (coordinateMap π e (complexChartAt (n := 0) x)) z
    have hsource := ((ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hpull hc y (fun _ => T (e.val y))).mpr (holomorphicAt_const _)).2
    have hT : (fun _ : ComplexModel 0 => T (e.val y)) = T := by
      funext z
      exact congrArg T (Subsingleton.elim _ _)
    change MultiplierIntegrableAt (chartFunction (fun q => u (π q)) e) c
      (fun _ => T (e.val y)) (e.val y) volume at hsource
    rw [hT] at hsource
    exact hsource

/-- The weight in the actual centered preferred chart, retaining all poles. -/
def centeredWeight (u : X → EReal) (x : X) (z : ComplexModel n) : EReal :=
  u ((complexChartAt (n := n) x).val.symm (z + (complexChartAt (n := n) x).val x))

/-- Quasi-PSH regularity in the actual centered coordinates follows from the original function. -/
theorem centeredWeight_quasiPSH {u : X → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (x : X) :
    QuasiPlurisubharmonicAt (centeredWeight (n := n) u x) 0 := by
  let e := complexChartAt (n := n) x
  have hw := hu e (e.val x) (e.val.map_source (mem_complexChartAt_source x))
  have h := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
    (u := chartFunction u e) (F := fun z : ComplexModel n => z + e.val x) isOpen_univ
    ((contDiff_id.add contDiff_const).contDiffOn :
      ContDiffOn ℂ ∞ (fun z : ComplexModel n => z + e.val x) Set.univ)
    (Set.mem_univ (0 : ComplexModel n)) (by simpa only [zero_add] using hw)
  exact h

/-- The whole original native multiplier ideal is the inverse image of the genuine weighted germ ideal. -/
def nativeMultiplierIdeal {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (c : ℝ) (hc : 0 < c) (x : X) : Ideal (NativeHolGerm n X x) :=
  (weightedGermIdeal (φ := centeredWeight (n := n) u x) hc (centeredWeight_quasiPSH hu x) volume).comap
    (NativeHolGerm.chartEquiv x).toRingHom

/-- An actual whole-germ readback reads the literal multiplier integral without an extra holomorphy certificate. -/
theorem mem_weightedGermIdeal_iff_source {φ : ComplexModel n → EReal} {c : ℝ}
    (hc : 0 < c) (hφ : QuasiPlurisubharmonicAt φ 0) (g : HolGerm (ComplexModel n))
    (F : ComplexModel n → ℂ)
    (hsource : (g : Germ (𝓝 (0 : ComplexModel n)) ℂ) = (F : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    g ∈ weightedGermIdeal hc hφ volume ↔ MultiplierIntegrableAt φ c F 0 volume := by
  constructor
  · rintro ⟨G,hG,heq,hint⟩
    have hGF : G =ᶠ[𝓝 (0 : ComplexModel n)] F :=
      Germ.coe_eq.mp ((congrArg (fun a : HolGerm (ComplexModel n) =>
        (a : Germ (𝓝 (0 : ComplexModel n)) ℂ)) heq).trans hsource)
    exact hint.congr EventuallyEq.rfl hGF
  · intro hint
    have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z := by
      obtain ⟨_,U,hU,h0,hhol,_⟩ := hint
      filter_upwards [hU.mem_nhds h0] with z hz
      exact (hhol z hz).differentiableAt (hU.mem_nhds hz)
    refine ⟨F,hF,?_,hint⟩
    apply Subtype.ext
    exact hsource.symm

/-- Every original native holomorphic function germ has its literal multiplier-ideal membership. -/
theorem nativeMultiplierIdeal_mem_mk_iff {u : X → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) {c : ℝ} (hc : 0 < c)
    (x : X) (F : X → ℂ) (hF : HolomorphicAt n F x) :
    NativeHolGerm.mk F hF ∈ nativeMultiplierIdeal hu c hc x ↔
      (multiplierIdeal (n := n) c u).mem x F := by
  change NativeHolGerm.chartEquiv x (NativeHolGerm.mk F hF) ∈
    weightedGermIdeal hc (centeredWeight_quasiPSH hu x) volume ↔ _
  rw [mem_weightedGermIdeal_iff_source hc (centeredWeight_quasiPSH hu x) _ _
    (NativeHolGerm.chartEquiv_mk F hF)]
  let e := complexChartAt (n := n) x
  have ht := ManifoldAdaptedMultiplierGermTransport.multiplierIdeal_mem_comp_adapted_iff
    x (HironakaHolomorphicJetRankLoci.translationEquiv (e.val x))
    (show (HironakaHolomorphicJetRankLoci.translationEquiv (e.val x)).toFun (e.val x) = 0 by
      simp [HironakaHolomorphicJetRankLoci.translationEquiv]) hu hF c
  exact ht.symm

/-- Literal Jacobian-weighted pullback test in the actual centered source coordinates. -/
def centeredPullbackTest (π : Y → X) (F : X → ℂ) (y : Y) (z : ComplexModel n) : ℂ :=
  F (π ((complexChartAt (n := n) y).val.symm (z + (complexChartAt (n := n) y).val y))) *
    complexJacobian (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) π y) z

/-- The canonical entire native pullback, multiplied by the Jacobian of the same actual centered map. -/
def jacobianWeightedPullback (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (y : Y) (g : NativeHolGerm n X (π y)) : HolGerm (ComplexModel n) :=
  NativeHolGerm.chartEquiv y (NativeHolGerm.comap π hπ y g) *
    jacobianGerm (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) π y)
      (NativeHolGerm.centeredCoordinateMap_holomorphic π hπ y)

/-- The WHOLE product germ is exactly the literal original pulled function times the SAME actual Jacobian. -/
theorem jacobianWeightedPullback_source (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (y : Y) (F : X → ℂ) (hF : HolomorphicAt n F (π y)) :
    ((jacobianWeightedPullback π hπ y (NativeHolGerm.mk F hF) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = (centeredPullbackTest (n := n) π F y : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  change ((NativeHolGerm.chartEquiv y (NativeHolGerm.mk (F ∘ π)
    (hF.comp_contMDiff (Eventually.of_forall fun q => hπ q))) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) *
    ((jacobianGerm _ _ : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [NativeHolGerm.chartEquiv_mk,jacobianGerm_source]
  rfl

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
/-- The actual centered Jacobian is the translated SAME preferred coordinate Jacobian. -/
theorem centeredJacobian_apply (π : Y → X) (y : Y) (z : ComplexModel n) :
    complexJacobian (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) π y) z =
      complexJacobian (coordinateMap π (complexChartAt (n := n) y)
        (complexChartAt (n := n) (π y))) (z + (complexChartAt (n := n) y).val y) := by
  unfold NativeHolGerm.centeredCoordinateMap complexJacobian
  rw [fderiv_sub_const,fderiv_comp_add_right]

/-- The arbitrary original test satisfies the SAME all-fibre criterion in actual centered source coordinates. -/
theorem multiplierIdeal_mem_iff_fiber_centered (hπ : IsAnalyticModification (n := n) π)
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) (x : X) (F : X → ℂ) (hF : HolomorphicAt n F x) :
    (multiplierIdeal (n := n) c u).mem x F ↔
      ∀ y : Y, π y = x → MultiplierIntegrableAt (centeredWeight (n := n) (fun q => u (π q)) y) c
        (centeredPullbackTest (n := n) π F y) 0 volume := by
  refine (multiplierIdeal_mem_iff_fiber hπ hu hc x F hF).trans
    (forall_congr' fun y => forall_congr' fun hy => ?_)
  subst x
  let e := complexChartAt (n := n) y
  have hw := (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu.1)
    e (e.val y) (e.val.map_source (mem_complexChartAt_source y))
  have ht := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    (HironakaHolomorphicJetRankLoci.translationEquiv (e.val y))
    (f := fun z => F (π (e.val.symm z)) *
      complexJacobian (coordinateMap π e (complexChartAt (n := n) (π y))) z) (c := c) hw
  change _ ↔ MultiplierIntegrableAt
    (fun z => u (π (e.val.symm (z + e.val y)))) c
    (fun z => F (π (e.val.symm (z + e.val y))) *
      complexJacobian (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) π y) z) 0 volume
  simp_rw [centeredJacobian_apply]
  simpa only [HironakaHolomorphicJetRankLoci.translationEquiv,sub_self,chartFunction,e] using ht.symm

/-- Transport along the genuine original fibre equality only changes the point index. -/
def fiberGerm {x : X} (g : NativeHolGerm n X x) (y : Y) (hy : π y = x) :
    NativeHolGerm n X (π y) := hy.symm ▸ g

/-- Entire arbitrary native multiplier germs are detected by their ACTUAL Jacobian-weighted pullbacks
at EVERY point of the SAME original modification fibre, in every dimension. -/
theorem nativeMultiplierIdeal_mem_iff_fiber (hπ : IsAnalyticModification (n := n) π)
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) (x : X) (g : NativeHolGerm n X x) :
    g ∈ nativeMultiplierIdeal hu.1 c hc x ↔
      ∀ (y : Y) (hy : π y = x),
        jacobianWeightedPullback π hπ.1 y (fiberGerm (n := n) g y hy) ∈
          weightedGermIdeal hc
            (centeredWeight_quasiPSH
              (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu.1) y) volume := by
  obtain ⟨F,hF,rfl⟩ := NativeHolGerm.exists_eq_mk (n := n) g
  rw [nativeMultiplierIdeal_mem_mk_iff hu.1 hc x F hF]
  refine (multiplierIdeal_mem_iff_fiber_centered hπ hu hc x F hF).trans
    (forall_congr' fun y => forall_congr' fun hy => ?_)
  subst x
  exact (mem_weightedGermIdeal_iff_source hc
    (centeredWeight_quasiPSH
      (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu.1) y)
    _ _ (jacobianWeightedPullback_source π hπ.1 y F hF)).symm

end AnyDimension
end EnvelopeProperty.Char0.NativeMultiplierGermTransform
