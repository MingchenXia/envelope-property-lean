import TranscendentalNakamaye.Pending.MultiplierSubadditivityLocal
import TranscendentalNakamaye.Pending.GlobalQuasiPshMultiplierCoherence
import TranscendentalNakamaye.Pending.SNCCoordinateUnitCorrection
import TranscendentalNakamaye.Pending.PositiveCurrentTraceMultiplier
import TranscendentalNakamaye.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

/-!
# Analytic multiplier subadditivity for independent quasi-PSH weights

This reuses the local DEL proof used by SGPT. All products below are actual
holomorphic germ ideal products. The comparison with the characteristic-zero
algebraic `schemeMultiplierIdealSheaf` is a separate, still open theorem.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.AnalyticMultiplierSubadditivity

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open TranscendentalNakamaye TranscendentalNakamaye.FirstPass
open TranscendentalNakamaye.FirstPass.HolomorphicIdealSheaves
open TranscendentalNakamaye.Pending
open MultiplierIdealBergmanNadelIdeal MultiplierIdealBergmanNadelManifold

/-- DEL for two independent raw quasi-PSH germs, retaining the original
factors and their finite holomorphic combination. -/
theorem inGermSpan_mul_of_quasiPlurisubharmonicAt
    {m : ℕ} {u v : ComplexModel (m + 1) → EReal} {z : ComplexModel (m + 1)}
    (hu : QuasiPlurisubharmonicAt u z) (hv : QuasiPlurisubharmonicAt v z)
    {f : ComplexModel (m + 1) → ℂ}
    (hf : MultiplierIntegrableAt (fun y => u y + v y) 1 f z volume) :
    InGermSpan {g | ∃ a b, MultiplierIntegrableAt u 1 a z volume ∧
      MultiplierIntegrableAt v 1 b z volume ∧ g = fun y => a y * b y} z f := by
  obtain ⟨U, P, r, hU, hzU, hP, hr, hEqU⟩ :=
    GlobalQuasiPshMultiplierCoherence.exists_open_psh_decomposition hu
  obtain ⟨V, Q, s, hV, hzV, hQ, hs, hEqV⟩ :=
    GlobalQuasiPshMultiplierCoherence.exists_open_psh_decomposition hv
  have hr' : ∀ᶠ y in 𝓝 z, ContinuousAt r y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact (hr y hy).continuousAt (hU.mem_nhds hy)
  have hs' : ∀ᶠ y in 𝓝 z, ContinuousAt s y := by
    filter_upwards [hV.mem_nhds hzV] with y hy
    exact (hs y hy).continuousAt (hV.mem_nhds hy)
  have hsumEq : (fun y => u y + v y) =ᶠ[𝓝 z]
      fun y => (P y + Q y) + ((r y + s y : ℝ) : EReal) := by
    filter_upwards [hU.mem_nhds hzU, hV.mem_nhds hzV] with y hyU hyV
    rw [hEqU y hyU, hEqV y hyV, EReal.coe_add]
    ac_rfl
  have hfPQ : MultiplierIntegrableAt (fun y => P y + Q y) 1 f z volume :=
    (SNCCoordinateUnitCorrection.multiplierIntegrableAt_add_continuous_iff
      (hr'.and hs' |>.mono fun y hy => hy.1.add hy.2)).mp
        (hf.congr hsumEq EventuallyEq.rfl)
  obtain ⟨N, g, a, hg, ha, heq⟩ :=
    MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt
      (hU.inter hV) (hP.mono inter_subset_left) (hQ.mono inter_subset_right)
      ⟨hzU, hzV⟩ hfPQ
  refine ⟨N, g, a, ?_, ha, heq⟩
  intro i
  obtain ⟨p, q, hp, hq, hgEq⟩ := hg i
  refine ⟨p, q, ?_, ?_, hgEq⟩
  · have h := (SNCCoordinateUnitCorrection.multiplierIntegrableAt_add_continuous_iff hr').mpr hp
    apply h.congr ?_ EventuallyEq.rfl
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact (hEqU y hy).symm
  · have h := (SNCCoordinateUnitCorrection.multiplierIntegrableAt_add_continuous_iff hs').mpr hq
    apply h.congr ?_ EventuallyEq.rfl
    filter_upwards [hV.mem_nhds hzV] with y hy
    exact (hEqV y hy).symm

private theorem multiplierIdeal_sum_le_mul_pos
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) :
    (multiplierIdeal (n := m + 1) 1 (fun y => u y + v y)).Le
      ((multiplierIdeal (n := m + 1) 1 u).mul (multiplierIdeal (n := m + 1) 1 v)) := by
  intro x f hf
  let e : ComplexChart (m + 1) M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz := e.val.map_source hx
  obtain ⟨N, s, a, hs, ha, heq⟩ :=
    inGermSpan_mul_of_quasiPlurisubharmonicAt (hu e _ hz) (hv e _ hz) hf.2
  choose p q hp hq hsp using hs
  have hmem (w : M → EReal) (t : ComplexModel (m + 1) → ℂ)
      (ht : MultiplierIntegrableAt (chartFunction w e) 1 t (e.val x) volume) :
      (multiplierIdeal (n := m + 1) 1 w).mem x (fun y => t (e.val y)) := by
    have htD : ∀ᶠ y in 𝓝 (e.val x), DifferentiableAt ℂ t y := by
      obtain ⟨_, W, hW, hzW, htd, -⟩ := ht
      filter_upwards [hW.mem_nhds hzW] with y hy
      exact htd.differentiableAt (hW.mem_nhds hy)
    refine ⟨holomorphicAt_comp_chart hx htD, ?_⟩
    apply ht.congr EventuallyEq.rfl
    filter_upwards [e.val.open_target.mem_nhds hz] with y hy
    rw [e.val.right_inv hy]
  refine ⟨hf.1, N, fun i y => p i (e.val y) * q i (e.val y),
    fun i y => a i (e.val y),
    fun i => ⟨_, _, hmem u (p i) (hp i), hmem v (q i) (hq i), rfl⟩,
    fun i => holomorphicAt_comp_chart hx (ha i), ?_⟩
  filter_upwards [e.val.open_source.mem_nhds hx, (e.val.continuousAt hx).eventually heq]
    with y hy heqy
  rw [e.val.left_inv hy] at heqy
  rw [heqy]
  exact Finset.sum_congr rfl fun i _ => by rw [hsp i]

/-- Full analytic ideal-sheaf inclusion for independent genuine quasi-PSH
potentials, including dimension zero and the empty manifold. -/
theorem multiplierIdeal_sum_le_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    (multiplierIdeal (n := n) 1 (fun y => u y + v y)).Le
      ((multiplierIdeal (n := n) 1 u).mul (multiplierIdeal (n := n) 1 v)) := by
  cases n with
  | succ m => exact multiplierIdeal_sum_le_mul_pos hu.1 hv.1
  | zero =>
    intro x f hf
    have hfu := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hu one_pos x f).mpr hf.1
    have h1v := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hv one_pos x (fun _ => 1)).mpr (holomorphicAt_const 1)
    refine ⟨hf.1, 1, fun _ => f, fun _ _ => 1, ?_,
      fun _ => holomorphicAt_const 1, Eventually.of_forall fun _ => by simp⟩
    intro _
    refine ⟨f, fun _ => 1, hfu, h1v, ?_⟩
    funext y
    simp

end EnvelopeProperty.Char0.AnalyticMultiplierSubadditivity
