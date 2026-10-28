import TranscendentalNakamaye.Pending.MultiplierIdealBergmanNadelManifold

set_option autoImplicit false

/-! # Multiplier coherence for an actual raw manifold quasi-PSH weight -/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold

namespace TranscendentalNakamaye.Pending.GlobalQuasiPshMultiplierCoherence

open FirstPass FirstPass.HolomorphicIdealSheaves
  MultiplierIdealBergmanNadelManifold MultiplierIdealBergmanNadelCoherence

noncomputable section

/-- The germ definition internally supplies one simultaneous open PSH decomposition. -/
theorem exists_open_psh_decomposition {n : ℕ} {v : ComplexModel n → EReal}
    {z : ComplexModel n} (hv : QuasiPlurisubharmonicAt v z) :
    ∃ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal)
      (h : ComplexModel n → ℝ),
      IsOpen W ∧ z ∈ W ∧ PlurisubharmonicOn P W ∧ ContinuousOn h W ∧
      ∀ y ∈ W, v y = P y + (h y : EReal) := by
  obtain ⟨P, h, ⟨U, hU, hzU, hP⟩, hh, heq⟩ := hv
  obtain ⟨V, hVsub, hV, hzV⟩ := _root_.mem_nhds_iff.mp (hh.and heq)
  refine ⟨U ∩ V, P, h, hU.inter hV, ⟨hzU, hzV⟩, ?_, ?_, ?_⟩
  · exact fun y hy => ⟨U ∩ V, hU.inter hV, hy, hP.mono inter_subset_left⟩
  · exact fun y hy => (hVsub hy.2).1.continuousAt.continuousWithinAt
  · exact fun y hy => (hVsub hy.2).2


/-- Raw manifold quasi-PSH supplies actual Nadel coherence without a global background. -/
theorem isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    {n : ℕ} (hn : 0 < n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {v : M → EReal} (hv : ManifoldQuasiPlurisubharmonic (n := n) v)
    {c : ℝ} (hc : 0 < c) : (multiplierIdeal (n := n) c v).IsCoherent := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  classical
  intro x
  let e : ComplexChart (m + 1) M := complexChartAt (n := m + 1) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, P, ρ, hW, hxW, hpsh, hρc, heq⟩ :=
    exists_open_psh_decomposition (hv e (e.val x) (e.val.map_source hxe))
  let Ω : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨W, hW⟩
  obtain ⟨r, hr, N, g, hballW, hgd, hgint, hgen⟩ :=
    exists_local_generators (Ω := Ω) (Ψ := P) hpsh hc hxW
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) r, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hxe, mem_ball_self hr⟩, N, fun l p => g l (e.val p), fun l p hp => ?_, fun y hy f => ?_⟩
  · have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (g l) (e.val p) := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hgd l).differentiableAt (isOpen_ball.mem_nhds hp.2)
    exact (hd.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp.1)).mdifferentiableWithinAt
  have hyW : e.val y ∈ W := hballW hy.2
  have hcont : ContinuousAt ρ (e.val y) := (hρc _ hyW).continuousAt (hW.mem_nhds hyW)
  constructor
  · intro hmem
    have husc : UpperSemicontinuousOn (chartFunction v e)
        (ChartWeightedL2.overlapDomain e (complexChartAt (n := m + 1) y)) :=
      (hv e).upperSemicontinuousOn.mono fun _ hw => hw.1
    have hraw : MultiplierIntegrableAt (chartFunction v e) c
        (fun w => f (e.val.symm w)) (e.val y) volume :=
      ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := f)
        e (complexChartAt (n := m + 1) y) hy.1 (mem_complexChartAt_source y)
        husc hc.ne' hmem.2
    have hmore : MoreSingularAt (chartFunction v e) P (e.val y) := by
      refine ⟨ρ (e.val y) + 1, ?_⟩
      filter_upwards [hW.mem_nhds hyW,
        hcont.eventually (gt_mem_nhds (lt_add_one (ρ (e.val y))))] with w hwW hw
      rw [heq w hwW]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hw.le)
    have hPf : MultiplierIntegrableAt P c (fun w => f (e.val.symm w)) (e.val y) volume :=
      multiplierIntegrableAt_of_moreSingularAt (hpsh _ hyW).quasiPlurisubharmonicAt hmore hraw
    obtain ⟨N', s', a, hs', ha, hsum⟩ := hgen (e.val y) hy.2 _ hPf
    choose l hl using hs'
    refine ⟨hmem.1, N', fun i p => s' i (e.val p), fun i p => a i (e.val p),
      fun i => ⟨l i, ?_⟩, fun i => holomorphicAt_comp_chart hy.1 (ha i), ?_⟩
    · funext p
      simp only [hl i]
    · filter_upwards [e.val.open_source.mem_nhds hy.1,
        (e.val.continuousAt hy.1).eventually hsum] with p hp hsumP
      simp only [e.val.left_inv hp] at hsumP
      exact hsumP
  · rintro ⟨hhol, N', s', a', hs', ha', he'⟩
    refine ⟨hhol, ?_⟩
    choose l hl using hs'
    have hsum : MultiplierIntegrableAt P c
        (fun w => ∑ i, a' i (e.val.symm w) * g (l i) w) (e.val y) volume :=
      multiplierIntegrableAt_sum_mul hc (hpsh _ hyW).quasiPlurisubharmonicAt
        (fun i => eventually_differentiableAt_comp_chart_symm hy.1 (ha' i))
        (fun i => hgint (l i) (e.val y) hy.2)
    have hT : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
      have ht := e.val.continuousAt_symm (e.val.map_source hy.1)
      rw [ContinuousAt, e.val.left_inv hy.1] at ht
      exact ht
    have hcomb : (fun w => ∑ i, a' i (e.val.symm w) * g (l i) w) =ᶠ[𝓝 (e.val y)]
        fun w => f (e.val.symm w) := by
      filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hy.1), hT.eventually he']
        with w hw hwe
      rw [hwe]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hl i]
      simp only [e.val.right_inv hw]
    have hPf : MultiplierIntegrableAt P c (fun w => f (e.val.symm w)) (e.val y) volume :=
      hsum.congr (EventuallyEq.refl _ _) hcomb
    have hmore : MoreSingularAt P (chartFunction v e) (e.val y) := by
      obtain ⟨C, hC⟩ := QuantitativeRegularizationChartGermTransfer.moreSingularAt_add_continuous
        (u := P) hW hρc hyW
      refine ⟨C, ?_⟩
      filter_upwards [hC, hW.mem_nhds hyW] with w hw hwW
      rw [heq w hwW]
      exact hw
    have hraw : MultiplierIntegrableAt (chartFunction v e) c (fun w => f (e.val.symm w))
        (e.val y) volume :=
      multiplierIntegrableAt_of_moreSingularAt (hv e _ (e.val.map_source hy.1)) hmore hPf
    have husc : UpperSemicontinuousOn (chartFunction v (complexChartAt (n := m + 1) y))
        (ChartWeightedL2.overlapDomain (complexChartAt (n := m + 1) y) e) :=
      (hv (complexChartAt (n := m + 1) y)).upperSemicontinuousOn.mono fun _ hw => hw.1
    exact ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := f)
      (complexChartAt (n := m + 1) y) e (mem_complexChartAt_source y) hy.1 husc hc.ne' hraw

end
end TranscendentalNakamaye.Pending.GlobalQuasiPshMultiplierCoherence
