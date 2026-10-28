import TranscendentalNakamaye.Pending.MultiplierIdeals
import TranscendentalNakamaye.Pending.IEnvelopeStrongOpenness
import TranscendentalNakamaye.Pending.PshConvexCone
import TranscendentalNakamaye.Pending.DemaillyApproximation

set_option autoImplicit false

/-!
# Maxima of I-equivalent potentials

Xia, Proposition 3.2.3 (`xia-sgpt:page-0139`), in the case used for Proposition 3.2.6:
if `u ∼_I φ` and `v ∼_I φ` then `max(u, v) ∼_I φ`.  The source derives this from the
valuative characterization of multiplier ideals.  Here it is proved analytically.

Fix a chart point `z` and `f ∈ I(c max(u, v))_z`.  Strong openness puts `f` in
`I(c(1+δ) max(u, v))_z` for some `δ > 0` (`exists_multiplierIntegrableAt_mul`).  Take
`m ≥ c(1+δ)/δ`.  Demailly's approximation gives holomorphic `g_l`, square integrable
against `e^{-mv}`, with `e^{mv} ≤ C Σ |g_l|²` near `z`; since `I(mv) = I(mu)` at every
nearby point, a compactness argument makes the `g_l` square integrable against `e^{-mu}`
(`exists_ball_weightedL2On`).  The elementary inequality

  `e^{-cs} ≤ e^{-c(1+δ) max(s,t)} + 2 + e^{mt} e^{-ms}`

(`real_exp_le_max_add`) then bounds `|f|² e^{-cu}` by an integrable function
(`multiplierIntegrableAt_of_max_of_generators`).  Smooth local potentials transport
everything to plurisubharmonic chart functions (`multiplierIntegrableAt_of_max_chart`).

Both analytic inputs are proved: strong openness (`Pending.StrongOpennessRegularRoute`) and
Demailly's approximation (`DemaillyApproximation.exists_weightedL2_generators`), so
`iEquivalentMaxClosed` holds unconditionally.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace TranscendentalNakamaye.Pending.IEquivalentMax

/-- The exponent inequality behind the max-closure of I-equivalence:
`e^{-cs} ≤ e^{-c(1+δ) max(s,t)} + 2 + e^{m t} e^{-m s}` once `c(1+δ)/δ ≤ m`. -/
theorem real_exp_le_max_add {c δ m : ℝ} (hδ : 0 < δ) (hm : c * (1 + δ) / δ ≤ m)
    (s t : ℝ) :
    Real.exp (-(c * s)) ≤
      Real.exp (-(c * (1 + δ) * max s t)) + 2 + Real.exp (m * t) * Real.exp (-(m * s)) := by
  have h0 : 0 ≤ Real.exp (-(c * (1 + δ) * max s t)) := (Real.exp_pos _).le
  have h1 : 0 ≤ Real.exp (m * t) * Real.exp (-(m * s)) := by positivity
  set w := max s t with hw
  by_cases hT : c * (w - s) ≤ δ * (-(c * w))
  · have : -(c * s) ≤ -(c * (1 + δ) * w) := by nlinarith
    have := Real.exp_le_exp.mpr this
    linarith
  · replace hT := not_le.mp hT
    have hq : -(c * s) < c * (1 + δ) / δ * (w - s) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hδ]
      nlinarith
    rcases le_total s t with hst | hts
    · have hwt : w = t := max_eq_right hst
      have hts' : 0 ≤ t - s := by linarith
      have : -(c * s) ≤ m * t + -(m * s) := by
        have := mul_le_mul_of_nonneg_right hm hts'
        rw [hwt] at hq
        nlinarith
      have := Real.exp_le_exp.mpr this
      rw [Real.exp_add] at this
      linarith
    · have hws : w = s := max_eq_left hts
      rw [hws, sub_self, mul_zero] at hq
      have : Real.exp (-(c * s)) ≤ 1 := Real.exp_le_one_iff.mpr hq.le
      linarith

/-- The same inequality for multiplier weights of extended-real values; `a ≠ ⊤`
as for every quasi-plurisubharmonic value. -/
theorem multiplierWeight_le_max_add {c δ m : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hm : c * (1 + δ) / δ ≤ m) {a b : EReal} (ha : a ≠ ⊤) :
    multiplierWeight c a ≤
      multiplierWeight (c * (1 + δ)) (max a b) + 2 +
        EReal.exp ((m : EReal) * b) * multiplierWeight m a := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hcδ : 0 < c * (1 + δ) := by positivity
  induction a using EReal.rec with
  | bot =>
    rw [multiplierWeight_bot hc]
    induction b using EReal.rec with
    | bot => simp [multiplierWeight_bot hcδ]
    | coe t =>
      have hpos : EReal.exp ((m : EReal) * (t : EReal)) ≠ 0 := by
        rw [← EReal.coe_mul, EReal.exp_coe]; simp [Real.exp_pos]
      simp [multiplierWeight_bot hm0, ENNReal.mul_top hpos]
    | top =>
      simp [EReal.coe_mul_top_of_pos hm0, multiplierWeight_bot hm0]
  | top => exact absurd rfl ha
  | coe s =>
    induction b using EReal.rec with
    | bot =>
      rw [max_eq_left bot_le]
      simp only [multiplierWeight_coe]
      rcases le_total s 0 with hs | hs
      · refine le_add_right (le_add_right (ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr ?_)))
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_pos hc hδ).le hs]
      · refine le_add_right (le_add_left ?_)
        calc ENNReal.ofReal (Real.exp (-(c * s))) ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith))
          _ ≤ 2 := by norm_num
    | top =>
      have hpos : ENNReal.ofReal (Real.exp (-(m * s))) ≠ 0 := by
        simp [Real.exp_pos]
      simp only [EReal.coe_mul_top_of_pos hm0, EReal.exp_top, multiplierWeight_coe,
        ENNReal.top_mul hpos, add_top]
      exact le_top
    | coe t =>
      rw [show max (s : EReal) (t : EReal) = ((max s t : ℝ) : EReal) from
        (EReal.coe_strictMono.monotone.map_max).symm]
      simp only [multiplierWeight_coe, ← EReal.coe_mul, EReal.exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_add (Real.exp_pos _).le (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (real_exp_le_max_add hδ hm s t)

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_open_quasiPlurisubharmonicOn_of_at {φ : E → EReal} {x : E}
    (hφ : QuasiPlurisubharmonicAt φ x) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ QuasiPlurisubharmonicOn φ U := by
  obtain ⟨p, h, ⟨P, hP, hxP, hp⟩, hh, heq⟩ := hφ
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (hh.and heq)
  refine ⟨P ∩ V, hP.inter hV, ⟨hxP, hxV⟩, ?_⟩
  intro y hy
  refine ⟨p, h, ⟨P ∩ V, hP.inter hV, hy, hp.mono inter_subset_left⟩, ?_, ?_⟩
  · exact Filter.eventually_of_mem ((hP.inter hV).mem_nhds hy)
      (fun z hz => (hVsub hz.2).1)
  · exact Filter.eventually_of_mem ((hP.inter hV).mem_nhds hy)
      (fun z hz => (hVsub hz.2).2)

theorem aemeasurable_multiplierDensity_restrict {φ : E → EReal} {c : ℝ} {f : E → ℂ}
    {U : Set E} (hU : IsOpen U) (hφ : QuasiPlurisubharmonicOn φ U) (hc : c ≠ 0)
    (hf : ContinuousOn f U) :
    AEMeasurable (multiplierDensity φ c f) (μ.restrict U) := by
  classical
  have hφmeas : AEMeasurable φ (μ.restrict U) := by
    let v : E → EReal := fun y => if y ∈ U then φ y else ⊤
    have hv : UpperSemicontinuous v := by
      intro y a hya
      by_cases hy : y ∈ U
      · have hua : φ y < a := by simpa [v, hy] using hya
        have hlocal := hφ.upperSemicontinuousOn y hy a hua
        rw [hU.nhdsWithin_eq hy] at hlocal
        filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
        simpa [v, hzU] using hz
      · simp [v, hy] at hya
    apply hv.measurable.aemeasurable.congr
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    simp [v, hy]
  have hcmul : AEMeasurable (fun y => (c : EReal) * φ y) (μ.restrict U) :=
    (FirstPass.continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφmeas
  have hweight : AEMeasurable (fun y => multiplierWeight c (φ y)) (μ.restrict U) := by
    have hneg : AEMeasurable (fun y => -((c : EReal) * φ y)) (μ.restrict U) :=
      continuous_neg.measurable.comp_aemeasurable' hcmul
    simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
  have hfmeas : AEMeasurable f (μ.restrict U) := hf.aemeasurable hU.measurableSet
  exact ((hfmeas.norm.pow_const 2).ennreal_ofReal).mul hweight

/-- **Local max-closure step.** If `f` is in the multiplier ideal of `max(U, V)` at a
strictly larger exponent `c(1+δ)`, and near `x` the weight `e^{mV}` is dominated by
finitely many functions `g_l` that are weighted-L² for `U` at exponent
`m ≥ c(1+δ)/δ`, then `f` is in the multiplier ideal of `U` at exponent `c`. -/
theorem multiplierIntegrableAt_of_max_of_generators [ProperSpace E]
    [IsFiniteMeasureOnCompacts μ] {U V : E → EReal} {x : E} {c δ m : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hm : c * (1 + δ) / δ ≤ m) {f : E → ℂ}
    (hU : QuasiPlurisubharmonicAt U x)
    (hmax : MultiplierIntegrableAt (fun y => max (U y) (V y)) (c * (1 + δ)) f x μ)
    {O : Set E} (hO : IsOpen O) (hxO : x ∈ O) {N : ℕ} {g : Fin N → E → ℂ}
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hgL2 : ∀ l, WeightedL2On U m (g l) O μ)
    (hdom : ∀ y ∈ O, EReal.exp ((m : EReal) * V y) ≤
      C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) :
    MultiplierIntegrableAt U c f x μ := by
  obtain ⟨-, W1, hW1, hxW1, hfhol, hfL2⟩ := hmax
  obtain ⟨Q, hQ, hxQ, hUQ⟩ := exists_open_quasiPlurisubharmonicOn_of_at hU
  have hfc : ContinuousAt f x := (hfhol.differentiableAt (hW1.mem_nhds hxW1)).continuousAt
  have hbound : ∀ᶠ y in 𝓝 x, ‖f y‖ < ‖f x‖ + 1 :=
    hfc.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨V2, hV2sub, hV2, hxV2⟩ := mem_nhds_iff.mp hbound
  let W := W1 ∩ O ∩ V2 ∩ Q ∩ Metric.ball x 1
  have hW : IsOpen W := (((hW1.inter hO).inter hV2).inter hQ).inter Metric.isOpen_ball
  have hxW : x ∈ W := ⟨⟨⟨⟨hxW1, hxO⟩, hxV2⟩, hxQ⟩, Metric.mem_ball_self one_pos⟩
  have hWW1 : W ⊆ W1 := fun _ hy => hy.1.1.1.1
  have hWO : W ⊆ O := fun _ hy => hy.1.1.1.2
  have hμW : μ W ≠ ⊤ := ((measure_mono (fun _ hy => hy.2)).trans_lt
    (measure_ball_lt_top (μ := μ))).ne
  let K : ℝ≥0∞ := ENNReal.ofReal ((‖f x‖ + 1) ^ 2)
  have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ y ∈ W, multiplierDensity U c f y ≤
      multiplierDensity (fun y => max (U y) (V y)) (c * (1 + δ)) f y + 2 * K +
        ∑ l, (K * C) * multiplierDensity U m (g l) y := by
    intro y hy
    have hfy : ENNReal.ofReal (‖f y‖ ^ 2) ≤ K := ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (hV2sub hy.1.1.2).le 2)
    have hw := multiplierWeight_le_max_add hc hδ hm (b := V y) (hUQ y hy.1.2).ne_top
    unfold multiplierDensity
    calc ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (U y)
        ≤ ENNReal.ofReal (‖f y‖ ^ 2) * (multiplierWeight (c * (1 + δ)) (max (U y) (V y)) +
            2 + EReal.exp ((m : EReal) * V y) * multiplierWeight m (U y)) := by gcongr
      _ ≤ ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight (c * (1 + δ)) (max (U y) (V y)) +
            2 * K + K * ((C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) *
              multiplierWeight m (U y)) := by
          rw [mul_add, mul_add]
          refine add_le_add (add_le_add le_rfl ?_) ?_
          · rw [mul_comm]; exact mul_le_mul' le_rfl hfy
          · exact mul_le_mul' hfy (mul_le_mul' (hdom y (hWO hy)) le_rfl)
      _ = _ := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  refine ⟨hc, W, hW, hxW, hfhol.mono hWW1, aemeasurable_multiplierDensity_restrict hW
    (hUQ.mono fun _ hy => hy.1.2) hc.ne' (hfhol.mono hWW1).continuousOn, ?_⟩
  calc (∫⁻ y in W, multiplierDensity U c f y ∂μ)
      ≤ ∫⁻ y in W, (multiplierDensity (fun y => max (U y) (V y)) (c * (1 + δ)) f y +
          2 * K + ∑ l, (K * C) * multiplierDensity U m (g l) y) ∂μ :=
        setLIntegral_mono_ae' hW.measurableSet (Eventually.of_forall hpoint)
    _ = (∫⁻ y in W, multiplierDensity (fun y => max (U y) (V y)) (c * (1 + δ)) f y ∂μ) +
          2 * K * μ W + ∑ l, (K * C) * ∫⁻ y in W, multiplierDensity U m (g l) y ∂μ := by
        rw [lintegral_add_right' _ (Finset.aemeasurable_fun_sum _ fun l _ =>
            ((hgL2 l).1.mono_measure (Measure.restrict_mono hWO le_rfl)).const_mul _),
          lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
          lintegral_finsetSum' _ fun l _ =>
            ((hgL2 l).1.mono_measure (Measure.restrict_mono hWO le_rfl)).const_mul _]
        simp_rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hK hC)]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨(hfL2.mono hWW1).2, ?_⟩, ?_⟩
        · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK.lt_top) hμW.lt_top
        · exact ENNReal.sum_lt_top.mpr fun l _ => ENNReal.mul_lt_top
            (ENNReal.mul_ne_top hK hC).lt_top
            (((hgL2 l).mono hWO).2)

/-- Pointwise multiplier integrability of one function on an open set gives weighted
`L²` on a ball around each of its points. -/
theorem exists_ball_weightedL2On [ProperSpace E] {U : E → EReal} {c : ℝ} {g : E → ℂ}
    {O : Set E} (hO : IsOpen O) {z : E} (hz : z ∈ O) (hQ : QuasiPlurisubharmonicOn U O)
    (hg : DifferentiableOn ℂ g O) (hc : 0 < c)
    (h : ∀ y ∈ O, MultiplierIntegrableAt U c g y μ) :
    ∃ r > 0, Metric.ball z r ⊆ O ∧ WeightedL2On U c g (Metric.ball z r) μ := by
  classical
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO z hz
  have hKO : Metric.closedBall z (ε / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεO
  have hex : ∀ y : Metric.closedBall z (ε / 2), ∃ V : Set E, IsOpen V ∧ (y : E) ∈ V ∧
      WeightedL2On U c g V μ := fun y => by
    obtain ⟨-, V, hV, hyV, -, hL2⟩ := h y (hKO y.2)
    exact ⟨V, hV, hyV, hL2⟩
  choose W hW hyW hWL2 using hex
  obtain ⟨t, ht⟩ := (isCompact_closedBall z (ε / 2)).elim_finite_subcover W hW
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨ε / 2, by positivity, Metric.ball_subset_closedBall.trans hKO, ?_⟩
  refine ⟨aemeasurable_multiplierDensity_restrict Metric.isOpen_ball
    (hQ.mono (Metric.ball_subset_closedBall.trans hKO)) hc.ne'
    (hg.mono (Metric.ball_subset_closedBall.trans hKO)).continuousOn, ?_⟩
  have hsub : Metric.ball z (ε / 2) ⊆ ⋃ i : t, W i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht (Metric.ball_subset_closedBall hy))
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
  calc (∫⁻ y in Metric.ball z (ε / 2), multiplierDensity U c g y ∂μ)
      ≤ ∫⁻ y in ⋃ i : t, W i, multiplierDensity U c g y ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' i : t, ∫⁻ y in W i, multiplierDensity U c g y ∂μ := lintegral_iUnion_le _ _
    _ < ⊤ := by
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.mpr fun i _ => (hWL2 i).2

end Local

section StrongOpenness

open FirstPass

variable {X : Type*} [TopologicalSpace X]

theorem uscRegularization_congr_of_eventuallyEq {f g : X → EReal} {x : X}
    (hfg : f =ᶠ[𝓝 x] g) : uscRegularization f x = uscRegularization g x :=
  le_antisymm
    (uscRegularization_le_of_eventually_le (upperSemicontinuous_uscRegularization g x)
      (hfg.mono fun y hy => hy ▸ le_uscRegularization g y))
    (uscRegularization_le_of_eventually_le (upperSemicontinuous_uscRegularization f x)
      (hfg.mono fun y hy => hy ▸ le_uscRegularization f y))

/-- `sup_j (1 + 1/(j+1)) p = p` for a nonpositive extended real `p`. -/
theorem iSup_scale_eq {p : EReal} (hp : p ≤ 0) :
    (⨆ j : ℕ, (((1 + 1 / ((j : ℝ) + 1)) : ℝ) : EReal) * p) = p := by
  have hge1 : ∀ j : ℕ, (1 : ℝ) ≤ 1 + 1 / ((j : ℝ) + 1) := fun j =>
    le_add_of_nonneg_right (by positivity)
  refine le_antisymm (iSup_le fun j => ?_) ?_
  · induction p using EReal.rec with
    | bot => exact (EReal.coe_mul_bot_of_pos (lt_of_lt_of_le one_pos (hge1 j))).le
    | top => exact absurd hp (by simp)
    | coe q =>
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      have : q ≤ 0 := EReal.coe_nonpos.mp hp
      nlinarith [hge1 j]
  · induction p using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hp (by simp)
    | coe q =>
      have ht : Tendsto (fun j : ℕ => (((1 + 1 / ((j : ℝ) + 1)) * q : ℝ) : EReal)) atTop
          (𝓝 (q : EReal)) := by
        refine (continuous_coe_real_ereal.tendsto q).comp ?_
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add 1).mul_const q
      exact le_of_tendsto' ht fun j => by
        rw [EReal.coe_mul]; exact le_iSup (fun j : ℕ =>
          (((1 + 1 / ((j : ℝ) + 1)) : ℝ) : EReal) * (q : EReal)) j

variable {n : ℕ}

/-- Strong openness for one function, from strong openness for increasing
sequences: membership in `I(cP)` gives membership in `I(c(1+δ)P)` for some
`δ > 0`. -/
theorem exists_multiplierIntegrableAt_mul (hSO : Pending.IncreasingStrongOpenness n) :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal), IsOpen W →
        PlurisubharmonicOn P W → (∀ y ∈ W, P y ≤ 0) →
        ∀ z ∈ W, ∀ c : ℝ, 0 < c → ∀ f : ComplexModel n → ℂ, AnalyticAt ℂ f z →
          MultiplierIntegrableAt P c f z volume →
          ∃ δ : ℝ, 0 < δ ∧ MultiplierIntegrableAt P (c * (1 + δ)) f z volume := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W P hW hP hP0 z hz c hc f hf hmem
  let a : ℕ → ℝ := fun j => 1 + 1 / ((j : ℝ) + 1)
  have ha : ∀ j, 0 < a j := fun j => by positivity
  let v : ℕ → ComplexModel n → EReal := fun j y => (a j : EReal) * P y
  have hv : ∀ j, PlurisubharmonicOn (v j) W := fun j => hP.const_mul (ha j)
  have hmono : ∀ y ∈ W, Monotone fun j => v j y := by
    intro y hy i j hij
    have hji : a j ≤ a i := by
      simp only [a, add_le_add_iff_left]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
    induction hPy : P y using EReal.rec with
    | bot => simp [v, hPy, EReal.coe_mul_bot_of_pos (ha i), EReal.coe_mul_bot_of_pos (ha j)]
    | top => exact absurd (hPy ▸ hP0 y hy) (by simp)
    | coe q =>
      have hq : q ≤ 0 := EReal.coe_nonpos.mp (hPy ▸ hP0 y hy)
      simp only [v, hPy, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      nlinarith
  have hbound : LocallyUniformlyBoundedAbove (range v) W := by
    intro y hy
    refine ⟨univ, univ_mem, 0, ?_⟩
    rintro _ ⟨j, rfl⟩ x ⟨-, hx⟩
    induction hPx : P x using EReal.rec with
    | bot => simp [v, hPx, EReal.coe_mul_bot_of_pos (ha j)]
    | top => exact absurd (hPx ▸ hP0 x hx) (by simp)
    | coe q =>
      have hq : q ≤ 0 := EReal.coe_nonpos.mp (hPx ▸ hP0 x hx)
      simp only [v, hPx, ← EReal.coe_mul]
      exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos (ha j).le hq)
  have hsupeq : ∀ y ∈ W, (⨆ j, v j) y = P y := fun y hy => by
    simp only [iSup_apply, v, a]
    exact iSup_scale_eq (hP0 y hy)
  have hPq : QuasiPlurisubharmonicAt P z := (hP z hz).quasiPlurisubharmonicAt
  have hreg : uscRegularization (⨆ j, v j) =ᶠ[𝓝 z] P := by
    filter_upwards [hW.mem_nhds hz] with y hy
    rw [uscRegularization_congr_of_eventuallyEq (Filter.eventually_of_mem (hW.mem_nhds hy)
      hsupeq)]
    exact le_antisymm (uscRegularization_le_of_eventually_le
      ((hP y hy).quasiPlurisubharmonicAt.upperSemicontinuousAt) (Eventually.of_forall
        fun _ => le_rfl)) (le_uscRegularization P y)
  have hmem' : MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c f z volume :=
    multiplierIntegrableAt_of_moreSingularAt (hPq.congr hreg.symm)
      ⟨0, hreg.mono fun y hy => by simp [hy]⟩ hmem
  obtain ⟨j, hj⟩ := hSO W v hW hv hmono hbound z hz c hc f hf hmem'
  refine ⟨1 / ((j : ℝ) + 1), by positivity, ?_⟩
  have hdens : multiplierDensity (v j) c f = multiplierDensity P (c * a j) f := by
    funext y
    simp only [multiplierDensity, multiplierWeight, v, EReal.coe_mul, mul_assoc]
  obtain ⟨-, U, hU, hzU, hhol, hL2⟩ := hj
  refine ⟨mul_pos hc (ha j), U, hU, hzU, hhol, ?_⟩
  change WeightedL2On (v j) c f U volume at hL2
  unfold WeightedL2On at hL2 ⊢
  rw [hdens] at hL2
  exact hL2

end StrongOpenness

section ERealArith

theorem le_add_coe_add_coe {x : EReal} {r s : ℝ} (h : 0 ≤ r + s) :
    x ≤ (x + (r : EReal)) + (s : EReal) := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

theorem exp_mul_le_exp_mul_add_coe {x : EReal} {m r B : ℝ} (hm : 0 ≤ m) (hr : -r ≤ B) :
    EReal.exp ((m : EReal) * x) ≤
      EReal.exp ((m : EReal) * (x + (r : EReal))) * EReal.exp ((m * B : ℝ) : EReal) := by
  rw [← EReal.exp_add]
  apply EReal.exp_monotone
  induction x using EReal.rec with
  | bot =>
    rcases hm.lt_or_eq with hm | rfl
    · simp [EReal.coe_mul_bot_of_pos hm]
    · simp
  | top =>
    rcases hm.lt_or_eq with hm | rfl
    · rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hm, EReal.top_add_coe]
    · simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    nlinarith

theorem add_coe_add_coe_le {x : EReal} {r s t : ℝ} (h : r + s ≤ t) :
    (x + (r : EReal)) + (s : EReal) ≤ x + (t : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe u =>
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

end ERealArith

section Chart

open FirstPass DemaillyApproximation

variable {n : ℕ}

/-- **Chart form of the max-closure of I-equivalence.** Let `Uc`, `Vc` be quasi-PSH
chart functions made PSH on `W` by the same smooth correction `ρ`, with the multiplier
ideals of `Vc` contained in those of `Uc` at every point of `W` and every exponent.
Then the multiplier ideals of `max(Uc, Vc)` are contained in those of `Uc`. -/
theorem multiplierIntegrableAt_of_max_chart (hSO : Pending.IncreasingStrongOpenness n) :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
        (Uc Vc : ComplexModel n → EReal), IsOpen W → ContinuousOn ρ W →
        PlurisubharmonicOn (fun y => Uc y + (ρ y : EReal)) W →
        PlurisubharmonicOn (fun y => Vc y + (ρ y : EReal)) W →
        (∀ y ∈ W, QuasiPlurisubharmonicAt Uc y) →
        (∀ y ∈ W, QuasiPlurisubharmonicAt Vc y) →
        (∀ y ∈ W, QuasiPlurisubharmonicAt (fun y => max (Uc y) (Vc y)) y) →
        (∀ y ∈ W, ∀ a : ℝ, 0 < a → ∀ g : ComplexModel n → ℂ, AnalyticAt ℂ g y →
          MultiplierIntegrableAt Vc a g y volume → MultiplierIntegrableAt Uc a g y volume) →
        ∀ z ∈ W, ∀ c : ℝ, 0 < c → ∀ f : ComplexModel n → ℂ, AnalyticAt ℂ f z →
          MultiplierIntegrableAt (fun y => max (Uc y) (Vc y)) c f z volume →
          MultiplierIntegrableAt Uc c f z volume := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W ρ Uc Vc hW hρ hPu hPv hUq hVq hMq hvu z hz c hc f hf hmem
  -- a bound for the correction near `z`
  have hρz : ∀ᶠ y in 𝓝 z, |ρ y - ρ z| < 1 := by
    have := ((hρ z hz).continuousAt (hW.mem_nhds hz)).sub_const (ρ z)
    simpa using (this.abs.eventually (gt_mem_nhds (by simp : |ρ z - ρ z| < 1)))
  obtain ⟨O0', hO0sub, hO0', hzO0'⟩ := mem_nhds_iff.mp hρz
  set B : ℝ := |ρ z| + 1
  let O0 := O0' ∩ W
  have hO0 : IsOpen O0 := hO0'.inter hW
  have hzO0 : z ∈ O0 := ⟨hzO0', hz⟩
  have hρB : ∀ y ∈ O0, -ρ y ≤ B ∧ ρ y ≤ B := fun y hy => by
    have h1 := hO0sub hy.1
    have h2 := abs_sub_abs_le_abs_sub (ρ y) (ρ z)
    constructor <;> [have := neg_abs_le (ρ y); have := le_abs_self (ρ y)] <;>
      simp only [mem_ofPred_eq] at h1 <;> linarith
  -- the corrected maximum and an upper bound near `z`
  have hPmax : PlurisubharmonicOn (fun y => max (Uc y) (Vc y) + (ρ y : EReal)) W := by
    have := hPu.max hPv
    convert this using 2 with y
    exact (max_add_add_right _ _ _).symm
  obtain ⟨A, hA⟩ : ∃ A : ℝ, max (Uc z) (Vc z) + (ρ z : EReal) < (A : EReal) :=
    EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hPmax z hz).ne_top) |>.imp
      fun _ h => h.1
  obtain ⟨O1, hO1sub, hO1, hzO1⟩ := mem_nhds_iff.mp
    ((hPmax z hz).quasiPlurisubharmonicAt.upperSemicontinuousAt (A : EReal) hA)
  let W' := O0 ∩ O1
  have hW' : IsOpen W' := hO0.inter hO1
  have hzW' : z ∈ W' := ⟨hzO0, hzO1⟩
  let P' : ComplexModel n → EReal := fun y => (max (Uc y) (Vc y) + (ρ y : EReal)) + ((-A : ℝ) : EReal)
  have hP'psh : PlurisubharmonicOn P' W' :=
    (hPmax.mono fun _ hy => hy.1.2).add fun y _ =>
      plurisubharmonicAt_const _ (EReal.coe_ne_top _) y
  have hP'0 : ∀ y ∈ W', P' y ≤ 0 := by
    intro y hy
    have hlt : max (Uc y) (Vc y) + (ρ y : EReal) < (A : EReal) := hO1sub hy.2
    simp only [P']
    induction hx : max (Uc y) (Vc y) + (ρ y : EReal) using EReal.rec with
    | bot => simp
    | top => rw [hx] at hlt; simp at hlt
    | coe t =>
      rw [hx] at hlt
      rw [← EReal.coe_add, EReal.coe_nonpos]
      have := EReal.coe_lt_coe_iff.mp hlt
      linarith
  -- (a) pass to the corrected function
  have hP' : MultiplierIntegrableAt P' c f z volume :=
    multiplierIntegrableAt_of_moreSingularAt (hP'psh z hzW').quasiPlurisubharmonicAt
      ⟨A + B, Filter.eventually_of_mem (hW'.mem_nhds hzW') fun y hy => by
        simp only [P']
        calc max (Uc y) (Vc y) ≤ (max (Uc y) (Vc y) + (ρ y : EReal)) + (B : EReal) :=
              le_add_coe_add_coe (by linarith [(hρB y hy.1).1])
          _ = ((max (Uc y) (Vc y) + (ρ y : EReal)) + ((-A : ℝ) : EReal)) +
                ((A + B : ℝ) : EReal) := by
              rw [add_assoc (max (Uc y) (Vc y) + (ρ y : EReal)), ← EReal.coe_add,
                show -A + (A + B) = B by ring]⟩ hmem
  -- (b) strong openness
  obtain ⟨δ, hδ, hSO'⟩ := exists_multiplierIntegrableAt_mul hSO W' P' hW' hP'psh hP'0 z hzW'
    c hc f hf hP'
  -- (c) back to the chart maximum
  have hmax' : MultiplierIntegrableAt (fun y => max (Uc y) (Vc y)) (c * (1 + δ)) f z volume :=
    multiplierIntegrableAt_of_moreSingularAt (hMq z hz)
      ⟨B - A, Filter.eventually_of_mem (hW'.mem_nhds hzW') fun y hy =>
        add_coe_add_coe_le (by linarith [(hρB y hy.1).2])⟩ hSO'
  -- (d) the exponent
  set m : ℕ := ⌈c * (1 + δ) / δ⌉₊ with hmdef
  have hm : c * (1 + δ) / δ ≤ (m : ℝ) := Nat.le_ceil _
  have hm0 : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  -- (e) Demailly generators for the corrected `Vc`
  obtain ⟨O2, hO2, hzO2, hO2W, N, g, C, hC, hgan, hgL2, hdom⟩ :=
    exists_weightedL2_generators W (fun y => Vc y + (ρ y : EReal)) hW hPv z hz m hm0
  let O3 := O2 ∩ O0
  have hO3 : IsOpen O3 := hO2.inter hO0
  have hzO3 : z ∈ O3 := ⟨hzO2, hzO0⟩
  have hdom' : ∀ y ∈ O3, EReal.exp (((m : ℝ) : EReal) * Vc y) ≤
      (EReal.exp (((m : ℝ) * B : ℝ) : EReal) * C) * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2) := by
    intro y hy
    calc EReal.exp (((m : ℝ) : EReal) * Vc y)
        ≤ EReal.exp (((m : ℝ) : EReal) * (Vc y + (ρ y : EReal))) *
            EReal.exp (((m : ℝ) * B : ℝ) : EReal) :=
          exp_mul_le_exp_mul_add_coe hm0'.le (hρB y hy.2).1
      _ ≤ (C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) *
            EReal.exp (((m : ℝ) * B : ℝ) : EReal) := by
          gcongr
          simpa using hdom y hy.1
      _ = _ := by ring
  -- (g) the generators are weighted L² for `Uc`
  have hgU : ∀ l, ∃ r > 0, Metric.ball z r ⊆ O3 ∧
      WeightedL2On Uc (m : ℝ) (g l) (Metric.ball z r) volume := by
    intro l
    refine exists_ball_weightedL2On hO3 hzO3 (fun y hy => hUq y (hO2W hy.1))
      ((hgan l).differentiableOn.mono inter_subset_left) hm0' fun y hy => ?_
    have hV : MultiplierIntegrableAt (fun y => Vc y + (ρ y : EReal)) (m : ℝ) (g l) y volume :=
      ⟨hm0', O2, hO2, hy.1, (hgan l).differentiableOn, hgL2 l⟩
    have hV' : MultiplierIntegrableAt Vc (m : ℝ) (g l) y volume :=
      multiplierIntegrableAt_of_moreSingularAt (hVq y (hO2W hy.1))
        ⟨B, Filter.eventually_of_mem (hO0.mem_nhds hy.2) fun x hx => by
          simpa using (add_coe_add_coe_le (x := Vc x) (r := ρ x) (s := 0) (t := B)
            (by linarith [(hρB x hx).2]))⟩ hV
    exact hvu y (hO2W hy.1) _ hm0' (g l) (hgan l y hy.1) hV'
  choose r hr hrO3 hrL2 using hgU
  let O4 := O3 ∩ ⋂ l, Metric.ball z (r l)
  have hO4 : IsOpen O4 := hO3.inter (isOpen_iInter_of_finite fun l => Metric.isOpen_ball)
  have hzO4 : z ∈ O4 := ⟨hzO3, mem_iInter.mpr fun l => Metric.mem_ball_self (hr l)⟩
  exact multiplierIntegrableAt_of_max_of_generators hc hδ hm (hUq z hz) hmax' hO4 hzO4
    (ENNReal.mul_ne_top (by rw [EReal.exp_coe]; exact ENNReal.ofReal_ne_top) hC)
    (fun l => (hrL2 l).mono fun y hy => mem_iInter.mp hy.2 l)
    fun y hy => hdom' y hy.1

end Chart

section Manifold

open FirstPass FirstPass.IEnvelope

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Xia, Proposition 3.2.3 (max case).** I-equivalence to a fixed theta-PSH
potential is closed under pointwise maxima, from strong openness (proved in
`Pending.StrongOpennessRegularRoute`) and Demailly's approximation with finitely many
generators (`Pending.DemaillyApproximation`). -/
theorem iEquivalentMaxClosed_of_strongOpenness (hSO : Pending.IncreasingStrongOpenness n)
    (θ : SmoothRealForm n M 2) : IEquivalentMaxClosed θ := by
  intro φ u v _hφ hu hv huφ hvφ
  have hmax := IsThetaPshPotential.max hu hv
  refine ⟨fun c hc e z hz f hf hmem => ?_, ?_⟩
  · let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    obtain ⟨W, ρ, hzW, hρ⟩ := hu.1.hasSmoothLocalPotentials e z hz
    have hpsh : ∀ {w : M → EReal}, IsThetaPshPotential θ w →
        PlurisubharmonicOn (fun y => chartFunction w e y + (ρ y : EReal)) W := fun {w} hw =>
      chartCorrectedFamily_plurisubharmonicOn (F := {w})
        (fun _ h => by rw [mem_singleton_iff.mp h]; exact hw) e hρ _ ⟨w, mem_singleton _, rfl⟩
    have hUc := multiplierIntegrableAt_of_max_chart hSO W ρ (chartFunction u e)
      (chartFunction v e) hρ.1 hρ.2.2.1.continuousOn (hpsh hu) (hpsh hv)
      (fun y hy => hu.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy => hv.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy => hmax.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy a ha g hg hV => huφ.2 a ha e y (hρ.2.1 hy) g hg
        (hvφ.1 a ha e y (hρ.2.1 hy) g hg hV))
      z hzW c hc f hf hmem
    exact huφ.1 c hc e z hz f hf hUc
  · exact huφ.2.trans (Pending.iOrderOnManifold_of_le_add hmax.1.quasiPlurisubharmonic
      (C := 0) fun x => by simp)

/-- **Xia, Proposition 3.2.3 (max case), unconditionally.** -/
theorem iEquivalentMaxClosed (θ : SmoothRealForm n M 2) : IEquivalentMaxClosed θ :=
  iEquivalentMaxClosed_of_strongOpenness (Pending.increasingStrongOpenness_ofRegularRoute n) θ

end Manifold

end TranscendentalNakamaye.Pending.IEquivalentMax
