import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.RestrictionOhsawaTakegoshi
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.StrongOpennessRegularRoute
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.QuasiEquisingularApproximationDemailly
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.GermIdealPullbackCalculus
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PshConvexCone
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicAnalytic
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PolydiskPerronDataComparison
import EnvelopeProperty.ComplexGeometry.Pluripotential.UscRegularizationLocality
import EnvelopeProperty.ComplexGeometry.Pluripotential.IEnvelope
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.StrongOpennessEnvelope
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.Envelopes

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The trace-multiplier inclusion `𝓘_V(λu) ⊆ Res_V 𝓘(λψ)` from the `I`-order against the restricted approximants

The trace multiplier inclusion is `𝓘(qu) ⊂ 𝔅̄_q`: see Xia, *Singularities in global
pluripotential theory*, Proposition 8.2.3, and Darvas–Xia, *The trace operator of
quasi-plurisubharmonic functions on compact Kähler manifolds* (2024), Theorem 3.16.
For the ideal comparison `𝓘(Mu) ⊆ 𝔅̄_M`, the proof uses only `I`-domination of
the trace `u` by the restricted approximants:

> `f ∈ 𝓘(λu)` ⟹ (strong openness) `f ∈ 𝓘((1+δ)λu)` ⟹ (`u ≼_I φ_q`) `f ∈ 𝓘((1+δ)λφ_q)`
> ⟹ (Ohsawa–Takegoshi from `V`) `f` extends to a germ of `𝓘((1+δ)λΦ_q)`
> ⟹ (quasi-equisingularity, `q ≫ 1`) `f` extends to a germ of `𝓘(λψ)`.

`multiplierIdeal_le_restrictIdeal_of_eventually_iOrder` is this argument, for ANY quasi-psh `u`
on `V` with `u ≼_I Φ_q|_V` (`IOrderOnManifold`) for all large `q`, where `Φ_q` is any
quasi-equisingular approximation of `ψ` on `X`. Both routes for the restriction of positive currents
supply that hypothesis (the trace operator: `u ≼_P φ_q`; the trace-free limit
`u = lim P_{β_q}[φ_q]`: `u ≤ P_{β_q}[φ_q]`), so this module is route-independent.

Ingredients:

* `exists_gt_multiplierIntegrableAt` — **strong openness for one function** (Guan–Zhou), from
  the tree's increasing-sequence form `IncreasingStrongOpenness` (proved:
  `increasingStrongOpenness_ofRegularRoute`) applied to `t_j (v - M)`, `t_j ↓ 1`, on a ball where
  `v ≤ M`; `exists_gt_mem_multiplierIdeal` is its manifold form for quasi-psh `u`;
* `multiplierIdeal_le_of_multiplierIdealIncluded` — the chartwise inclusion
  `MultiplierIdealIncluded` (all atlas charts, the form of `IsQuasiEquisingularApproximation` and
  `IOrderOnManifold`) gives the germ-ideal inclusion `𝓘(cφ) ≤ 𝓘(dψ)`;
* Ohsawa–Takegoshi from `V`: `RestrictionOhsawaTakegoshi.multiplierIdeal_le_restrictIdeal`
  (the, piece C3);
* `iOrderOnManifold_of_le_singularityEnvelope_add` — the hypothesis `u ≼_I φ_q` from
  `u ≤ P_β[φ_q] + C` (Xia Prop. 3.2.9: `P_β[φ] ~_I φ`), the form both routes produce.

-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace ComplexGeometry.AnalyticGeometry.PositiveCurrentTraceMultiplier

noncomputable section

open Pluripotential Pluripotential.PositiveClasses Pluripotential.HolomorphicIdealSheaves Pluripotential.IEnvelope
  Pluripotential.QuasiEquisingularApproximation Pluripotential.BlowupSequences
  SubmanifoldChartedSpace SubmanifoldIdealRestriction

/-! ### Scaling the weight -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E]
  {μ : Measure E}

/-- `exp(-c (t a)) = exp(-(ct) a)`. -/
theorem multiplierWeight_coe_mul (c t : ℝ) (a : EReal) :
    multiplierWeight c ((t : EReal) * a) = multiplierWeight (c * t) a := by
  unfold multiplierWeight
  rw [← mul_assoc, ← EReal.coe_mul]

/-- **Scaling the weight is scaling the exponent**: `𝓘(c · (t w)) = 𝓘((ct) w)` for `t > 0`. -/
theorem multiplierIntegrableAt_coe_mul_iff {w : E → EReal} {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {f : E → ℂ} {z : E} :
    MultiplierIntegrableAt (fun y => (t : EReal) * w y) c f z μ ↔
      MultiplierIntegrableAt w (c * t) f z μ := by
  have hdens : multiplierDensity (fun y => (t : EReal) * w y) c f =
      multiplierDensity w (c * t) f := by
    funext y
    simp only [multiplierDensity, multiplierWeight_coe_mul]
  unfold MultiplierIntegrableAt WeightedL2On
  rw [hdens]
  exact ⟨fun ⟨_, h⟩ => ⟨mul_pos hc ht, h⟩, fun ⟨_, h⟩ => ⟨hc, h⟩⟩

end Scaling

/-! ### Strong openness for one function -/

section StrongOpenness

/-- On `a ≤ 0`, multiplication by a real `t ≥ 1` decreases. -/
theorem coe_mul_le_coe_mul_of_nonpos {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {a : EReal}
    (ha : a ≤ 0) : (t : EReal) * a ≤ (s : EReal) * a := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos (hs.trans_le hst), EReal.coe_mul_bot_of_pos hs]
  | coe a =>
      have ha' : a ≤ 0 := EReal.coe_nonpos.mp ha
      rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      nlinarith
  | top => exact absurd ha (by simp)

/-- `sup_j t_j a = a` for `a ≤ 0` and `t_j = 1 + 1/(j+1) ↓ 1`. -/
theorem iSup_coe_mul_of_nonpos {a : EReal} (ha : a ≤ 0) :
    (⨆ j : ℕ, ((1 + 1 / ((j : ℝ) + 1) : ℝ) : EReal) * a) = a := by
  induction a using EReal.rec with
  | bot =>
      have : ∀ j : ℕ, ((1 + 1 / ((j : ℝ) + 1) : ℝ) : EReal) * ⊥ = ⊥ := fun j =>
        EReal.coe_mul_bot_of_pos (by positivity)
      rw [show (fun j : ℕ => ((1 + 1 / ((j : ℝ) + 1) : ℝ) : EReal) * ⊥) = fun _ => ⊥ from
        funext this]
      exact iSup_const
  | coe a =>
      have ha' : a ≤ 0 := EReal.coe_nonpos.mp ha
      refine le_antisymm (iSup_le fun j => ?_) ?_
      · rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
        have : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
        nlinarith
      · -- `t_j a → a`
        have ht : Tendsto (fun j : ℕ => (1 + 1 / ((j : ℝ) + 1)) * a) atTop (𝓝 a) := by
          have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h2 := (tendsto_const_nhds (x := (1 : ℝ))).add h1
          rw [add_zero] at h2
          simpa using h2.mul_const a
        have hte : Tendsto (fun j : ℕ => (((1 + 1 / ((j : ℝ) + 1)) * a : ℝ) : EReal)) atTop
            (𝓝 (a : EReal)) :=
          (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp ht
        refine le_of_tendsto' hte fun j => ?_
        rw [EReal.coe_mul]
        exact le_iSup (fun j : ℕ => ((1 + 1 / ((j : ℝ) + 1) : ℝ) : EReal) * (a : EReal)) j
  | top => exact absurd ha (by simp)

/-- A regularization is dominated at a point by any majorant upper semicontinuous there (the
pointwise form of `Pluripotential.uscRegularization_le`). -/
theorem uscRegularization_apply_le_of_upperSemicontinuousAt' {X : Type*} [TopologicalSpace X]
    {f g : X → EReal} (hfg : f ≤ g) {p : X} (hg : UpperSemicontinuousAt g p) :
    uscRegularization f p ≤ g p := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨y, hy1, hy2⟩ := exists_between hcon
  have hmem : {x : X | g x < y} ∈ 𝓝 p := hg y hy1
  refine absurd ((uscRegularization_le_localSup f hmem).trans ?_) (not_le.mpr hy2)
  exact iSup₂_le fun x hx => (hfg x).trans hx.le

variable {k : ℕ}

/-- **Strong openness for one plurisubharmonic weight** (Guan–Zhou): if `|f|² e^{-cv}` is
integrable near `z` for `v` psh near `z`, so is `|f|² e^{-c'v}` for some `c' > c`.  From the
increasing-sequence form `IncreasingStrongOpenness` (`increasingStrongOpenness_ofRegularRoute`)
applied to `t_j (v - M)`, `t_j = 1 + 1/(j+1) ↓ 1`, on a neighbourhood where `v < M`. -/
theorem exists_gt_multiplierIntegrableAt {v : ComplexModel k → EReal} {W : Set (ComplexModel k)}
    (hW : IsOpen W) (hv : PlurisubharmonicOn v W) {z : ComplexModel k} (hz : z ∈ W) {c : ℝ}
    {f : ComplexModel k → ℂ} (hint : MultiplierIntegrableAt v c f z volume) :
    ∃ c' : ℝ, c < c' ∧ MultiplierIntegrableAt v c' f z volume := by
  have hc : 0 < c := hint.1
  -- a neighbourhood `B` of `z` in `W` on which `v < M`
  obtain ⟨U, hU, hzU, hdisc⟩ := hv z hz
  obtain ⟨M, hvzM, -⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr (hdisc.ne_top z hzU))
  have hlt : {y | v y < ((M : ℝ) : EReal)} ∈ 𝓝 z :=
    (hv z hz).upperSemicontinuousAt _ (by exact_mod_cast hvzM)
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hlt
  set B : Set (ComplexModel k) := (W ∩ U) ∩ O with hBdef
  have hB : IsOpen B := (hW.inter hU).inter hO
  have hzB : z ∈ B := ⟨⟨hz, hzU⟩, hzO⟩
  have hvB : ∀ y ∈ B, v y < ((M : ℝ) : EReal) := fun y hy => hOsub hy.2
  -- the normalized weight `w = v - M ≤ 0` on `B`
  set w : ComplexModel k → EReal := fun y => v y + ((-(M : ℝ) : ℝ) : EReal) with hwdef
  have hwB : ∀ y ∈ B, w y ≤ 0 := by
    intro y hy
    have h := hvB y hy
    simp only [hwdef]
    induction hvy : v y using EReal.rec with
    | bot => simp
    | coe a =>
        rw [hvy] at h
        rw [← EReal.coe_add, EReal.coe_nonpos]
        have := EReal.coe_lt_coe_iff.mp h
        linarith
    | top => rw [hvy] at h; exact absurd h (by simp)
  have hwpsh : PlurisubharmonicOn w B := (hv.mono fun y hy => hy.1.1).add_const _
  set t : ℕ → ℝ := fun j => 1 + 1 / ((j : ℝ) + 1) with htdef
  have htpos : ∀ j, 0 < t j := fun j => by positivity
  have ht1 : ∀ j, 1 < t j := fun j => by
    have : 0 < 1 / ((j : ℝ) + 1) := by positivity
    simp only [htdef]; linarith
  set s : ℕ → ComplexModel k → EReal := fun j y => (t j : EReal) * w y with hsdef
  have hspsh : ∀ j, PlurisubharmonicOn (s j) B := fun j => hwpsh.const_mul (htpos j)
  have hsmono : ∀ y ∈ B, Monotone fun j => s j y := by
    intro y hy i j hij
    refine coe_mul_le_coe_mul_of_nonpos (htpos j) ?_ (hwB y hy)
    simp only [htdef]
    have : ((i : ℝ) + 1) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hij
    gcongr
  have hsbdd : LocallyUniformlyBoundedAbove (range s) B := by
    intro y hy
    refine ⟨B, self_mem_nhdsWithin, 0, ?_⟩
    rintro g ⟨j, rfl⟩ x hx
    have h0 : ((t j : ℝ) : EReal) * w x ≤ (t j : EReal) * 0 :=
      mul_le_mul_of_nonneg_left (hwB x hx.1) (EReal.coe_nonneg.mpr (htpos j).le)
    simpa using h0
  -- `usc(sup_j s_j) = w` on `B`
  have hsup : ∀ y ∈ B, (⨆ j, s j) y = w y := by
    intro y hy
    rw [iSup_apply]
    exact iSup_coe_mul_of_nonpos (hwB y hy)
  have hwusc : ∀ y ∈ B, UpperSemicontinuousAt w y := fun y hy =>
    (hwpsh y hy).upperSemicontinuousAt
  have hreg : ∀ y ∈ B, uscRegularization (⨆ j, s j) y = w y := by
    intro y hy
    have heq : (⨆ j, s j) =ᶠ[𝓝 y] w :=
      eventually_of_mem (hB.mem_nhds hy) fun x hx => hsup x hx
    rw [uscRegularization_congr_of_eventuallyEq heq]
    exact le_antisymm
      (uscRegularization_apply_le_of_upperSemicontinuousAt' le_rfl (hwusc y hy))
      (le_uscRegularization w y)
  -- the hypothesis, for `w` and then for `usc(sup_j s_j)`
  have hwint : MultiplierIntegrableAt w c f z volume :=
    multiplierIntegrableAt_of_moreSingularAt
      (hwpsh z hzB).quasiPlurisubharmonicAt
      ⟨M, eventually_of_mem (hB.mem_nhds hzB) fun y _ => by
        simp only [hwdef]
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]⟩ hint
  have hregint : MultiplierIntegrableAt (uscRegularization (⨆ j, s j)) c f z volume := by
    obtain ⟨-, U₁, hU₁, hzU₁, hfd, hL2⟩ := hwint
    refine ⟨hc, U₁ ∩ B, hU₁.inter hB, ⟨hzU₁, hzB⟩, hfd.mono inter_subset_left, ?_⟩
    have hL2' := hL2.mono (inter_subset_left : U₁ ∩ B ⊆ U₁)
    have hcongr : EqOn (multiplierDensity (uscRegularization (⨆ j, s j)) c f)
        (multiplierDensity w c f) (U₁ ∩ B) := by
      intro y hy
      simp only [multiplierDensity, hreg y hy.2]
    refine ⟨hL2'.1.congr ((ae_restrict_iff' (hU₁.inter hB).measurableSet).mpr
      (Eventually.of_forall fun y hy => (hcongr hy).symm)), ?_⟩
    rw [setLIntegral_congr_fun (hU₁.inter hB).measurableSet hcongr]
    exact hL2'.2
  have hfz : AnalyticAt ℂ f z := by
    obtain ⟨-, U₁, hU₁, hzU₁, hfd, -⟩ := hint
    exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU₁ hfd hzU₁
  -- strong openness for the increasing sequence `s_j`
  obtain ⟨j, hj⟩ := increasingStrongOpenness_ofRegularRoute k B s hB hspsh hsmono hsbdd z hzB
    c hc f hfz ((QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mp hregint)
  have hj' : MultiplierIntegrableAt (s j) c f z volume :=
    (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr hj
  -- back to `v`, at the exponent `c t_j > c`
  have hwj : MultiplierIntegrableAt w (c * t j) f z volume :=
    (multiplierIntegrableAt_coe_mul_iff hc (htpos j)).mp hj'
  refine ⟨c * t j, by nlinarith [ht1 j], ?_⟩
  refine multiplierIntegrableAt_of_moreSingularAt
    ((hv z hz).quasiPlurisubharmonicAt) ⟨-M, Eventually.of_forall fun y => ?_⟩ hwj
  simp only [hwdef]
  rw [EReal.coe_neg]

end StrongOpenness

/-! ### Manifold form, and chartwise inclusions as germ-ideal inclusions -/

section Manifold

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- **Strong openness for a quasi-psh function on a manifold**: every germ of `𝓘(cu)` lies in
`𝓘(c'u)` for some `c' > c`.  In the preferred chart `u = P + h` near the point with `P` psh and
`h` smooth (hence bounded), so the Euclidean statement applies to `P`. -/
theorem exists_gt_mem_multiplierIdeal {u : Z → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u) {c : ℝ} {p : Z} {g : Z → ℂ}
    (hg : (multiplierIdeal (n := k) c u).mem p g) :
    ∃ c' : ℝ, c < c' ∧ (multiplierIdeal (n := k) c' u).mem p g := by
  obtain ⟨hghol, hint⟩ := hg
  set e := complexChartAt (n := k) p with hedef
  have hz : e.val p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source p)
  have hqp := hu e (e.val p) hz
  obtain ⟨P, h, hP, hh, heq⟩ := hqp
  obtain ⟨U, hUo, hzU, hdisc⟩ := hP
  have hPU : PlurisubharmonicOn P U := fun y hy => ⟨U, hUo, hy, hdisc⟩
  have hhc : ContinuousAt h (e.val p) := hh.self_of_nhds.continuousAt
  have hnear : ∀ᶠ y in 𝓝 (e.val p), |h y - h (e.val p)| < 1 := by
    filter_upwards [hhc (Metric.ball_mem_nhds (h (e.val p)) one_pos)] with y hy
    simpa [Real.dist_eq] using hy
  have h1 : MoreSingularAt (chartFunction u e) P (e.val p) := by
    refine ⟨h (e.val p) + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    have := (abs_lt.mp hb).2
    linarith
  have h2 : MoreSingularAt P (chartFunction u e) (e.val p) := by
    refine ⟨-h (e.val p) + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy, add_assoc, ← EReal.coe_add]
    refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
    have := (abs_lt.mp hb).1
    linarith
  have hPint := multiplierIntegrableAt_of_moreSingularAt
    (hPU _ hzU).quasiPlurisubharmonicAt h1 hint
  obtain ⟨c', hcc', hPint'⟩ := exists_gt_multiplierIntegrableAt hUo hPU hzU hPint
  exact ⟨c', hcc', hghol, multiplierIntegrableAt_of_moreSingularAt (hu e (e.val p) hz) h2 hPint'⟩

/-- **A chartwise inclusion is an inclusion of germ ideals**: `MultiplierIdealIncluded φ c ψ d`
(every atlas chart, the form of `IsQuasiEquisingularApproximation` and of `IOrderOnManifold`)
gives `𝓘(cφ) ≤ 𝓘(dψ)` (read in the preferred chart, with the ambient Borel structure). -/
theorem multiplierIdeal_le_of_multiplierIdealIncluded {φ ψ : Z → EReal} {c d : ℝ}
    (h : MultiplierIdealIncluded (n := k) φ c ψ d) :
    (multiplierIdeal (n := k) c φ).Le (multiplierIdeal (n := k) d ψ) := by
  rintro p g ⟨hghol, hint⟩
  refine ⟨hghol, ?_⟩
  set e := complexChartAt (n := k) p
  have hz : e.val p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source p)
  have hfz : AnalyticAt ℂ (fun z => g (e.val.symm z)) (e.val p) := by
    obtain ⟨-, U, hU, hzU, hfd, -⟩ := hint
    exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU hfd hzU
  have h' := h e (e.val p) hz _ hfz
    ((QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mp hint)
  exact (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mpr h'

/-- `u ≼_I φ` gives `𝓘(cu) ≤ 𝓘(cφ)` for every `c > 0`. -/
theorem multiplierIdeal_le_of_iOrderOnManifold {φ ψ : Z → EReal}
    (h : IOrderOnManifold (n := k) φ ψ) {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := k) c φ).Le (multiplierIdeal (n := k) c ψ) :=
  multiplierIdeal_le_of_multiplierIdealIncluded (h c hc)

/-- **The `I`-domination hypothesis from a domination by a `P`-envelope.**  If
`u ≤ P_β[φ] + C` for a genuine `β`-psh `φ` (`β` closed of type `(1,1)`, `Z` compact), then
`u ≼_I φ`: `u ≼_I P_β[φ]` by the additive comparison and `P_β[φ] ≼_I φ` (Xia, Prop. 3.2.9, by
strong openness).  The trace-free limit satisfies `u ≤ P_{β_q}[φ_q]`, and the trace satisfies
`u ≤ P_β[u] + C ≤ P_β[φ_q] + C` when `u ≼_P φ_q`. -/
theorem iOrderOnManifold_of_le_singularityEnvelope_add [CompactSpace Z] [Nonempty Z]
    {β : SmoothRealForm k Z 2} (hclosed : β.IsClosed) (h11 : β.IsTypeOneOne)
    {φ u : Z → EReal} (hφ : IsThetaPshPotential β φ) {C : ℝ}
    (hu : ∀ x, u x ≤ singularityEnvelope β φ x + (C : EReal)) :
    IOrderOnManifold (n := k) u φ :=
  (iOrderOnManifold_of_le_add (singularityEnvelope_isThetaPshPotential β hclosed h11
      hφ.1.hasSmoothLocalPotentials φ hφ).1.quasiPlurisubharmonic hu).trans
    (iEquivalent_singularityEnvelope_of_strongOpenness (increasingStrongOpenness_ofRegularRoute k)
      β hclosed h11 hφ.1.hasSmoothLocalPotentials φ hφ).2

end Manifold

/-! ### The trace-multiplier inclusion -/

section TraceMultiplier

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`𝓘_V(cu) ⊆ Res_V 𝓘(cψ)` (the trace multiplier, DX24 Thm 3.16's argument).**
Let `Φ_q` be a quasi-equisingular approximation of `ψ` on `X`, `W` a closed complex submanifold,
and `u` quasi-psh on `W` with `u ≼_I Φ_q|_W` for all large `q`. Then for every `c > 0` every
germ of `𝓘_W(cu)` is the restriction of a combination of germs of `𝓘_X(cψ)`: strong openness
moves `c` to some `c' > c`, the `I`-order passes to `𝓘_W(c'Φ_q|_W)`, Ohsawa–Takegoshi extends to
`𝓘_X(c'Φ_q)`, and quasi-equisingularity gives `𝓘_X(c'Φ_q) ⊆ 𝓘_X(cψ)` for `q` large. -/
theorem multiplierIdeal_le_restrictIdeal_of_eventually_iOrder
    {omega : KahlerBackground n X} {θ : ClosedRealOneOneForm n X} {ψ : X → EReal}
    {ε : ℕ → ℝ} {Φ : ℕ → X → EReal} (hqea : IsQuasiEquisingularApproximation omega θ ψ ε Φ)
    {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ {u : W → EReal}, ManifoldQuasiPlurisubharmonic (n := k) u →
      (∀ᶠ q in atTop, IOrderOnManifold (n := k) u (fun x : W => Φ q x.1)) →
      ∀ {c : ℝ}, 0 < c →
        (multiplierIdeal (n := k) c u).Le
          (restrictIdeal (k := k) (W := W) (multiplierIdeal (n := n) c ψ)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro u hu hH c hc p g hg
  obtain ⟨c', hcc', hg'⟩ := exists_gt_mem_multiplierIdeal hu hg
  obtain ⟨q, hq1, hq2⟩ := (hH.and (hqea.eventually_multiplierIdealIncluded hc hcc')).exists
  have h1 : (multiplierIdeal (n := k) c' (fun x : W => Φ q x.1)).mem p g :=
    multiplierIdeal_le_of_iOrderOnManifold hq1 (hc.trans hcc') p g hg'
  have h2 := RestrictionOhsawaTakegoshi.multiplierIdeal_le_restrictIdeal hk hW
    (hqea.term q).1.quasiPlurisubharmonic p g h1
  exact GermIdealPullbackCalculus.pullback_le_pullback
    (multiplierIdeal_le_of_multiplierIdealIncluded hq2) p g h2

end TraceMultiplier

end

end ComplexGeometry.AnalyticGeometry.PositiveCurrentTraceMultiplier
