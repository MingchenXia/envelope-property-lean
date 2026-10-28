import TranscendentalNakamaye.Pending.DemaillyApproximationAnalyticType
import TranscendentalNakamaye.Pending.QuasiEquisingularBasics
import TranscendentalNakamaye.Pending.ChartWeightedL2Transfer

set_option autoImplicit false

/-!
# Quasi-equisingular approximation from Demailly's approximation theorem

Xia, *Singularities of the plurisubharmonic envelope*, Theorem 1.6.2 (`xia-sgpt:page-0049`):
every `θ`-PSH potential `u` on a compact Kähler manifold admits a quasi-equisingular
approximation in the sense of `FirstPass.QuasiEquisingularApproximation`.  Xia's proof is
Demailly's Bergman-kernel regularization, which is proved in the tree
(`DemaillyApproximationSequence`, `DemaillyApproximationAnalyticType`): the explicit sequence
`u_k = DemaillyApproximationSequence.seq F ρ u E k` (the glued chart Bergman branches at level
`m = 2^k`, shifted by a constant)

* decreases to `u` at every point (`antitone_seq`, `tendsto_seq`, `iInf_seq`);
* is `(θ + ε_k ω)`-PSH with `ε_k = (C_B + 1) C_χ 2^{-k}` (`isThetaPshPotential_seq`);
* has analytic singularities of type `(2^{-k}, 𝓘(2^k u))`
  (`DemaillyApproximationAnalyticType.hasAnalyticSingularitiesOfType_seq`).

This file adds the two missing clauses of `IsQuasiEquisingularApproximation`:

* **chartwise type** (`HasAnalyticSingularitiesOfType.hasManifoldAnalyticSingularityType`): a
  global type `(c, 𝔞)` gives, in every atlas chart, the rational logarithmic presentation
  `HasAnalyticSingularityTypeAt` with the chart-read generators;
* **the multiplier clause** (`multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType`):
  if `ψ ≤ φ` and `φ` has type `(m⁻¹, 𝓘(mψ))` with `m ≥ cd/(d-c)`, `0 < c < d`, then
  `𝓘(dφ) ⊆ 𝓘(cψ)` in every chart.  The proof is the pointwise Young inequality
  `e^{-cψ} ≤ e^{-dφ} + e^{mφ} e^{-mψ}` (exponents `d/c`, `d/(d-c)`; `multiplierWeight_le_add`)
  together with `e^{mφ} ≤ C ∑ |g_i|²` for generators `g_i ∈ 𝓘(mψ)`.  No strong openness is
  used: that is the other inclusion.

The assembly `exists_quasiEquisingularApproximation` treats dimension `0` by the constant
sequence (`isQuasiEquisingularApproximation_const`).  No connectedness is assumed.  In positive
dimension `exists_quasiEquisingularApproximation_ofType` exports, beyond the chartwise clause, the
GLOBAL type `(2^{-k}, 𝓘(2^k u))` of the `k`-th approximant, which the positive-current programme
consumes (Copy-4 `sec:trace-approx` and the second level `K_ℓ`).
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace TranscendentalNakamaye.Pending.QuasiEquisingularApproximationDemailly

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.QuasiEquisingularApproximation

/-! ### The pointwise Young inequality -/

/-- **Young's inequality for the multiplier weights, real form.**  For `0 < c < d`,
`m (d - c) ≥ c d` and `r ≤ s`: `e^{-cr} ≤ e^{-ds} + e^{ms} e^{-mr}`. -/
theorem real_exp_neg_mul_le_add {c d m r s : ℝ} (hc : 0 < c) (hcd : c < d)
    (hm : c * d ≤ m * (d - c)) (hrs : r ≤ s) :
    Real.exp (-(c * r)) ≤ Real.exp (-(d * s)) + Real.exp (m * s) * Real.exp (-(m * r)) := by
  have hd : 0 < d := hc.trans hcd
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hm0 : 0 < m := by nlinarith [mul_pos hc hd]
  rcases le_or_gt (d * s) (c * r) with h | h
  · have h1 : Real.exp (-(c * r)) ≤ Real.exp (-(d * s)) := Real.exp_le_exp.mpr (by linarith)
    exact h1.trans (le_add_of_nonneg_right (by positivity))
  · have hkey : -(c * r) ≤ m * s + -(m * r) := by
      rcases le_or_gt 0 r with hr | hr
      · nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hrs)]
      · have h1 : (d - c) * (-r) ≤ d * (s - r) := by nlinarith
        have h2 : m * ((d - c) * (-r)) ≤ m * (d * (s - r)) := mul_le_mul_of_nonneg_left h1 hm0.le
        have h3 : c * d * (-r) ≤ m * (d - c) * (-r) :=
          mul_le_mul_of_nonneg_right hm (by linarith)
        nlinarith
    calc Real.exp (-(c * r)) ≤ Real.exp (m * s + -(m * r)) := Real.exp_le_exp.mpr hkey
      _ = Real.exp (m * s) * Real.exp (-(m * r)) := Real.exp_add _ _
      _ ≤ Real.exp (-(d * s)) + Real.exp (m * s) * Real.exp (-(m * r)) :=
        le_add_of_nonneg_left (Real.exp_pos _).le

/-- **Young's inequality for the multiplier weights**, in `ℝ≥0∞` with extended-real
arguments: for `0 < c < d`, `m (d - c) ≥ c d` and `a ≤ b`,
`e^{-ca} ≤ e^{-db} + e^{mb} e^{-ma}`.  Poles are allowed: at `a = ⊥` the right side is
infinite (either `b = ⊥`, or `e^{mb} > 0` and `e^{-m⊥} = ∞`). -/
theorem multiplierWeight_le_add {c d m : ℝ} (hc : 0 < c) (hcd : c < d)
    (hm : c * d ≤ m * (d - c)) {a b : EReal} (hab : a ≤ b) :
    multiplierWeight c a ≤
      multiplierWeight d b + EReal.exp ((m : EReal) * b) * multiplierWeight m a := by
  have hd : 0 < d := hc.trans hcd
  have hm0 : 0 < m := by nlinarith [mul_pos hc hd, sub_pos.mpr hcd]
  induction a using EReal.rec with
  | bot =>
    rw [multiplierWeight_bot hc, multiplierWeight_bot hm0]
    by_cases hb : b = ⊥
    · rw [hb, multiplierWeight_bot hd, top_add]
    · have hexp : EReal.exp ((m : EReal) * b) ≠ 0 := by
        rw [Ne, EReal.exp_eq_zero_iff]
        induction b using EReal.rec with
        | bot => exact absurd rfl hb
        | top => rw [EReal.coe_mul_top_of_pos hm0]; exact top_ne_bot
        | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
      rw [ENNReal.mul_top hexp, add_top]
  | top =>
    rw [multiplierWeight_top hc]
    exact zero_le
  | coe r =>
    induction b using EReal.rec with
    | bot => exact absurd hab (not_le.mpr (EReal.bot_lt_coe r))
    | top =>
      rw [EReal.coe_mul_top_of_pos hm0, EReal.exp_top, multiplierWeight_coe m r,
        ENNReal.top_mul (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne', add_top]
      exact le_top
    | coe s =>
      have hrs : r ≤ s := EReal.coe_le_coe_iff.mp hab
      rw [multiplierWeight_coe, multiplierWeight_coe, multiplierWeight_coe, ← EReal.coe_mul,
        EReal.exp_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
      exact ENNReal.ofReal_le_ofReal (real_exp_neg_mul_le_add hc hcd hm hrs)

/-! ### `e^{mφ}` is dominated by the generators -/

/-- If `φ(y) = m⁻¹ log ∑ |g_i(y)|² + R` with `|R| ≤ C`, then
`e^{mφ(y)} ≤ e^{mC} ∑ |g_i(y)|²` (both sides vanish at a common zero of the `g_i`). -/
theorem exp_mul_le_of_eq_generatorLog {X : Type*} {m : ℕ} (hm : 0 < m) {N : ℕ}
    {g : Fin N → X → ℂ} {y : X} {a : EReal} {R C : ℝ} (hRC : |R| ≤ C)
    (ha : a = ((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * generatorLog g y + (R : EReal)) :
    EReal.exp (((m : ℝ) : EReal) * a) ≤
      ENNReal.ofReal (Real.exp ((m : ℝ) * C) * ∑ i, ‖g i y‖ ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcR : (((m : ℚ)⁻¹ : ℚ) : ℝ) = (m : ℝ)⁻¹ := by push_cast; ring
  rw [hcR] at ha
  set S : ℝ := ∑ i, ‖g i y‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · have hlog : generatorLog g y = ⊥ := by
      rw [generatorLog_eq_log_sum, ← hS, ← h0, ENNReal.ofReal_zero, ENNReal.log_zero]
    rw [ha, hlog, EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR), EReal.bot_add,
      EReal.coe_mul_bot_of_pos hmR, EReal.exp_bot]
    exact zero_le
  · have hlog : generatorLog g y = (Real.log S : EReal) := by
      rw [generatorLog_eq_log_sum, ← hS, ENNReal.log_ofReal_of_pos hpos]
    rw [ha, hlog, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, EReal.exp_coe]
    refine ENNReal.ofReal_le_ofReal ?_
    have hRle : R ≤ C := (le_abs_self R).trans hRC
    have heq : (m : ℝ) * ((m : ℝ)⁻¹ * Real.log S + R) = Real.log S + (m : ℝ) * R := by
      field_simp
    rw [heq, Real.exp_add, Real.exp_log hpos, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hRle hmR.le)) hS0

/-! ### The chartwise analytic singularity type -/

section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A holomorphic function on an open set `U` of the manifold, read in an atlas chart, is
holomorphic on `e.target ∩ e⁻¹' U`. -/
theorem differentiableOn_comp_symm {e : ComplexChart n M} {U : Set M} (hU : IsOpen U)
    {g : M → ℂ} (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U) :
    DifferentiableOn ℂ (fun w => g (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' U) := by
  intro w hw
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (e.val.symm w) :=
    hg.mdifferentiableAt (hU.mem_nhds hw.2)
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val.symm w :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.2 hw.1
  have h3 := h1.comp w h2
  rw [mdifferentiableAt_iff_differentiableAt] at h3
  exact h3.differentiableWithinAt

/-- **Global type gives the chartwise type.**  If `φ` has analytic singularities of type
`(c, 𝔞)`, then in every atlas chart and at every point of its target, `φ` read in the chart
has the rational logarithmic presentation `HasAnalyticSingularityTypeAt`, with coefficient `c`,
the chart-read generators and the chart-read bounded remainder. -/
theorem _root_.TranscendentalNakamaye.FirstPass.GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType.hasManifoldAnalyticSingularityType
    {φ : M → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (h : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) :
    HasManifoldAnalyticSingularityType (n := n) φ := by
  obtain ⟨hc, -, hloc⟩ := h
  intro e z hz
  obtain ⟨U, hU, hxU, N, g, hgd, -, R, C, hRC, hφ⟩ := hloc (e.val.symm z)
  have hV : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
    e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hU
  have hzV : z ∈ e.val.target ∩ e.val.symm ⁻¹' U := ⟨hz, hxU⟩
  refine ⟨c, N, fun j w => g j (e.val.symm w), ⟨Rat.cast_pos.mpr hc,
    ⟨_, hV, hzV, fun j => differentiableOn_comp_symm hU (hgd j)⟩,
    fun w => R (e.val.symm w), ⟨C, (abs_nonneg _).trans (hRC _ hxU), ?_⟩, ?_⟩⟩
  · filter_upwards [hV.mem_nhds hzV] with w hw
    exact hRC _ hw.2
  · filter_upwards [hV.mem_nhds hzV] with w hw
    exact hφ _ hw.2

end Chart

/-! ### The multiplier-ideal clause -/

/-- Multiplier integrability does not depend on which of the two Borel structures `ℂⁿ`
carries: the canonical `WithLp` one (used by `multiplierIdeal`) or `borel _` (used by
`MultiplierIdealIncluded`).  They are propositionally, not definitionally, equal
(compare `QuantitativeRegularizationPatchGeneratorIdeal.weightedL2On_ambient_eq_borel`). -/
theorem multiplierIntegrableAt_ambient_iff_borel {n : ℕ} [MeasurableSpace (ComplexModel n)]
    [BorelSpace (ComplexModel n)] (φ : ComplexModel n → EReal) (c : ℝ)
    (f : ComplexModel n → ℂ) (z : ComplexModel n) :
    MultiplierIntegrableAt φ c f z volume ↔
      (letI : MeasurableSpace (ComplexModel n) := borel _
       letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
       MultiplierIntegrableAt φ c f z volume) := by
  have h : ‹MeasurableSpace (ComplexModel n)› = borel (ComplexModel n) :=
    BorelSpace.measurable_eq
  subst h
  exact Iff.rfl

section Multiplier

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A generator of an ideal belongs to it. -/
theorem mem_of_generator {𝔞 : GermIdeal n M} {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    {N : ℕ} {g : Fin N → M → ℂ}
    (hgd : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U)
    (hgen : ∀ y ∈ U, ∀ h, 𝔞.mem y h ↔ IsInSpanAt (n := n) (· ∈ range g) y h) (i : Fin N) :
    𝔞.mem x (g i) := by
  refine (hgen x hxU (g i)).mpr ⟨?_, 1, fun _ => g i, fun _ _ => 1, fun _ => ⟨i, rfl⟩,
    fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const, ?_⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hgd i y hy).mdifferentiableAt (hU.mem_nhds hy)
  · exact Eventually.of_forall fun y => by simp

/-- **The multiplier-ideal clause from the analytic type.**  Let `ψ` be quasi-PSH, `ψ ≤ φ`, and
let `φ` have analytic singularities of type `(m⁻¹, 𝓘(mψ))`.  For `0 < c < d` with
`m (d - c) ≥ c d`, every germ of `𝓘(dφ)` is a germ of `𝓘(cψ)`, in every atlas chart.

Pointwise, `|f|² e^{-cψ} ≤ |f|² e^{-dφ} + |f|² e^{mφ} e^{-mψ}` (`multiplierWeight_le_add`) and
`|f|² e^{mφ} ≤ K ∑ |g_i|²` near the point (`exp_mul_le_of_eq_generatorLog`, `f` continuous),
while each `|g_i|² e^{-mψ}` is integrable near the point because `g_i ∈ 𝓘(mψ)` (transported
from the preferred chart to `e`, `ChartWeightedL2.multiplierIntegrableAt_chart`). -/
theorem multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType {ψ φ : M → EReal}
    (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) (hle : ∀ x, ψ x ≤ φ x) {m : ℕ} (hm : 0 < m)
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ ((m : ℚ))⁻¹
      (multiplierIdeal (n := n) (m : ℝ) ψ))
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hmcd : c * d ≤ (m : ℝ) * (d - c)) :
    MultiplierIdealIncluded (n := n) φ d ψ c := by
  classical
  intro e z hz f hfz hmem'
  have hmem : MultiplierIntegrableAt (chartFunction φ e) d f z volume :=
    (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mpr hmem'
  refine (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mp ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set x : M := e.val.symm z with hxdef
  have hx : x ∈ e.val.source := e.val.map_target hz
  have hex : e.val x = z := e.val.right_inv hz
  obtain ⟨-, -, hloc⟩ := hφ
  obtain ⟨U₀, hU₀, hxU₀, N, g, hgd, hgen, R, C, hRC, hφeq⟩ := hloc x
  -- the generators lie in `𝓘(mψ)` at `x`; read them in the chart `e`
  have hgi : ∀ i, MultiplierIntegrableAt (chartFunction ψ e) (m : ℝ)
      (fun w => g i (e.val.symm w)) z volume := by
    intro i
    have hmem_i := (mem_of_generator hU₀ hxU₀ hgd hgen i).2
    have husc : UpperSemicontinuousOn (chartFunction ψ e)
        (ChartWeightedL2.overlapDomain e (complexChartAt (n := n) x)) :=
      (hψ e).upperSemicontinuousOn.mono fun _ hw => hw.1
    have h := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) e
      (complexChartAt (n := n) x) hx (mem_complexChartAt_source x) husc hmR.ne' hmem_i
    rwa [hex] at h
  choose _hgc V hV hzV _hgd hgint using hgi
  obtain ⟨-, U, hU, hzU, hfdiff, hfint⟩ := hmem
  -- `|f|²` is bounded near `z`
  set Bf : ℝ := (‖f z‖ + 1) ^ 2 with hBf
  obtain ⟨B, hBsub, hB, hzB⟩ := mem_nhds_iff.mp
    (hfz.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖f z‖)))
  -- the neighbourhood
  set P : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U₀ with hPdef
  have hP : IsOpen P := e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hU₀
  set W : Set (ComplexModel n) := ((U ∩ ⋂ i, V i) ∩ B) ∩ P with hWdef
  have hW : IsOpen W :=
    ((hU.inter (isOpen_iInter_of_finite hV)).inter hB).inter hP
  have hzW : z ∈ W := ⟨⟨⟨hzU, mem_iInter.mpr hzV⟩, hzB⟩, hz, by rw [mem_preimage]; exact hxU₀⟩
  have hWU : W ⊆ U := fun _ hw => hw.1.1.1
  have hWV : ∀ i, W ⊆ V i := fun i _ hw => mem_iInter.mp hw.1.1.2 i
  set K : ℝ≥0∞ := ENNReal.ofReal (Bf * Real.exp ((m : ℝ) * C)) with hK
  -- the pointwise bound
  have hpoint : ∀ w ∈ W, multiplierDensity (chartFunction ψ e) c f w ≤
      multiplierDensity (chartFunction φ e) d f w +
        K * ∑ i, multiplierDensity (chartFunction ψ e) (m : ℝ)
          (fun w => g i (e.val.symm w)) w := by
    intro w hw
    have hwP : w ∈ P := hw.2
    have hwt : w ∈ e.val.target := hwP.1
    have hwU₀ : e.val.symm w ∈ U₀ := hwP.2
    have hfw : ‖f w‖ ^ 2 ≤ Bf := by
      rw [hBf]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (hBsub hw.1.2)) 2
    have hweight := multiplierWeight_le_add hc hcd hmcd (hle (e.val.symm w))
    have hexp := exp_mul_le_of_eq_generatorLog hm (hRC _ hwU₀) (hφeq _ hwU₀)
    simp only [multiplierDensity, chartFunction]
    set a := ψ (e.val.symm w)
    set b := φ (e.val.symm w)
    set S : ℝ := ∑ i, ‖g i (e.val.symm w)‖ ^ 2 with hS
    have hsum : ENNReal.ofReal (Real.exp ((m : ℝ) * C) * S) =
        ENNReal.ofReal (Real.exp ((m : ℝ) * C)) *
          ∑ i, ENNReal.ofReal (‖g i (e.val.symm w)‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, hS,
        ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    have hK' : K = ENNReal.ofReal Bf * ENNReal.ofReal (Real.exp ((m : ℝ) * C)) := by
      rw [hK, ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (‖f w‖ ^ 2) * multiplierWeight c a
        ≤ ENNReal.ofReal (‖f w‖ ^ 2) *
            (multiplierWeight d b + EReal.exp (((m : ℝ) : EReal) * b) *
              multiplierWeight (m : ℝ) a) := mul_le_mul_right hweight _
      _ = ENNReal.ofReal (‖f w‖ ^ 2) * multiplierWeight d b +
            ENNReal.ofReal (‖f w‖ ^ 2) * EReal.exp (((m : ℝ) : EReal) * b) *
              multiplierWeight (m : ℝ) a := by rw [mul_add, mul_assoc]
      _ ≤ ENNReal.ofReal (‖f w‖ ^ 2) * multiplierWeight d b +
            ENNReal.ofReal Bf * ENNReal.ofReal (Real.exp ((m : ℝ) * C) * S) *
              multiplierWeight (m : ℝ) a := by
          gcongr
      _ = ENNReal.ofReal (‖f w‖ ^ 2) * multiplierWeight d b +
            K * ∑ i, ENNReal.ofReal (‖g i (e.val.symm w)‖ ^ 2) *
              multiplierWeight (m : ℝ) a := by
          rw [hsum, hK', ← Finset.sum_mul]
          ring
  -- measurability
  have hmeasc : AEMeasurable (multiplierDensity (chartFunction ψ e) c f) (volume.restrict W) :=
    Pending.aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
      (fun w hw => hψ e w hw.2.1) hc.ne' (hfdiff.mono hWU).continuousOn
  have hmeasd : AEMeasurable (multiplierDensity (chartFunction φ e) d f) (volume.restrict W) :=
    hfint.1.mono_measure (Measure.restrict_mono hWU le_rfl)
  have hmeasg : ∀ i, AEMeasurable (multiplierDensity (chartFunction ψ e) (m : ℝ)
      (fun w => g i (e.val.symm w))) (volume.restrict W) := fun i =>
    (hgint i).1.mono_measure (Measure.restrict_mono (hWV i) le_rfl)
  refine ⟨hc, W, hW, hzW, hfdiff.mono hWU, hmeasc, ?_⟩
  calc (∫⁻ w in W, multiplierDensity (chartFunction ψ e) c f w)
      ≤ ∫⁻ w in W, (multiplierDensity (chartFunction φ e) d f w +
          K * ∑ i, multiplierDensity (chartFunction ψ e) (m : ℝ)
            (fun w => g i (e.val.symm w)) w) :=
        setLIntegral_mono_ae' hW.measurableSet (Eventually.of_forall hpoint)
    _ = (∫⁻ w in W, multiplierDensity (chartFunction φ e) d f w) +
          K * ∑ i, ∫⁻ w in W, multiplierDensity (chartFunction ψ e) (m : ℝ)
            (fun w => g i (e.val.symm w)) w := by
        rw [lintegral_add_left' hmeasd, lintegral_const_mul' K _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun i _ => hmeasg i]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨((lintegral_mono_set hWU).trans_lt hfint.2), ?_⟩
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun i _ => ?_)
        exact (lintegral_mono_set (hWV i)).trans_lt (hgint i).2

end Multiplier

/-! ### Assembly: Xia, Theorem 1.6.2 -/

section Assembly

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

open DemaillyApproximationSequence DemaillyApproximationAnalyticType
  QuantitativeRegularizationFixedCover

/-- **Demailly's sequence is a quasi-equisingular approximation, with its global type exported.**
In positive dimension the approximation of `exists_quasiEquisingularApproximation` is Demailly's
sequence `u_k = seq F ρ u E k`, and `u_k` has analytic singularities of type
`(2^{-k}, 𝓘(2^k u))` on all of `M` (`DemaillyApproximationAnalyticType.hasAnalyticSingularitiesOfType_seq`),
not only chartwise.  Copy-4 uses exactly this type twice: for `Φ^D_q` on `X` (`sec:trace-approx`) and
for `φ_{K,q}` on `V` (the second level `K_ℓ`).  The errors `ε_k = (C_B + 1) C_χ 2^{-k}` are
positive. -/
theorem exists_quasiEquisingularApproximation_ofType_pos (hn : 0 < n)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    ∃ ε : ℕ → ℝ, ∃ uSeq : ℕ → M → EReal,
      IsQuasiEquisingularApproximation omega θ u ε uSeq ∧ (∀ k, 0 < ε k) ∧
        ∀ k, HasAnalyticSingularitiesOfType (n := n) (uSeq k) (((2 ^ k : ℕ) : ℚ)⁻¹)
          (multiplierIdeal (n := n) ((2 ^ k : ℕ) : ℝ) u) := by
  obtain ⟨F⟩ := exists_fixedChartCover (Z := M) hn
  obtain ⟨ρ, hρ⟩ := F.exists_potentials θ
  obtain ⟨D, -, hD⟩ := exists_doublingConst F
  have hdouble := hD θ.val u hu.1 ρ hρ
  obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun j => ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j))
  have hCB := F.CB_nonneg
  refine ⟨fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ, seq F ρ u (2 * (D + 1 / 4)), ⟨hu,
    ⟨fun k => by positivity, fun a b hab => ?_, ?_⟩,
    fun k => isThetaPshPotential_seq hn F omega hsemi hu hρ _ k,
    fun k => (hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k).hasManifoldAnalyticSingularityType,
    ⟨fun x => antitone_seq F hdouble x, fun x => tendsto_seq F hu.1 hρ _ x⟩, ?_⟩,
    fun k => by positivity, fun k => hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k⟩
  · -- the errors decrease
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by linarith) (by positivity) ?_)
      hCχ.le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hab
  · -- the errors tend to zero
    have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h2 := h1.const_mul ((F.CB + 1) * Cχ)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    push_cast
    field_simp
  · -- the multiplier-ideal clause
    intro c d hc hcd
    have hdc : 0 < d - c := sub_pos.mpr hcd
    have hK : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
      have := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
      exact this.congr fun k => by push_cast; rfl
    filter_upwards [hK.eventually_ge_atTop (c * d / (d - c))] with k hk
    have hmcd : c * d ≤ ((2 ^ k : ℕ) : ℝ) * (d - c) := (div_le_iff₀ hdc).mp hk
    have hle : ∀ x, u x ≤ seq F ρ u (2 * (D + 1 / 4)) k x := fun x => by
      rw [← iInf_seq F hu.1 hρ hdouble x]
      exact iInf_le _ k
    exact multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType hu.1.quasiPlurisubharmonic hle
      (by positivity) (hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k) hc hcd hmcd

/-- `exists_quasiEquisingularApproximation_ofType_pos` without the positivity of the errors. -/
theorem exists_quasiEquisingularApproximation_ofType (hn : 0 < n) (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ ε : ℕ → ℝ, ∃ uSeq : ℕ → M → EReal,
      IsQuasiEquisingularApproximation omega θ u ε uSeq ∧
        ∀ k, HasAnalyticSingularitiesOfType (n := n) (uSeq k) (((2 ^ k : ℕ) : ℚ)⁻¹)
          (multiplierIdeal (n := n) ((2 ^ k : ℕ) : ℝ) u) := by
  obtain ⟨ε, uSeq, h, -, htype⟩ := exists_quasiEquisingularApproximation_ofType_pos hn omega θ hu
  exact ⟨ε, uSeq, h, htype⟩

/-- **Xia, SGPT, Theorem 1.6.2: existence of quasi-equisingular approximations**
(`xia-sgpt:page-0049`), from Demailly's approximation theorem.  On a compact Kähler manifold
(no connectedness; dimension `0` included) every `θ`-PSH potential `u` has a
quasi-equisingular approximation: in positive dimension Demailly's sequence
`u_k = seq F ρ u E k` with errors `ε_k = (C_B + 1) C_χ 2^{-k}`; in dimension `0` the constant
sequence. -/
theorem exists_quasiEquisingularApproximation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ ε : ℕ → ℝ, ∃ uSeq : ℕ → M → EReal,
      IsQuasiEquisingularApproximation omega θ u ε uSeq := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨c, 𝔞, h⟩ := hasAnalyticSingularities_of_dim_zero hu
    exact ⟨_, _, Pending.isQuasiEquisingularApproximation_const omega θ hu
      h.hasManifoldAnalyticSingularityType⟩
  obtain ⟨ε, uSeq, h, -⟩ := exists_quasiEquisingularApproximation_ofType hn omega θ hu
  exact ⟨ε, uSeq, h⟩

end Assembly

end

end TranscendentalNakamaye.Pending.QuasiEquisingularApproximationDemailly
