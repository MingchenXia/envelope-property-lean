/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PointPoleExtension
import EnvelopeProperty.Char0.Weights

/-!
# Hörmander's estimate on balls and on `ℂ^N` (adapters to ComplexGeometry)

This file proves, from the `L²` theory of `EnvelopeProperty.ComplexGeometry`, the following nodes of
the characteristic-zero blueprint (`blueprint/src/char0.tex`):

* `lem:c0-hormander-bounded` (`hormander_ball`): Hörmander's `L²` estimate for `∂̄ u = v` on
  `B(0, R)`, for a smooth weight `Φ` plurisubharmonic on `B(0, R + 1)`, a `∂̄`-closed continuous
  `(0,1)`-form `v` supported in `closedBall 0 R`, and a Levi majorant `g`
  (`|∑ v_j ξ̄_j|² ≤ g L_Φ(ξ)`): `∫_{B(0,R)} |u|² e^{-Φ} ≤ 2 ∫ g e^{-Φ}`. It is
  `ComplexGeometry.AnalyticGeometry.Hormander.hormanderL2Estimate` on the bounded convex domain `B(0, R + 1)` with `K =
  closedBall 0 R` and `t = 1`; the correction weights `lam₁ ≤ lam₂` vanish near `K`, so they do
  not affect data supported in `K` nor the restriction to `B(0, R)`.
* `lem:c0-analytic-basics` (1) (`exists_differentiableOn_ae_eq_of_weakDbarEq_zero`): Weyl's lemma
  for `∂̄`, from `ComplexGeometry.AnalyticGeometry.exists_differentiableOn_ae_eq_of_weak_dbar`.
* `exists_holomorphic_ball`: the case `v = ∂̄ (θ f)` (`θ` a smooth cut-off, `f` holomorphic near
  `supp θ`) for weights with `L_Φ(ξ) ≥ (1 + |z|²)^{-2} |ξ|²`; then `θ f - u` is holomorphic.
* `lem:c0-hormander-global`: `exists_entire_hormander_global` for a decreasing sequence of smooth
  weights `Φ_i` with `L_{Φ_i}(ξ) ≥ (1 + |z|²)^{-2} |ξ|²` and a uniform bound
  `∫ |∂̄ θ|² |f|² (1 + |z|²)² e^{-Φ_i} ≤ I`: there is an entire `G` with
  `∫ |θ f - G|² e^{-Φ_i} ≤ 2 I` for every `i` and for the limit weight `sup_i e^{-Φ_i}`;
  `exists_entire_hormander_global_weights` for the weights of the blueprint,
  `Φ = ∑_a c_a log ∑_j |h_{a,j}|² + log (1 + |z|²)` regularized by `hormanderWeight`
  (`ε_i = regEps i = (i + 1)^{-2}`), with `e^{-Φ} = sup_i e^{-Φ_{ε_i}}`
  (`iSup_exp_neg_hormanderWeight` identifies it off the zero sets).
* `leviForm_eq_leviFormC0`: `ComplexGeometry.leviForm` is `leviFormC0` (`lem:c0-weight`), by `rfl`.

## Deviation from the blueprint proof of `lem:c0-hormander-global`

The blueprint takes weak limits in weighted `L²` of the solutions `u_{R,ε}`. Here, since the datum
is `v = ∂̄ (θ f)`, the functions `G_i = θ f - u_i` are holomorphic on the balls `B(0, R_i)`
(`exists_holomorphic_ball`), bounded in `L²(e^{-Φ_0})` uniformly; the normal-family lemma
`ComplexGeometry.AnalyticGeometry.exists_subseq_differentiableOn_extension_of_weighted_bounds`
(Montel) gives a locally uniformly
convergent subsequence with an entire limit `G`, and Fatou's lemma gives the estimate for every
`Φ_i`. The exhaustion `R_i → ∞` and the regularization `ε_i → 0` run along the same sequence.
The global lemma is stated for data `v = ∂̄ (θ f)`, the only case used (`prop:c0-l2-extension`),
with the Levi majorant `|f|² |dθ|² (1 + |z|²)²` (`poleMajorant`) in place of `|v|² (1 + |z|²)²`.
-/

open scoped NNReal ENNReal Topology ComplexConjugate ContDiff
open MeasureTheory Metric Set Filter

noncomputable section

namespace EnvelopeProperty.Char0

open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
  ComplexGeometry.AnalyticGeometry.Hormander ComplexGeometry.AnalyticGeometry.CauchyGreen
  ComplexGeometry.AnalyticGeometry.OTChen ComplexGeometry.AnalyticGeometry.PointPole

variable {N : ℕ}

/-- The Levi form `ComplexGeometry.leviForm` and `leviFormC0` (`lem:c0-weight`) are the same
function. -/
theorem leviForm_eq_leviFormC0 (u : ComplexModel N → ℝ) (x v : ComplexModel N) :
    leviForm u x v = leviFormC0 u x v := rfl

/-- A function vanishing off `K`, multiplied by `e^{-(Φ + lam)}` with `lam = 0` on `K`, is the
indicator of `K` of the function multiplied by `e^{-Φ}`. -/
theorem mul_exp_neg_add_eq_indicator {K : Set (ComplexModel N)} {G Φ lam : ComplexModel N → ℝ}
    (hG : ∀ z, G z ≠ 0 → z ∈ K) (hlam : ∀ z ∈ K, lam z = 0) :
    (fun z => G z * Real.exp (-(Φ z + lam z))) = K.indicator fun z => G z * Real.exp (-Φ z) := by
  funext z
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz, hlam z hz, add_zero]
  · have : G z = 0 := by_contra fun h => hz (hG z h)
    rw [indicator_of_notMem hz, this, zero_mul]

/-- **Hörmander's estimate on balls** (`lem:c0-hormander-bounded`). Let `Φ` be smooth and
plurisubharmonic on `B(0, R + 1)`, `v` a continuous weakly `∂̄`-closed `(0,1)`-form supported in
`closedBall 0 R`, and `g ≥ 0` supported in `closedBall 0 R` with `|∑ v_j ξ̄_j|² ≤ g L_Φ(ξ)` and
`∫ g e^{-Φ} < ∞`. Then there is `u ∈ L²(B(0,R), e^{-Φ})` with `∂̄ u = v` on `B(0, R)` and
`∫_{B(0,R)} |u|² e^{-Φ} ≤ 2 ∫ g e^{-Φ}`. -/
theorem hormander_ball {R : ℝ} {Φ : ComplexModel N → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (ball 0 (R + 1)))
    (hΦL : ∀ z ∈ ball (0 : ComplexModel N) (R + 1), ∀ ξ, 0 ≤ leviForm Φ z ξ)
    {v : Fin N → ComplexModel N → ℂ} (hv : ∀ j, Continuous (v j))
    (hvs : ∀ j z, v j z ≠ 0 → z ∈ closedBall (0 : ComplexModel N) R)
    (hvc : WeakDbarClosed (ball 0 (R + 1)) v)
    {g : ComplexModel N → ℝ} (hg0 : ∀ z, 0 ≤ g z)
    (hgs : ∀ z, g z ≠ 0 → z ∈ closedBall (0 : ComplexModel N) R)
    (hgL : ∀ z ∈ ball (0 : ComplexModel N) (R + 1), ∀ ξ : Fin N → ℂ,
      ‖∑ j, conj (ξ j) * v j z‖ ^ 2 ≤ g z * leviForm Φ z (∑ j, ξ j • coordVec j))
    (hgi : IntegrableOn (fun z => g z * Real.exp (-Φ z)) (closedBall 0 R)) :
    ∃ u : ComplexModel N → ℂ, MemLp u 2 (weightedVolume (ball 0 R) Φ) ∧
      WeakDbarEq (ball 0 R) u v ∧
      ∫ z in ball 0 R, ‖u z‖ ^ 2 * Real.exp (-Φ z) ≤
        2 * ∫ z in closedBall 0 R, g z * Real.exp (-Φ z) := by
  set K : Set (ComplexModel N) := closedBall 0 R with hK
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'D, -, hKU, hUD', hl₁, hl₂, -, hl0, hest⟩ :=
    hormanderL2Estimate N (ball 0 (R + 1)) isOpen_ball (convex_ball _ _) isBounded_ball
      K (isCompact_closedBall _ _) (closedBall_subset_ball (by linarith)) 1 one_pos
  have hD'sub : D' ⊆ ball 0 (R + 1) := subset_closure.trans hD'D
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hKD' : K ⊆ D' := hKU.trans hUD'
  have hKB : K ⊆ ball 0 (R + 1) := hKD'.trans hD'sub
  have hl₁K : ∀ z ∈ K, lam₁ z = 0 := fun z hz => (hl0 z (hKU hz)).1
  have hl₂K : ∀ z ∈ K, lam₂ z = 0 := fun z hz => (hl0 z (hKU hz)).2
  have hΦc : ContinuousOn Φ (ball 0 (R + 1)) := hΦ.continuousOn
  have hΦK : ContinuousOn (fun z => Real.exp (-Φ z)) K := (hΦc.mono hKB).neg.rexp
  -- the datum lies in the weighted `L²` space of `D'`
  have hvmem : ∀ j, MemLp (v j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x) := by
    intro j
    rw [memLp_weightedVolume_iff (w := fun x ↦ Φ x + lam₂ x)
      ((hΦc.mono hD'sub).add hl₂ |>.aemeasurable hD'm)
      (hv j).aestronglyMeasurable]
    rw [mul_exp_neg_add_eq_indicator (G := fun z => ‖v j z‖ ^ 2) (fun z hz => hvs j z (by
      simpa using hz)) hl₂K]
    refine (IntegrableOn.integrable_indicator ?_ measurableSet_closedBall).mono_measure
      Measure.restrict_le_self
    have hc : ContinuousOn (fun z => ‖v j z‖ ^ 2 * Real.exp (-Φ z)) K :=
      ((hv j).norm.pow 2).continuousOn.mul hΦK
    exact hc.integrableOn_compact (isCompact_closedBall _ _)
  have hvclosed : WeakDbarClosed D' v := fun h hh j k =>
    hvc h ⟨hh.1, hh.2.1, hh.2.2.trans hD'sub⟩ j k
  have hgint : Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') := by
    rw [mul_exp_neg_add_eq_indicator hgs hl₁K]
    exact (hgi.integrable_indicator measurableSet_closedBall).mono_measure
      Measure.restrict_le_self
  obtain ⟨⟨u, humem, hueq, huorth⟩, huest⟩ := hest Φ hΦ hΦL v hvmem hvclosed g
    (fun z _ => hg0 z) (fun z hz ξ => hgL z (hD'sub hz) ξ) hgint
  have hfinal := huest u humem hueq huorth
  have hw₁m : AEMeasurable (fun x ↦ Φ x + lam₁ x) (volume.restrict D') :=
    ((hΦc.mono hD'sub).add hl₁).aemeasurable hD'm
  have huint := integrable_of_memLp_weightedVolume hw₁m humem
  have hBK : ball (0 : ComplexModel N) R ⊆ K := ball_subset_closedBall
  have hBD' : ball (0 : ComplexModel N) R ⊆ D' := hBK.trans hKD'
  have heqB : ∀ z ∈ ball (0 : ComplexModel N) R,
      ‖u z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) = ‖u z‖ ^ 2 * Real.exp (-Φ z) := fun z hz => by
    rw [hl₁K z (hBK hz), add_zero]
  refine ⟨u, ?_, fun h hh j => hueq h ⟨hh.1, hh.2.1, hh.2.2.trans hBD'⟩ j, ?_⟩
  · have hΦBm : AEMeasurable Φ (volume.restrict (ball 0 R)) :=
      (hΦc.mono (ball_subset_ball (by linarith))).aemeasurable measurableSet_ball
    rw [memLp_weightedVolume_iff hΦBm
      ((aestronglyMeasurable_of_memLp_weightedVolume hw₁m humem).mono_measure
        (Measure.restrict_mono hBD' le_rfl))]
    exact ((huint.mono_measure (Measure.restrict_mono hBD' le_rfl)).congr
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall heqB)))
  · have hrhs : ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x)) =
        ∫ z in K, g z * Real.exp (-Φ z) := by
      rw [mul_exp_neg_add_eq_indicator hgs hl₁K, setIntegral_indicator measurableSet_closedBall,
        inter_eq_right.2 hKD']
    have hlhs : ∫ z in ball 0 R, ‖u z‖ ^ 2 * Real.exp (-Φ z) ≤
        ∫ x in D', ‖u x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x)) := by
      rw [← setIntegral_congr_fun measurableSet_ball heqB]
      exact setIntegral_mono_set huint (Eventually.of_forall fun z => by positivity)
        (Eventually.of_forall hBD')
    rw [← hrhs]
    linarith

/-- **Weyl's lemma for `∂̄`** (`lem:c0-analytic-basics` (1)): a locally integrable `u` on an open
`Ω ⊆ ℂ^N` with `∂̄ u = 0` in the sense of distributions agrees almost everywhere on `Ω` with a
holomorphic function. -/
theorem exists_differentiableOn_ae_eq_of_weakDbarEq_zero {Ω : Set (ComplexModel N)}
    (hΩ : IsOpen Ω) {u : ComplexModel N → ℂ} (hu : LocallyIntegrableOn u Ω)
    (hdbar : WeakDbarEq Ω u 0) :
    ∃ F : ComplexModel N → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ᵐ z ∂(volume.restrict Ω), u z = F z :=
  exists_differentiableOn_ae_eq_of_weak_dbar hΩ hu
    (integral_mul_dbarDir_eq_zero_of_coord hu fun h hh j => by simpa using hdbar h hh j)

/-- **Hörmander's estimate on balls for `v = ∂̄ (θ f)`.** Let `Φ` be smooth on `B(0, R + 1)`
with `L_Φ(ξ) ≥ (1 + |z|²)^{-2} |ξ|²`, `θ` a smooth function supported in `closedBall 0 R` and `f`
holomorphic near `supp θ`. Then there is `G` holomorphic on `B(0, R)` with
`∫_{B(0,R)} |θ f - G|² e^{-Φ} ≤ 2 ∫ |f|² |dθ|² (1 + |z|²)² e^{-Φ}`. -/
theorem exists_holomorphic_ball {R : ℝ} {Φ : ComplexModel N → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (ball 0 (R + 1)))
    (hΦL : ∀ z ∈ ball (0 : ComplexModel N) (R + 1), ∀ ξ,
      ‖ξ‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤ leviForm Φ z ξ)
    {θ : ComplexModel N → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθR : tsupport θ ⊆ closedBall 0 R)
    {W : Set (ComplexModel N)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    {f : ComplexModel N → ℂ} (hf : DifferentiableOn ℂ f W) :
    ∃ G : ComplexModel N → ℂ, DifferentiableOn ℂ G (ball 0 R) ∧
      ∫⁻ z in ball 0 R, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 * Real.exp (-Φ z)) ≤
        ENNReal.ofReal (2 * ∫ z in closedBall 0 R,
          poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-Φ z)) := by
  set a := cutProd θ f with ha_def
  set v : Fin N → ComplexModel N → ℂ := poleForm θ f with hv_def
  have hθd : ∀ z, DifferentiableAt ℝ θ z := fun z => (hθ.differentiable (by simp)) z
  have ha : ContDiff ℝ ∞ a := contDiff_cutProd hW hθ hf hts
  have ha1 : ContDiff ℝ 1 a := ha.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvdef : (fun j => dbarDir (coordVec j) a) = v :=
    funext fun j => funext fun z => dbarDir_cutProd hW hθ hf hts j z
  have hΦL0 : ∀ z ∈ ball (0 : ComplexModel N) (R + 1), ∀ ξ, 0 ≤ leviForm Φ z ξ :=
    fun z hz ξ => le_trans (by positivity) (hΦL z hz ξ)
  have hvs : ∀ j z, v j z ≠ 0 → z ∈ closedBall (0 : ComplexModel N) R := fun j z hz =>
    hθR (tsupport_poleForm_subset j (subset_tsupport _ hz))
  have hgs : ∀ z, poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 ≠ 0 →
      z ∈ closedBall (0 : ComplexModel N) R := by
    intro z hz
    by_contra hzK
    exact hz (by rw [poleMajorant_eq_zero_of_notMem_tsupport fun h => hzK (hθR h), zero_mul])
  have hgL : ∀ z ∈ ball (0 : ComplexModel N) (R + 1), ∀ ξ : Fin N → ℂ,
      ‖∑ j, conj (ξ j) * v j z‖ ^ 2 ≤
        poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 * leviForm Φ z (∑ j, ξ j • coordVec j) := by
    intro z hz ξ
    refine (norm_sum_conj_mul_poleForm_sq_le hθd z ξ).trans ?_
    have h1 := hΦL z hz (∑ j, ξ j • coordVec j)
    rw [div_le_iff₀ (by positivity)] at h1
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) (poleMajorant_nonneg θ f z)
  have hgc : Continuous fun z => poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 :=
    (continuous_poleMajorant hW hθ hf hts).mul (by fun_prop)
  have hgi : IntegrableOn (fun z => poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-Φ z))
      (closedBall 0 R) :=
    (hgc.continuousOn.mul (hΦ.continuousOn.mono (closedBall_subset_ball (by linarith))).neg.rexp
      ).integrableOn_compact (isCompact_closedBall _ _)
  have hvc : WeakDbarClosed (ball 0 (R + 1)) v := by
    rw [← hvdef]; exact weakDbarClosed_of_contDiffOn isOpen_ball ha1.contDiffOn
  obtain ⟨u, humem, hueq, hest⟩ := hormander_ball hΦ hΦL0
    (fun j => continuous_poleForm hW hθ hf hts j) hvs hvc
    (fun z => by have := poleMajorant_nonneg θ f z; positivity) hgs hgL hgi
  -- Weyl's lemma turns `a - u` into a holomorphic function.
  have hΦB : ContinuousOn Φ (ball 0 R) :=
    hΦ.continuousOn.mono (ball_subset_ball (by linarith))
  have huloc : LocallyIntegrableOn u (ball 0 R) :=
    locallyIntegrableOn_of_memLp_weightedVolume isOpen_ball hΦB humem
  have haloc : LocallyIntegrableOn a (ball 0 R) :=
    ha.continuous.continuousOn.locallyIntegrableOn measurableSet_ball
  have hFloc : LocallyIntegrableOn (fun z => a z - u z) (ball 0 R) := haloc.sub huloc
  have hweak : WeakDbarEq (ball 0 R) (fun z => a z - u z) 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn huloc hdc hdcs hdts
    simp only [sub_mul, Pi.zero_apply, zero_mul, integral_zero, neg_zero]
    rw [integral_sub i1 i2, hueq h hh j]
    have := weakDbarEq_of_contDiffOn isOpen_ball ha1.contDiffOn h hh j
    rw [show (fun j => dbarDir (coordVec j) a) j = v j from congrFun hvdef j] at this
    rw [this]
    ring
  obtain ⟨G, hG, hGae⟩ := exists_differentiableOn_ae_eq_of_weakDbarEq_zero isOpen_ball hFloc hweak
  have hae : (fun z => a z - G z) =ᵐ[volume.restrict (ball 0 R)] u := by
    filter_upwards [hGae] with z hz
    rw [← hz]; ring
  refine ⟨G, hG, ?_⟩
  have hΦm : AEMeasurable Φ (volume.restrict (ball 0 R)) := hΦB.aemeasurable measurableSet_ball
  have huint := integrable_of_memLp_weightedVolume hΦm humem
  calc ∫⁻ z in ball 0 R, ENNReal.ofReal (‖a z - G z‖ ^ 2 * Real.exp (-Φ z))
      = ∫⁻ z in ball 0 R, ENNReal.ofReal (‖u z‖ ^ 2 * Real.exp (-Φ z)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with z hz
        rw [hz]
    _ = ENNReal.ofReal (∫ z in ball 0 R, ‖u z‖ ^ 2 * Real.exp (-Φ z)) :=
        (ofReal_integral_eq_lintegral_ofReal huint
          (Eventually.of_forall fun z => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hest

/-- `|G|² ≤ 2 |a|² + 2 |a - G|²`. -/
theorem norm_sq_le_two_mul_add (a G : ℂ) : ‖G‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - G‖ ^ 2 := by
  have h : ‖G‖ ≤ ‖a‖ + ‖a - G‖ := by
    calc ‖G‖ = ‖a - (a - G)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖a‖ + ‖a - G‖ := norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖a - G‖)]

/-- **Hörmander's estimate on `ℂ^N` with polynomial weights** (`lem:c0-hormander-global`), for
data `v = ∂̄ (θ f)` and the regularized weights of the blueprint proof. Let `Φ_i` be smooth
weights on `ℂ^N`, decreasing in `i`, with `L_{Φ_i}(ξ) ≥ (1 + |z|²)^{-2} |ξ|²` (e.g.
`Φ_i = ∑_a c_a log (ε_i + ∑_j |h_{a,j}|²) + log (1 + |z|²)` with `ε_i ↓ 0`, see
`le_leviFormC0_weight`), let `θ` be smooth with compact support and `f` holomorphic near
`supp θ`, and assume `∫ |f|² |dθ|² (1 + |z|²)² e^{-Φ_i} ≤ I < ∞` for all `i`. Then there is an
entire `G` with `∫ |θ f - G|² e^{-Φ_i} ≤ 2 I` for every `i`, and also
`∫ |θ f - G|² sup_i e^{-Φ_i} ≤ 2 I`. In particular `u = θ f - G` solves `∂̄ u = ∂̄ (θ f)` on
`ℂ^N` (`G` is holomorphic) with the `L²` bound for the limit weight. -/
theorem exists_entire_hormander_global {Φ : ℕ → ComplexModel N → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i))
    (hΦL : ∀ i z ξ, ‖ξ‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤ leviForm (Φ i) z ξ)
    (hanti : ∀ z, Antitone fun i => Φ i z)
    {θ : ComplexModel N → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    {W : Set (ComplexModel N)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    {f : ComplexModel N → ℂ} (hf : DifferentiableOn ℂ f W) {I : ℝ≥0∞} (hI : I ≠ ⊤)
    (hIb : ∀ i, ∫⁻ z, ENNReal.ofReal (poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 *
      Real.exp (-Φ i z)) ≤ I) :
    ∃ G : ComplexModel N → ℂ, Differentiable ℂ G ∧
      (∀ i, ∫⁻ z, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 * Real.exp (-Φ i z)) ≤ 2 * I) ∧
      ∫⁻ z, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2) *
        ⨆ i, ENNReal.ofReal (Real.exp (-Φ i z)) ≤ 2 * I := by
  set a := cutProd θ f with ha_def
  have ha : ContDiff ℝ ∞ a := contDiff_cutProd hW hθ hf hts
  obtain ⟨R₀, hR₀⟩ := hθcs.isCompact.isBounded.subset_closedBall (0 : ComplexModel N)
  set U : ℕ → Set (ComplexModel N) := fun i => ball 0 (R₀ + i) with hU
  have hUo : ∀ i, IsOpen (U i) := fun i => isOpen_ball
  have hUm : Monotone U := fun i j hij => ball_subset_ball (by simp [hij])
  have hUuniv : (⋃ i, U i) = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    obtain ⟨i, hi⟩ := exists_nat_gt (‖z‖ - R₀)
    exact ⟨i, by simp [U, mem_ball, dist_eq_norm]; linarith⟩
  -- one solution on each ball
  have hsol : ∀ i, ∃ G : ComplexModel N → ℂ, DifferentiableOn ℂ G (U i) ∧
      ∫⁻ z in U i, ENNReal.ofReal (‖a z - G z‖ ^ 2 * Real.exp (-Φ i z)) ≤ 2 * I := by
    intro i
    obtain ⟨G, hG, hb⟩ := exists_holomorphic_ball (R := R₀ + i) (hΦ i).contDiffOn
      (fun z _ ξ => hΦL i z ξ) hθ
      (hR₀.trans (closedBall_subset_closedBall (by simp))) hW hts hf
    refine ⟨G, hG, hb.trans ?_⟩
    have hgc : Continuous fun z => poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-Φ i z) :=
      ((continuous_poleMajorant hW hθ hf hts).mul (by fun_prop)).mul
        ((hΦ i).continuous.neg.rexp)
    have hgi : IntegrableOn (fun z => poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 *
        Real.exp (-Φ i z)) (closedBall 0 (R₀ + i)) :=
      hgc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun z => by
        have := poleMajorant_nonneg θ f z; positivity)]
    gcongr
    exact setLIntegral_le_lintegral _ _ |>.trans (hIb i)
  choose G hG hGb using hsol
  -- uniform bounds in the fixed weight `e^{-Φ_0}`
  set w₀ : ComplexModel N → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-Φ 0 z)) with hw₀
  have hw₀c : Continuous w₀ := ENNReal.continuous_ofReal.comp (hΦ 0).continuous.neg.rexp
  have hacs : HasCompactSupport a := by
    refine hθcs.mono' fun z hz => ?_
    simp only [Function.mem_support, a, cutProd, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
      not_or] at hz
    exact subset_tsupport _ hz.1
  set J : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (‖a z‖ ^ 2 * Real.exp (-Φ 0 z)) with hJ
  have hJ : J ≠ ⊤ := by
    refine (Integrable.lintegral_lt_top ?_).ne
    refine (ha.continuous.norm.pow 2 |>.mul
      (hΦ 0).continuous.neg.rexp).integrable_of_hasCompactSupport ?_
    refine hacs.mono fun z hz => ?_
    intro h0
    exact hz (by simp [h0])
  have hbound : ∀ i, ∫⁻ z in U i, ENNReal.ofReal (‖G i z‖ ^ 2) * w₀ z ≤ 2 * J + 2 * (2 * I) := by
    intro i
    have hpt : ∀ z, ENNReal.ofReal (‖G i z‖ ^ 2) * w₀ z ≤
        2 * ENNReal.ofReal (‖a z‖ ^ 2 * Real.exp (-Φ 0 z)) +
          2 * ENNReal.ofReal (‖a z - G i z‖ ^ 2 * Real.exp (-Φ i z)) := by
      intro z
      have he : Real.exp (-Φ 0 z) ≤ Real.exp (-Φ i z) :=
        Real.exp_le_exp.2 (neg_le_neg (hanti z (Nat.zero_le i)))
      rw [hw₀, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := norm_sq_le_two_mul_add (a z) (G i z)
      have h2 : ‖a z - G i z‖ ^ 2 * Real.exp (-Φ 0 z) ≤ ‖a z - G i z‖ ^ 2 * Real.exp (-Φ i z) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-Φ 0 z)).le
      nlinarith
    calc ∫⁻ z in U i, ENNReal.ofReal (‖G i z‖ ^ 2) * w₀ z
        ≤ ∫⁻ z in U i, (2 * ENNReal.ofReal (‖a z‖ ^ 2 * Real.exp (-Φ 0 z)) +
          2 * ENNReal.ofReal (‖a z - G i z‖ ^ 2 * Real.exp (-Φ i z))) := lintegral_mono hpt
      _ = 2 * (∫⁻ z in U i, ENNReal.ofReal (‖a z‖ ^ 2 * Real.exp (-Φ 0 z))) +
          2 * ∫⁻ z in U i, ENNReal.ofReal (‖a z - G i z‖ ^ 2 * Real.exp (-Φ i z)) := by
        have hc0 : Continuous fun z => ‖a z‖ ^ 2 * Real.exp (-Φ 0 z) :=
          (ha.continuous.norm.pow 2).mul (hΦ 0).continuous.neg.rexp
        rw [lintegral_add_left' (f := fun z => 2 * ENNReal.ofReal (‖a z‖ ^ 2 *
          Real.exp (-Φ 0 z))) ((ENNReal.continuous_ofReal.comp hc0).measurable.const_mul
            2).aemeasurable,
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * J + 2 * (2 * I) :=
        add_le_add (mul_le_mul_right (setLIntegral_le_lintegral _ _) 2)
          (mul_le_mul_right (hGb i) 2)
  have hlow : ∀ x ∈ ⋃ i, U i, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ (fun _ : ℕ => w₀) 0 y := by
    intro x _
    obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
      (hΦ 0).continuous.continuousOn
    refine ⟨1, one_pos, Real.exp (-M), Real.exp_pos _, fun y hy => ENNReal.ofReal_le_ofReal ?_⟩
    have := hM y (ball_subset_closedBall hy)
    rw [Real.norm_eq_abs] at this
    exact Real.exp_le_exp.2 (by linarith [le_abs_self (Φ 0 y)])
  obtain ⟨ψ, G', hψ, hG', hconv, -, -⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds (ι := fun e : Empty => e.elim)
      (g := fun e : Empty => e.elim) (w := fun _ => w₀) hUo hUm (fun _ _ => monotone_const)
      (fun _ => hw₀c.aemeasurable) hlow hG (fun _ e => e.elim)
      (by finiteness) hbound
  rw [hUuniv] at hG' hconv
  have hpt : ∀ z, Tendsto (fun k => G (ψ k) z) atTop (𝓝 (G' z)) := fun z =>
    hconv.tendsto_at (mem_univ z)
  -- Fatou at a fixed weight `e^{-Φ_{i₀}}`
  have hfatou : ∀ i₀, ∫⁻ z, ENNReal.ofReal (‖a z - G' z‖ ^ 2 * Real.exp (-Φ i₀ z)) ≤ 2 * I := by
    intro i₀
    set F : ℕ → ComplexModel N → ℝ≥0∞ := fun k => (U (ψ k)).indicator
      fun z => ENNReal.ofReal (‖a z - G (ψ k) z‖ ^ 2 * Real.exp (-Φ i₀ z)) with hF
    have hmeas : ∀ k, AEMeasurable (F k) volume := by
      intro k
      rw [aemeasurable_indicator_iff (hUo _).measurableSet]
      refine (ENNReal.continuous_ofReal.comp_continuousOn ?_).aemeasurable (hUo _).measurableSet
      exact ((ha.continuous.continuousOn.sub (hG (ψ k)).continuousOn).norm.pow 2).mul
        (hΦ i₀).continuous.neg.rexp.continuousOn
    have hlim : ∀ z, Tendsto (fun k => F k z) atTop
        (𝓝 (ENNReal.ofReal (‖a z - G' z‖ ^ 2 * Real.exp (-Φ i₀ z)))) := by
      intro z
      have hev : ∀ᶠ k in atTop, z ∈ U (ψ k) := by
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hUuniv.symm ▸ mem_univ z : z ∈ ⋃ i, U i)
        filter_upwards [eventually_ge_atTop i] with k hk
        exact hUm (hk.trans (hψ.id_le k)) hi
      have h1 : Tendsto (fun k => ENNReal.ofReal (‖a z - G (ψ k) z‖ ^ 2 * Real.exp (-Φ i₀ z)))
          atTop (𝓝 (ENNReal.ofReal (‖a z - G' z‖ ^ 2 * Real.exp (-Φ i₀ z)))) :=
        ENNReal.tendsto_ofReal
          (((tendsto_const_nhds.sub (hpt z)).norm.pow 2).mul tendsto_const_nhds)
      refine h1.congr' ?_
      filter_upwards [hev] with k hk
      simp [F, indicator_of_mem hk]
    have hev : ∀ᶠ k in atTop, ∫⁻ z, F k z ≤ 2 * I := by
      filter_upwards [eventually_ge_atTop i₀] with k hk
      rw [lintegral_indicator (hUo _).measurableSet]
      refine le_trans (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_) (hGb (ψ k))
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg
        (hanti z (hk.trans (hψ.id_le k))))) (by positivity)
    calc ∫⁻ z, ENNReal.ofReal (‖a z - G' z‖ ^ 2 * Real.exp (-Φ i₀ z))
        = ∫⁻ z, liminf (fun k => F k z) atTop :=
          lintegral_congr fun z => (hlim z).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ z, F k z) atTop := lintegral_liminf_le' hmeas
      _ ≤ 2 * I := liminf_le_of_frequently_le' hev.frequently
  refine ⟨G', differentiableOn_univ.1 hG', hfatou, ?_⟩
  -- monotone convergence in the weight
  have hmeas' : ∀ i, AEMeasurable (fun z => ENNReal.ofReal (‖a z - G' z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-Φ i z))) volume := fun i =>
    ((ENNReal.measurable_ofReal.comp ((ha.continuous.sub
      (differentiableOn_univ.1 hG').continuous).norm.pow 2).measurable).mul
      (ENNReal.measurable_ofReal.comp (hΦ i).continuous.neg.rexp.measurable)).aemeasurable
  have hmono : ∀ᵐ z ∂(volume : Measure (ComplexModel N)), Monotone fun i =>
      ENNReal.ofReal (‖a z - G' z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ i z)) :=
    Eventually.of_forall fun z i j hij => mul_le_mul_right
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (hanti z hij)))) _
  calc ∫⁻ z, ENNReal.ofReal (‖a z - G' z‖ ^ 2) * ⨆ i, ENNReal.ofReal (Real.exp (-Φ i z))
      = ∫⁻ z, ⨆ i, ENNReal.ofReal (‖a z - G' z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ i z)) :=
        lintegral_congr fun z => ENNReal.mul_iSup _ _
    _ = ⨆ i, ∫⁻ z, ENNReal.ofReal (‖a z - G' z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ i z)) :=
        lintegral_iSup' hmeas' hmono
    _ ≤ 2 * I := iSup_le fun i => by
        simpa only [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖a _ - G' _‖ ^ 2)]
          using hfatou i

/-! ### The weights of `lem:c0-hormander-global` -/

/-- The regularization parameter `ε_i = δ_i² = (i + 1)^{-2}`. -/
def regEps (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) ^ 2

theorem regEps_pos (i : ℕ) : 0 < regEps i := by unfold regEps; positivity

theorem regEps_le_one (i : ℕ) : regEps i ≤ 1 := by
  unfold regEps
  have h1 : 1 / ((i : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have h0 : 0 ≤ 1 / ((i : ℝ) + 1) := by positivity
  nlinarith

theorem antitone_regEps : Antitone regEps := by
  intro i j hij
  unfold regEps
  have hi : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact pow_le_pow_left₀ (by positivity) this 2

theorem tendsto_regEps : Tendsto regEps atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := h.pow 2
  rw [zero_pow two_ne_zero] at this
  exact this

section Weights

variable {A : Type*} [Fintype A] {J : A → Type*} [∀ a, Fintype (J a)]

/-- The regularized weights `Φ_{ε_i} = ∑_a c_a log (ε_i + ∑_j |h_{a,j}|²) + log (1 + |z|²)` of
`lem:c0-hormander-global`, decreasing to `Φ = ∑_a c_a log ∑_j |h_{a,j}|² + log (1 + |z|²)`. -/
def hormanderWeight (c : A → ℝ) (h : (a : A) → J a → ComplexModel N → ℂ) (i : ℕ)
    (z : ComplexModel N) : ℝ :=
  ∑ a, c a * Real.log (regEps i + ∑ j, ‖h a j z‖ ^ 2) + Real.log (1 + ‖z‖ ^ 2)

theorem antitone_hormanderWeight {c : A → ℝ} (hc : ∀ a, 0 ≤ c a)
    (h : (a : A) → J a → ComplexModel N → ℂ) (z : ComplexModel N) :
    Antitone fun i => hormanderWeight c h i z := by
  intro i j hij
  simp only [hormanderWeight]
  gcongr with a
  · exact hc a
  · exact add_pos_of_pos_of_nonneg (regEps_pos j) (Finset.sum_nonneg fun _ _ => by positivity)
  · exact antitone_regEps hij

/-- Off the zero sets, `sup_i e^{-Φ_{ε_i}} = e^{-Φ} = ∏_a (∑_j |h_{a,j}|²)^{-c_a} (1 + |z|²)^{-1}`
(monotone convergence of the weights, `lem:c0-weight` (1)). -/
theorem iSup_exp_neg_hormanderWeight {c : A → ℝ} (hc : ∀ a, 0 ≤ c a)
    (h : (a : A) → J a → ComplexModel N → ℂ) {z : ComplexModel N}
    (hz : ∀ a, 0 < ∑ j, ‖h a j z‖ ^ 2) :
    ⨆ i, ENNReal.ofReal (Real.exp (-hormanderWeight c h i z)) =
      ENNReal.ofReal ((∏ a, (∑ j, ‖h a j z‖ ^ 2) ^ (-c a)) * (1 + ‖z‖ ^ 2)⁻¹) := by
  have hmono : Monotone fun i => ENNReal.ofReal (Real.exp (-hormanderWeight c h i z)) :=
    fun i j hij => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg
      (antitone_hormanderWeight hc h z hij)))
  have hlim : Tendsto (fun i => hormanderWeight c h i z) atTop
      (𝓝 (∑ a, c a * Real.log (∑ j, ‖h a j z‖ ^ 2) + Real.log (1 + ‖z‖ ^ 2))) := by
    refine (tendsto_finsetSum _ fun a _ => ?_).add tendsto_const_nhds
    have h1 : Tendsto (fun i => regEps i + ∑ j, ‖h a j z‖ ^ 2) atTop
        (𝓝 (0 + ∑ j, ‖h a j z‖ ^ 2)) := tendsto_regEps.add tendsto_const_nhds
    rw [zero_add] at h1
    exact (h1.log (hz a).ne').const_mul _
  have hval : Real.exp (-(∑ a, c a * Real.log (∑ j, ‖h a j z‖ ^ 2) + Real.log (1 + ‖z‖ ^ 2))) =
      (∏ a, (∑ j, ‖h a j z‖ ^ 2) ^ (-c a)) * (1 + ‖z‖ ^ 2)⁻¹ := by
    rw [neg_add, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum, Real.exp_neg (Real.log _),
      Real.exp_log (by positivity)]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Real.rpow_def_of_pos (hz a)]
    congr 1
    ring
  refine tendsto_nhds_unique (tendsto_atTop_iSup hmono) ?_
  rw [← hval]
  exact ENNReal.tendsto_ofReal (Real.continuous_exp.continuousAt.tendsto.comp hlim.neg)

/-- **Hörmander's estimate on `ℂ^N` with polynomial weights** (`lem:c0-hormander-global`), in the
weights of the blueprint. Let `c_a ≥ 0`, `h_{a,j}` entire (`C^∞` holomorphic) and
`e^{-Φ} = sup_i e^{-Φ_{ε_i}}` (`= ∏_a (∑_j |h_{a,j}|²)^{-c_a} (1 + |z|²)^{-1}` off the zero sets,
`iSup_exp_neg_hormanderWeight`). For `θ` smooth with compact support and `f` holomorphic near
`supp θ`, if `∫ |f|² |dθ|² (1 + |z|²)² e^{-Φ} ≤ I < ∞` then there is an entire `G` with
`∫ |θ f - G|² e^{-Φ} ≤ 2 I`; i.e. `u = θ f - G` solves `∂̄ u = ∂̄ (θ f)` on `ℂ^N` with
`∫ |u|² e^{-Φ} ≤ 2 I`. -/
theorem exists_entire_hormander_global_weights {c : A → ℝ} (hc : ∀ a, 0 ≤ c a)
    {h : (a : A) → J a → ComplexModel N → ℂ} (hh : ∀ a j, ContDiff ℂ ∞ (h a j))
    {θ : ComplexModel N → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    {W : Set (ComplexModel N)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    {f : ComplexModel N → ℂ} (hf : DifferentiableOn ℂ f W) {I : ℝ≥0∞} (hI : I ≠ ⊤)
    (hIb : ∫⁻ z, ENNReal.ofReal (poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2) *
      ⨆ i, ENNReal.ofReal (Real.exp (-hormanderWeight c h i z)) ≤ I) :
    ∃ G : ComplexModel N → ℂ, Differentiable ℂ G ∧
      ∫⁻ z, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2) *
        ⨆ i, ENNReal.ofReal (Real.exp (-hormanderWeight c h i z)) ≤ 2 * I := by
  have hh2 : ∀ a j, ContDiff ℂ 2 (h a j) := fun a j => (hh a j).of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨G, hG, -, hsup⟩ := exists_entire_hormander_global (Φ := hormanderWeight c h)
    (fun i => contDiff_weight c hh (regEps_pos i))
    (fun i z ξ => le_leviFormC0_weight hc hh2 (regEps_pos i) z ξ)
    (antitone_hormanderWeight hc h) hθ hθcs hW hts hf hI fun i => by
      refine le_trans (lintegral_mono fun z => ?_) hIb
      rw [ENNReal.ofReal_mul (by have := poleMajorant_nonneg θ f z; positivity)]
      exact mul_le_mul_right
        (le_iSup (fun i => ENNReal.ofReal (Real.exp (-hormanderWeight c h i z))) i) _
  exact ⟨G, hG, hsup⟩

end Weights

end EnvelopeProperty.Char0
