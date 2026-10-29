/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.OTPoint
import EnvelopeProperty.Char0.HormanderGlobal
import EnvelopeProperty.Char0.BergmanFinite
import EnvelopeProperty.Char0.EuclideanBridge

/-!
# `L²` extension from a point with polynomial growth

This file proves `prop:c0-l2-extension`, the remaining part of `cor:c0-bergman-lower`, and part
(3) of `lem:c0-analytic-basics` of the characteristic-zero blueprint
(`blueprint/src/char0.tex`).

Let `g = (g_j)` be polynomials on `ℂ^{n+2}` with `|g|² ≤ C_g (1+|x|²)^D (1+|t|²)^β`, `c > 0`,
`N = n + 2` and `ω = |g|^{-2c} (1 + |z|²)^{-N-1}` (`c0Weight`).

* `not_integrableOn_ball_inv_norm_sub_sq_pow`, `eq_zero_of_lintegral_pole_ne_top`
  (`lem:c0-analytic-basics` (3)): `∫_{B(y,r)} |z - y|^{-2N} dλ = ∞`, hence a function continuous
  at `y` with `∫_{B(y,r)} |u|² |z - y|^{-2N} < ∞` vanishes at `y`;
  `integrableOn_ball_norm_rpow_iff`: `∫_{|s| < δ} |s|^{2κ} dλ(s) < ∞` in `ℂ` iff `κ > -1`.
* `exists_entire_extension` and `exists_polynomial_extension` (`prop:c0-l2-extension`): for every
  compact `K` there is `C_K` such that every `y ∈ K \ Z(g)` admits a polynomial `F` with
  `F(y) = 1`, `∫ |F|² ω ≤ C_K |g(y)|^{-2c}`, `x`-degree `≤ cD + 2` and `t`-degree `≤ cβ + N`.
* `exists_homogeneous_lower_bound_of_bihomogeneous` (`cor:c0-bergman-lower`): for bihomogeneous
  `g_j` of `x`-degree `D`, not all zero, finitely many `x`-homogeneous polynomials `P_k` of
  `x`-degree `≤ cD + 2`, square integrable against `|g|^{-2c}` on compact sets, with
  `|P| ≥ c_K |g|^c` on every compact `K`.

The proof of `prop:c0-l2-extension` follows the blueprint: Ohsawa–Takegoshi at `y`
(`exists_extension_from_point_ball`, on `B(y, 2)`), the cut-off `θ_y` (a `ContDiffBump`, equal
to `1` on `B(y, 1/2)`, supported in `closedBall y 1`), Hörmander on `ℂ^N`
(`exists_entire_hormander_global`) for the weights
`Φ_i = c log (δ_i² + |g|²) + N log (|z - y|² + δ_i²) + log (1 + |z|²)`, `δ_i = 1/(i+1)`, the
vanishing at the pole, and `lem:c0-polynomial-growth`. The analytic work is done on
`ComplexModel N = EuclideanSpace ℂ (Fin N)` (`famSq g z = |g(z)|²`, `regWeight`, `cutoffAt`) and
transported to `Fin (n + 2) → ℂ` by `measurePreserving_euclideanSpace_ofLp`.

Deviations from the blueprint proof: Ohsawa–Takegoshi is applied on `B(y, 2)` (instead of
`B(y, 1)`) so that the cut-off can be supported in `closedBall y 1`; this only changes `C_K`.
-/

open scoped NNReal ENNReal Topology ComplexConjugate ContDiff
open MeasureTheory Metric Set Filter

noncomputable section

namespace EnvelopeProperty.Char0

open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
  ComplexGeometry.AnalyticGeometry.PointPole

/-! ### `lem:c0-analytic-basics` (3) -/

section Pole

variable {N : ℕ}

/-- `ℂ^N` (`N > 0`) is nontrivial. -/
theorem nontrivial_complexModel_of_pos (hN : 0 < N) : Nontrivial (ComplexModel N) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_complexModel]; omega)

/-- **`lem:c0-analytic-basics` (3)**, first half: `|z - y|^{-2N}` is not integrable on any ball
`B(y, r)` of `ℂ^N`. -/
theorem not_integrableOn_ball_inv_norm_sub_sq_pow (hN : 0 < N) (y : ComplexModel N) {r : ℝ}
    (hr : 0 < r) : ¬ IntegrableOn (fun z => ((‖z - y‖ ^ 2) ^ N)⁻¹) (ball y r) := by
  have := nontrivial_complexModel_of_pos hN
  intro hint
  have hmp : MeasurePreserving (fun x : ComplexModel N => x + y) volume volume :=
    measurePreserving_add_right volume y
  have hpre : (fun x : ComplexModel N => x + y) ⁻¹' ball y r = ball 0 r := by
    ext x; simp [mem_ball, dist_eq_norm]
  have h0 : IntegrableOn (fun x : ComplexModel N => ((‖x‖ ^ 2) ^ N)⁻¹) (ball 0 r) := by
    have := (hmp.integrableOn_comp_preimage (measurableEmbedding_addRight y)).2 hint
    rw [hpre] at this
    simpa [Function.comp_def] using this
  have h1 := (integrableOn_fun_norm_addHaar (μ := volume) (f := fun t : ℝ => ((t ^ 2) ^ N)⁻¹)
    (r := r)).1 h0
  rw [finrank_real_complexModel] at h1
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 r) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have ht0 : 0 < t := ht.1
    dsimp only
    rw [Real.rpow_neg_one, smul_eq_mul, ← pow_mul]
    obtain ⟨k, hk⟩ : ∃ k, 2 * N = k + 1 := ⟨2 * N - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ ht0.ne'), one_mul]
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hr).1 h2)

/-- **Vanishing at the pole** (`prop:c0-l2-extension`, step (4)): a function `u` continuous at
`y` with `∫_{B(y,r)} |u|² |z - y|^{-2N} < ∞` vanishes at `y`. -/
theorem eq_zero_of_lintegral_pole_ne_top (hN : 0 < N) {u : ComplexModel N → ℂ}
    {y : ComplexModel N} {r : ℝ} (hr : 0 < r) (hu : ContinuousAt u y)
    (hfin : ∫⁻ z in ball y r, ENNReal.ofReal (‖u z‖ ^ 2 * ((‖z - y‖ ^ 2) ^ N)⁻¹) ≠ ⊤) :
    u y = 0 := by
  by_contra huy
  set m : ℝ := ‖u y‖ ^ 2 / 2 with hm
  have hm0 : 0 < m := by rw [hm]; have := norm_pos_iff.2 huy; positivity
  have hlt : m < ‖u y‖ ^ 2 := by rw [hm]; linarith
  have hev : ∀ᶠ z in 𝓝 y, m < ‖u z‖ ^ 2 :=
    ((continuous_norm.continuousAt.comp hu).pow 2).eventually (lt_mem_nhds hlt)
  obtain ⟨r', hr', hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set s := min r r' with hs
  have hs0 : 0 < s := lt_min hr hr'
  set P : ComplexModel N → ℝ := fun z => ((‖z - y‖ ^ 2) ^ N)⁻¹ with hP
  have hPm : Measurable P := by
    have : Continuous fun z : ComplexModel N => (‖z - y‖ ^ 2) ^ N := by fun_prop
    exact this.measurable.inv
  have hinf : ∫⁻ z in ball y s, ENNReal.ofReal (P z) = ⊤ := by
    by_contra hne
    refine not_integrableOn_ball_inv_norm_sub_sq_pow hN y hs0 ⟨hPm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)]
    exact lt_top_iff_ne_top.2 hne
  apply hfin
  refine eq_top_iff.2 ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal m * ∫⁻ z in ball y s, ENNReal.ofReal (P z) := by
        rw [hinf, ENNReal.mul_top (by simpa using hm0)]
    _ = ∫⁻ z in ball y s, ENNReal.ofReal (m * P z) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_mul hm0.le]
    _ ≤ ∫⁻ z in ball y s, ENNReal.ofReal (‖u z‖ ^ 2 * P z) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ENNReal.ofReal_le_ofReal ?_
        have := hball z (ball_subset_ball (min_le_right _ _) hz)
        exact mul_le_mul_of_nonneg_right this.le (by positivity)
    _ ≤ ∫⁻ z in ball y r, ENNReal.ofReal (‖u z‖ ^ 2 * P z) :=
        lintegral_mono_set (ball_subset_ball (min_le_left _ _))

end Pole

/-- **`lem:c0-analytic-basics` (3)**, second half: for `δ > 0` and `κ ∈ ℝ`,
`∫_{|s| < δ} |s|^{2κ} dλ(s) < ∞` in `ℂ` if and only if `κ > -1`. -/
theorem integrableOn_ball_norm_rpow_iff {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    IntegrableOn (fun s : ℂ => ‖s‖ ^ (2 * κ)) (ball 0 δ) ↔ -1 < κ := by
  rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun t : ℝ => t ^ (2 * κ)),
    Complex.finrank_real_complex]
  have : IntegrableOn (fun t : ℝ => (t ^ (2 - 1) • t ^ (2 * κ))) (Ioo 0 δ) ↔
      IntegrableOn (fun t : ℝ => t ^ (2 * κ + 1)) (Ioo 0 δ) := by
    refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo
    rw [smul_eq_mul, Real.rpow_add ht.1, Real.rpow_one, mul_comm]
    norm_num
  rw [this, intervalIntegral.integrableOn_Ioo_rpow_iff hδ]
  constructor <;> intro h <;> linarith

/-! ### The cut-off `θ_y` -/

section Cutoff

variable {N : ℕ}

/-- A fixed smooth bump on `ℂ^N`: `1` on `closedBall 0 (1/2)`, support `ball 0 1`. -/
def cutoffBump (N : ℕ) : ContDiffBump (0 : ComplexModel N) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The cut-off `χ_y = χ(· - y)` of `prop:c0-l2-extension`, step (2). -/
def cutoffAt (y z : ComplexModel N) : ℝ := cutoffBump N (z - y)

theorem contDiff_cutoffAt (y : ComplexModel N) : ContDiff ℝ ∞ (cutoffAt y) :=
  (cutoffBump N).contDiff.comp (contDiff_id.sub contDiff_const)

theorem cutoffAt_eq_one {y z : ComplexModel N} (hz : z ∈ ball y (1 / 2)) : cutoffAt y z = 1 :=
  (cutoffBump N).one_of_mem_closedBall (by
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    rw [mem_ball, dist_eq_norm] at hz
    exact hz.le)

theorem cutoffAt_nonneg (y z : ComplexModel N) : 0 ≤ cutoffAt y z := (cutoffBump N).nonneg

theorem cutoffAt_le_one (y z : ComplexModel N) : cutoffAt y z ≤ 1 := (cutoffBump N).le_one

theorem tsupport_cutoffAt_subset (y : ComplexModel N) :
    tsupport (cutoffAt y) ⊆ closedBall y 1 := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  have : z - y ∈ Function.support (cutoffBump N) := hz
  rw [(cutoffBump N).support_eq] at this
  rw [mem_closedBall, dist_eq_norm]
  rw [mem_ball, dist_eq_norm, sub_zero] at this
  exact this.le

theorem hasCompactSupport_cutoffAt (y : ComplexModel N) : HasCompactSupport (cutoffAt y) :=
  (isCompact_closedBall y 1).of_isClosed_subset (isClosed_tsupport _) (tsupport_cutoffAt_subset y)

/-- The derivatives of the cut-offs `χ_y` are bounded uniformly in `y`. -/
theorem exists_norm_fderiv_cutoffAt_le (N : ℕ) :
    ∃ M : ℝ, ∀ y z : ComplexModel N, ‖fderiv ℝ (cutoffAt y) z‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((cutoffBump N).contDiff.continuous_fderiv (n := 1)
    (by simp)).bounded_above_of_compact_support
    ((cutoffBump N).hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨M, fun y z => ?_⟩
  have : fderiv ℝ (cutoffAt y) z = fderiv ℝ (cutoffBump N) (z - y) :=
    fderiv_comp_sub (f := cutoffBump N) y
  rw [this]
  exact hM _

end Cutoff

/-! ### The regularized weights -/

section Weights

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- `|g(z)|² = ∑_j |g_j(z)|²` for polynomials `g_j` on `ℂ^N` (`ComplexModel N`). -/
def famSq (g : ι → MvPolynomial (Fin N) ℂ) (z : ComplexModel N) : ℝ :=
  ∑ j, ‖MvPolynomial.eval (WithLp.ofLp z) (g j)‖ ^ 2

theorem famSq_nonneg (g : ι → MvPolynomial (Fin N) ℂ) (z : ComplexModel N) : 0 ≤ famSq g z :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem contDiff_eval_ofLp (P : MvPolynomial (Fin N) ℂ) {k : WithTop ℕ∞} :
    ContDiff ℂ k fun z : ComplexModel N => MvPolynomial.eval (WithLp.ofLp z) P :=
  contDiff_eval_mvPolynomial_euclidean P

theorem continuous_famSq (g : ι → MvPolynomial (Fin N) ℂ) : Continuous (famSq g) :=
  continuous_finsetSum _ fun j _ => ((contDiff_eval_ofLp (k := 0) (g j)).continuous.norm).pow 2

/-- The smooth weights `Φ_i = c log (ε_i + |g|²) + N log (|z - y|² + ε_i) + log (1 + |z|²)` of
`prop:c0-l2-extension`, decreasing to `Φ = 2φ + 2N log |z - y| + log (1 + |z|²)`. -/
def regWeight (g : ι → MvPolynomial (Fin N) ℂ) (c : ℝ) (y : ComplexModel N) (i : ℕ)
    (z : ComplexModel N) : ℝ :=
  c * Real.log (regEps i + famSq g z) + (N : ℝ) * polePotential y (1 / ((i : ℝ) + 1)) z +
    Real.log (1 + ‖z‖ ^ 2)

theorem contDiff_regWeight (g : ι → MvPolynomial (Fin N) ℂ) (c : ℝ) (y : ComplexModel N)
    (i : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (regWeight g c y i) := by
  have h1 : ContDiff ℝ k fun z => Real.log (regEps i + famSq g z) :=
    contDiff_log_add_sum_normSq (fun j => contDiff_eval_ofLp (g j)) (regEps_pos i)
  exact ((contDiff_const.mul h1).add (contDiff_const.mul
    (contDiff_polePotential (by positivity) y))).add contDiff_log_one_add_norm_sq

/-- **The Levi form bound** for the weights `Φ_i` (`lem:c0-weight` (1), (5)). -/
theorem le_leviForm_regWeight (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (y : ComplexModel N) (i : ℕ) (z ξ : ComplexModel N) :
    ‖ξ‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤ leviForm (regWeight g c y i) z ξ := by
  have hA : ContDiff ℝ 2 fun z => Real.log (regEps i + famSq g z) :=
    contDiff_log_add_sum_normSq (fun j => contDiff_eval_ofLp (g j)) (regEps_pos i)
  have hB : ContDiff ℝ 2 (polePotential y (1 / ((i : ℝ) + 1))) :=
    contDiff_polePotential (by positivity) y
  change ‖ξ‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤ leviFormC0 (fun z => (c * Real.log (regEps i + famSq g z) +
    (N : ℝ) * polePotential y (1 / ((i : ℝ) + 1)) z) + Real.log (1 + ‖z‖ ^ 2)) z ξ
  rw [leviFormC0_add ((contDiff_const.mul hA).add (contDiff_const.mul hB)).contDiffAt
      contDiff_log_one_add_norm_sq.contDiffAt,
    leviFormC0_add (contDiff_const.mul hA).contDiffAt (contDiff_const.mul hB).contDiffAt,
    leviFormC0_const_mul hA.contDiffAt, leviFormC0_const_mul hB.contDiffAt]
  have h1 : 0 ≤ leviFormC0 (fun z => Real.log (regEps i + famSq g z)) z ξ :=
    leviFormC0_log_add_sum_normSq_nonneg (fun j => contDiff_eval_ofLp (g j)) (regEps_pos i) z ξ
  have h2 : 0 ≤ leviFormC0 (polePotential y (1 / ((i : ℝ) + 1))) z ξ :=
    leviForm_polePotential_nonneg (by positivity) y z ξ
  have h3 := le_leviFormC0_log_one_add_norm_sq z ξ
  have h4 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_nonneg hc h1, mul_nonneg h4 h2]

theorem antitone_regWeight (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (y z : ComplexModel N) : Antitone fun i => regWeight g c y i z := by
  intro i j hij
  have he := antitone_regEps hij
  have h1 : Real.log (regEps j + famSq g z) ≤ Real.log (regEps i + famSq g z) :=
    Real.log_le_log (by linarith [regEps_pos j, famSq_nonneg g z]) (by linarith)
  have h2 : polePotential y (1 / ((j : ℝ) + 1)) z ≤ polePotential y (1 / ((i : ℝ) + 1)) z := by
    unfold polePotential
    refine Real.log_le_log (by have := regEps_pos j; unfold regEps at this; positivity) ?_
    have : (1 / ((j : ℝ) + 1)) ^ 2 ≤ (1 / ((i : ℝ) + 1)) ^ 2 := he
    linarith
  have h4 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [regWeight]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 h4]

/-- `e^{-Φ_i} = (ε_i + |g|²)^{-c} (|z - y|² + ε_i)^{-N} (1 + |z|²)^{-1}`. -/
theorem exp_neg_regWeight (g : ι → MvPolynomial (Fin N) ℂ) (c : ℝ) (y : ComplexModel N)
    (i : ℕ) (z : ComplexModel N) :
    Real.exp (-regWeight g c y i z) = (regEps i + famSq g z) ^ (-c) *
      ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹ := by
  have hS : 0 < regEps i + famSq g z := by linarith [regEps_pos i, famSq_nonneg g z]
  have hP : 0 < ‖z - y‖ ^ 2 + regEps i := by linarith [regEps_pos i, sq_nonneg ‖z - y‖]
  have hZ : 0 < 1 + ‖z‖ ^ 2 := by positivity
  rw [regWeight, polePotential, neg_add, neg_add, Real.exp_add, Real.exp_add,
    Real.rpow_def_of_pos hS, ← Real.log_pow, Real.exp_neg (Real.log _),
    Real.exp_log (by positivity),
    Real.exp_neg (Real.log _), Real.exp_log hZ]
  congr 3
  ring

end Weights

/-! ### Pointwise estimates for `prop:c0-l2-extension` -/

section Pointwise

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- The polynomial maps `z ↦ g_j(z)` on `ℂ^N`. -/
def famFun (g : ι → MvPolynomial (Fin N) ℂ) (j : ι) (z : ComplexModel N) : ℂ :=
  MvPolynomial.eval (WithLp.ofLp z) (g j)

omit [Fintype ι] in
theorem differentiable_famFun (g : ι → MvPolynomial (Fin N) ℂ) (j : ι) :
    Differentiable ℂ (famFun g j) :=
  (contDiff_eval_ofLp (k := 1) (g j)).differentiable one_ne_zero

theorem logNormSqFam_famFun (g : ι → MvPolynomial (Fin N) ℂ) (z : ComplexModel N) :
    logNormSqFam (famFun g) z = ENNReal.log (ENNReal.ofReal (famSq g z)) := rfl

/-- The weight `multiplierWeight c (log |g|²) = e^{-c log |g|²}` dominates the regularized
`(ε + |g|²)^{-c}`. -/
theorem ofReal_regEps_add_rpow_le (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    (i : ℕ) (z : ComplexModel N) :
    ENNReal.ofReal ((regEps i + famSq g z) ^ (-c)) ≤
      multiplierWeight c (logNormSqFam (famFun g) z) := by
  rw [logNormSqFam_famFun]
  rcases (famSq_nonneg g z).lt_or_eq with hS | hS
  · rw [multiplierWeight_log_ofReal hS]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hS
      (by linarith [regEps_pos i]) (by linarith))
  · rw [← hS, ENNReal.ofReal_zero, ENNReal.log_zero, multiplierWeight_bot hc]
    exact le_top

/-- The right-hand side of Hörmander's estimate in `prop:c0-l2-extension`, step (3): on the
support of `∂̄ χ_y` (where `1/2 ≤ |z - y| ≤ 1`), `e^{-Φ_i} ≤ 4^N e^{-2φ} (1 + |z|²)^{-1}`. -/
theorem ofReal_poleMajorant_mul_le (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    {y : ComplexModel N} {f : ComplexModel N → ℂ} {Mθ R : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ (cutoffAt y) z‖ ≤ Mθ) (hR : ‖y‖ ≤ R) (i : ℕ) (z : ComplexModel N) :
    ENNReal.ofReal (poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) ^ 2 *
        Real.exp (-regWeight g c y i z)) ≤
      ENNReal.ofReal (Mθ ^ 2 * 4 ^ N * (1 + (R + 1) ^ 2)) * (ball y 2).indicator
        (fun z => ENNReal.ofReal (‖f z‖ ^ 2) *
          multiplierWeight c (logNormSqFam (famFun g) z)) z := by
  by_cases hz0 : poleMajorant (cutoffAt y) f z = 0
  · simp [hz0]
  have hzs : z ∈ tsupport (cutoffAt y) := by
    by_contra h; exact hz0 (poleMajorant_eq_zero_of_notMem_tsupport h)
  have hzK : z ∈ closedBall y 1 := tsupport_cutoffAt_subset y hzs
  have hz2 : z ∈ ball y 2 := closedBall_subset_ball (by norm_num) hzK
  have hzb : 1 / 2 ≤ ‖z - y‖ := by
    by_contra h
    rw [not_le] at h
    exact hz0 (poleMajorant_eq_zero_of_mem_ball (fun w hw => cutoffAt_eq_one hw)
      (by rw [mem_ball, dist_eq_norm]; exact h))
  rw [indicator_of_mem hz2, exp_neg_regWeight]
  have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ 0)
  have hX : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hzR : ‖z‖ ≤ R + 1 := by
    rw [mem_closedBall, dist_eq_norm] at hzK
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hX' : 1 + ‖z‖ ^ 2 ≤ 1 + (R + 1) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg z) hzR 2
    linarith
  have hQ : ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ ≤ 4 ^ N := by
    have h1 : (1 / 4 : ℝ) ≤ ‖z - y‖ ^ 2 + regEps i := by
      have := pow_le_pow_left₀ (by norm_num) hzb 2
      nlinarith [regEps_pos i]
    calc ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ ≤ (((1 : ℝ) / 4) ^ N)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h1 N)
      _ = 4 ^ N := by rw [one_div, inv_pow, inv_inv]
  set s := (regEps i + famSq g z) ^ (-c) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg (by linarith [regEps_pos i, famSq_nonneg g z]) _
  have hPM := poleMajorant_le (f := f) hMθ z
  have hreal : poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) ^ 2 *
      (s * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹) ≤
      Mθ ^ 2 * 4 ^ N * (1 + (R + 1) ^ 2) * ‖f z‖ ^ 2 * s := by
    have e : poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) ^ 2 *
        (s * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹) =
        poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) * s *
          ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ := by
      field_simp
    rw [e]
    have hP0 := poleMajorant_nonneg (cutoffAt y) f z
    have hQ0 : 0 ≤ ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ := by
      have := regEps_pos i; positivity
    calc poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) * s * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹
        ≤ (Mθ ^ 2 * ‖f z‖ ^ 2) * (1 + (R + 1) ^ 2) * s * 4 ^ N := by gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (poleMajorant (cutoffAt y) f z * (1 + ‖z‖ ^ 2) ^ 2 *
        (s * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹))
      ≤ ENNReal.ofReal (Mθ ^ 2 * 4 ^ N * (1 + (R + 1) ^ 2) * ‖f z‖ ^ 2 * s) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Mθ ^ 2 * 4 ^ N * (1 + (R + 1) ^ 2)) *
          (ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal s) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ _ := by
        gcongr
        exact ofReal_regEps_add_rpow_le g hc i z

/-- A lower bound for a supremum by the limit of a minorizing sequence. -/
theorem ofReal_le_iSup_of_tendsto {b e : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 L))
    (hbe : ∀ i, b i ≤ e i) : ENNReal.ofReal L ≤ ⨆ i, ENNReal.ofReal (e i) :=
  le_of_tendsto' (ENNReal.tendsto_ofReal hb)
    fun i => (ENNReal.ofReal_le_ofReal (hbe i)).trans (le_iSup (fun i => ENNReal.ofReal (e i)) i)

/-- Near the pole: `|z - y|^{-2N} ≤ L sup_i e^{-Φ_i(z)}` where `L` depends on upper bounds `M`
of `|g(z)|²` and `R` of `|z|` (`prop:c0-l2-extension`, step (4)). -/
theorem ofReal_pole_le_iSup (hN : 0 < N) (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    {y z : ComplexModel N} {M R : ℝ} (hM : famSq g z ≤ M) (hzR : ‖z‖ ≤ R) :
    ENNReal.ofReal (((‖z - y‖ ^ 2) ^ N)⁻¹) ≤ ENNReal.ofReal ((1 + M) ^ c * (1 + R ^ 2)) *
      ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z)) := by
  rcases eq_or_ne z y with rfl | hzy
  · simp [zero_pow (by omega : N ≠ 0)]
  have hP : 0 < ‖z - y‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hzy); positivity
  have hM0 : 0 < 1 + M := by linarith [famSq_nonneg g z]
  set L := (1 + M) ^ c * (1 + R ^ 2) with hL
  have hLpos : 0 < L := by positivity
  have hb : Tendsto (fun i => L⁻¹ * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹) atTop
      (𝓝 (L⁻¹ * ((‖z - y‖ ^ 2) ^ N)⁻¹)) := by
    have h1 : Tendsto (fun i => ‖z - y‖ ^ 2 + regEps i) atTop (𝓝 (‖z - y‖ ^ 2 + 0)) :=
      tendsto_const_nhds.add tendsto_regEps
    rw [add_zero] at h1
    exact ((h1.pow N).inv₀ (by positivity)).const_mul _
  have hbe : ∀ i, L⁻¹ * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ ≤ Real.exp (-regWeight g c y i z) := by
    intro i
    rw [exp_neg_regWeight]
    have hS : 0 < regEps i + famSq g z := by linarith [regEps_pos i, famSq_nonneg g z]
    have h1 : ((1 + M) ^ c)⁻¹ ≤ (regEps i + famSq g z) ^ (-c) := by
      rw [← Real.rpow_neg hM0.le]
      exact Real.rpow_le_rpow_of_nonpos hS (by linarith [regEps_le_one i]) (by linarith)
    have h2 : (1 + R ^ 2)⁻¹ ≤ (1 + ‖z‖ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    have hQ : 0 ≤ ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ := by have := regEps_pos i; positivity
    rw [hL, mul_inv]
    calc ((1 + M) ^ c)⁻¹ * (1 + R ^ 2)⁻¹ * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹
        ≤ (regEps i + famSq g z) ^ (-c) * (1 + ‖z‖ ^ 2)⁻¹ * ((‖z - y‖ ^ 2 + regEps i) ^ N)⁻¹ := by
          gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (((‖z - y‖ ^ 2) ^ N)⁻¹)
      = ENNReal.ofReal L * ENNReal.ofReal (L⁻¹ * ((‖z - y‖ ^ 2) ^ N)⁻¹) := by
        rw [← ENNReal.ofReal_mul hLpos.le, ← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul]
    _ ≤ _ := by gcongr; exact ofReal_le_iSup_of_tendsto hb hbe

/-- Away from the pole: `ω = |g|^{-2c} (1 + |z|²)^{-N-1} ≤ (2 (1 + R²))^N sup_i e^{-Φ_i}` for
`|y| ≤ R` (`prop:c0-l2-extension`, step (5)). -/
theorem ofReal_c0Weight_le_iSup (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    {y z : ComplexModel N} {R : ℝ} (hyR : ‖y‖ ≤ R) (hzy : z ≠ y) :
    ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1))) ≤
      ENNReal.ofReal ((2 * (1 + R ^ 2)) ^ N) *
        ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z)) := by
  rcases (famSq_nonneg g z).lt_or_eq with hS | hS
  swap
  · rw [← hS, Real.zero_rpow (by linarith), zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  have hP : 0 < ‖z - y‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hzy); positivity
  have hX : 0 < 1 + ‖z‖ ^ 2 := by positivity
  set Kc := (2 * (1 + R ^ 2)) ^ N with hKc
  have hKc0 : 0 < Kc := by positivity
  set L := famSq g z ^ (-c) * ((‖z - y‖ ^ 2) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹ with hLdef
  have hlim : Tendsto (fun i => Real.exp (-regWeight g c y i z)) atTop (𝓝 L) := by
    simp only [exp_neg_regWeight]
    have h1 : Tendsto (fun i => regEps i + famSq g z) atTop (𝓝 (0 + famSq g z)) :=
      tendsto_regEps.add tendsto_const_nhds
    have h2 : Tendsto (fun i => ‖z - y‖ ^ 2 + regEps i) atTop (𝓝 (‖z - y‖ ^ 2 + 0)) :=
      tendsto_const_nhds.add tendsto_regEps
    rw [zero_add] at h1
    rw [add_zero] at h2
    exact ((h1.rpow_const (Or.inl hS.ne')).mul ((h2.pow N).inv₀ (by positivity))).mul
      tendsto_const_nhds
  have hreal : famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1)) ≤ Kc * L := by
    have hpow : (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1)) = ((1 + ‖z‖ ^ 2) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hX.le, show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_succ, mul_inv]
    have hPN : (‖z - y‖ ^ 2) ^ N ≤ Kc * (1 + ‖z‖ ^ 2) ^ N := by
      rw [hKc, ← mul_pow]
      refine pow_le_pow_left₀ hP.le ?_ N
      have h1 : ‖z - y‖ ≤ ‖z‖ + ‖y‖ := norm_sub_le _ _
      have h2 : ‖z - y‖ ^ 2 ≤ (‖z‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyR 2
      nlinarith [sq_nonneg (‖z‖ - ‖y‖), norm_nonneg z, norm_nonneg y,
        mul_nonneg (sq_nonneg ‖z‖) (sq_nonneg ‖y‖)]
    have hinv : ((1 + ‖z‖ ^ 2) ^ N)⁻¹ ≤ Kc * ((‖z - y‖ ^ 2) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
      linarith
    rw [hpow, hLdef]
    have hs0 : 0 ≤ famSq g z ^ (-c) := Real.rpow_nonneg (famSq_nonneg g z) _
    calc famSq g z ^ (-c) * (((1 + ‖z‖ ^ 2) ^ N)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹)
        ≤ famSq g z ^ (-c) * ((Kc * ((‖z - y‖ ^ 2) ^ N)⁻¹) * (1 + ‖z‖ ^ 2)⁻¹) := by
          gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1)))
      ≤ ENNReal.ofReal (Kc * L) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal Kc * ENNReal.ofReal L := ENNReal.ofReal_mul hKc0.le
    _ ≤ _ := by gcongr; exact ofReal_le_iSup_of_tendsto hlim fun i => le_rfl

end Pointwise

/-! ### `prop:c0-l2-extension` on `ℂ^N` -/

section Extension

variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem multiplierWeight_one_coe_mul (c : ℝ) (a : EReal) :
    multiplierWeight 1 ((c : EReal) * a) = multiplierWeight c a := by
  simp [multiplierWeight]

/-- **`L²` extension from a point with polynomial growth, analytic part**
(`prop:c0-l2-extension`, steps (1)–(5)). Let `g_j` be polynomials on `ℂ^N` (`N > 0`), `c > 0` and
`ω = |g|^{-2c} (1 + |z|²)^{-N-1}`. For every compact `K` there is `C_K` such that for every
`y ∈ K` with `g(y) ≠ 0` there is an entire `G` with `G(y) = 1` and
`∫ |G|² ω dλ ≤ C_K |g(y)|^{-2c}`. -/
theorem exists_entire_extension (hN : 0 < N) (g : ι → MvPolynomial (Fin N) ℂ) {c : ℝ}
    (hc : 0 < c) {K : Set (ComplexModel N)} (hK : IsCompact K) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ y ∈ K, famSq g y ≠ 0 → ∃ G : ComplexModel N → ℂ,
      Differentiable ℂ G ∧ G y = 1 ∧
      ∫⁻ z, ENNReal.ofReal (‖G z‖ ^ 2) *
          ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1))) ≤
        ENNReal.ofReal (CK * famSq g y ^ (-c)) := by
  obtain ⟨C₁, hC₁, hOT⟩ := exists_extension_from_point_ball (N := N) (r := 2) two_pos
  obtain ⟨R', hR'⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  set R := max R' 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ y ∈ K, ‖y‖ ≤ R := fun y hy => by
    have := hR' y hy; rw [norm_norm] at this; exact this.trans (le_max_left _ _)
  obtain ⟨Mθ, hMθ⟩ := exists_norm_fderiv_cutoffAt_le N
  have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ 0 0)
  set B := Mθ ^ 2 * 4 ^ N * (1 + (R + 1) ^ 2) with hB
  set Kc := (2 * (1 + R ^ 2)) ^ N with hKc
  have hB0 : 0 ≤ B := by positivity
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨2 * C₁ + 4 * Kc * (B * C₁), by positivity, fun y hy hSy => ?_⟩
  have hSpos : 0 < famSq g y := lt_of_le_of_ne (famSq_nonneg g y) (Ne.symm hSy)
  set sy := famSq g y ^ (-c) with hsy
  have hsy0 : 0 ≤ sy := Real.rpow_nonneg hSpos.le _
  set wg : ComplexModel N → ℝ≥0∞ := fun z => multiplierWeight c (logNormSqFam (famFun g) z)
    with hwg
  have hwgy : wg y = ENNReal.ofReal sy := by
    simp only [hwg, logNormSqFam_famFun]; exact multiplierWeight_log_ofReal hSpos c
  -- (1) Ohsawa–Takegoshi on `B(y, 2)`
  have hpsh : PlurisubharmonicOn (fun z => (c : EReal) * logNormSqFam (famFun g) z) (ball y 2) :=
    fun z _ => plurisubharmonicOn_mul_logNormSqFam (differentiable_famFun g) hc z (mem_univ z)
  obtain ⟨f, hf, hfy, hfint⟩ := hOT y _ hpsh 1 one_pos
  simp only [multiplierWeight_one_coe_mul] at hfint
  -- (2) the cut-off and (3) Hörmander on `ℂ^N`
  set θ := cutoffAt y with hθ
  have htsW : tsupport θ ⊆ ball y 2 :=
    (tsupport_cutoffAt_subset y).trans (closedBall_subset_ball (by norm_num))
  set I : ℝ≥0∞ := ENNReal.ofReal B * (ENNReal.ofReal C₁ * wg y) with hI
  have hItop : I ≠ ⊤ := by rw [hI, hwgy]; finiteness
  have hIb : ∀ i, ∫⁻ z, ENNReal.ofReal (poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 *
      Real.exp (-regWeight g c y i z)) ≤ I := by
    intro i
    calc ∫⁻ z, ENNReal.ofReal (poleMajorant θ f z * (1 + ‖z‖ ^ 2) ^ 2 *
          Real.exp (-regWeight g c y i z))
        ≤ ∫⁻ z, ENNReal.ofReal B * (ball y 2).indicator
          (fun z => ENNReal.ofReal (‖f z‖ ^ 2) * wg z) z :=
          lintegral_mono fun z => ofReal_poleMajorant_mul_le g hc (hMθ y) (hR y hy) i z
      _ = ENNReal.ofReal B * ∫⁻ z in ball y 2, ENNReal.ofReal (‖f z‖ ^ 2) * wg z := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_indicator measurableSet_ball]
      _ ≤ I := mul_le_mul_right hfint _
  obtain ⟨G, hGd, -, hGsup⟩ := exists_entire_hormander_global
    (fun i => contDiff_regWeight g c y i) (fun i z ξ => le_leviForm_regWeight g hc.le y i z ξ)
    (fun z => antitone_regWeight g hc.le y z) (contDiff_cutoffAt y) (hasCompactSupport_cutoffAt y)
    isOpen_ball htsW hf hItop hIb
  set u : ComplexModel N → ℂ := fun z => cutProd θ f z - G z with hu
  -- (4) `u(y) = 0`, hence `G(y) = 1`
  have hu_eq : ∀ z ∈ ball y (1 / 2), u z = f z - G z := fun z hz => by
    have h1 : θ z = 1 := cutoffAt_eq_one hz
    simp [hu, cutProd, h1]
  have hucont : ContinuousAt u y := by
    have h1 : ContinuousAt (fun z => f z - G z) y :=
      ((hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self two_pos))).sub
        (hGd y)).continuousAt
    refine h1.congr ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))]
      with z hz
    exact (hu_eq z hz).symm
  obtain ⟨M', hM'⟩ := (isCompact_closedBall y 1).exists_bound_of_continuousOn
    (continuous_famSq g).continuousOn
  have hM : ∀ z ∈ ball y (1 / 2), famSq g z ≤ M' := fun z hz => by
    have := hM' z (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hzR : ∀ z ∈ ball y (1 / 2), ‖z‖ ≤ R + 1 := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith [hR y hy]
  set Ly := (1 + M') ^ c * (1 + (R + 1) ^ 2) with hLy
  have hpole : ∫⁻ z in ball y (1 / 2), ENNReal.ofReal (‖u z‖ ^ 2 * ((‖z - y‖ ^ 2) ^ N)⁻¹) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal Ly * (2 * I)) (by finiteness) ?_
    calc ∫⁻ z in ball y (1 / 2), ENNReal.ofReal (‖u z‖ ^ 2 * ((‖z - y‖ ^ 2) ^ N)⁻¹)
        ≤ ∫⁻ z in ball y (1 / 2), ENNReal.ofReal Ly * (ENNReal.ofReal (‖u z‖ ^ 2) *
          ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z))) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          rw [ENNReal.ofReal_mul (by positivity), mul_left_comm]
          exact mul_le_mul_right (ofReal_pole_le_iSup hN g hc (hM z hz) (hzR z hz)) _
      _ ≤ ∫⁻ z, ENNReal.ofReal Ly * (ENNReal.ofReal (‖u z‖ ^ 2) *
          ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z))) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal Ly * ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) *
          ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Ly * (2 * I) := mul_le_mul_right hGsup _
  have huy : u y = 0 := eq_zero_of_lintegral_pole_ne_top hN (by norm_num) hucont hpole
  have hGy : G y = 1 := by
    have := hu_eq y (mem_ball_self (by norm_num))
    rw [huy, hfy] at this
    linear_combination this
  refine ⟨G, hGd, hGy, ?_⟩
  -- (5) the `L²` bound
  set wt : ComplexModel N → ℝ := fun z => famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-((N : ℝ) + 1))
    with hwt
  have hwt0 : ∀ z, 0 ≤ wt z := fun z =>
    mul_nonneg (Real.rpow_nonneg (famSq_nonneg g z) _) (Real.rpow_nonneg (by positivity) _)
  have hwtle : ∀ z, wt z ≤ famSq g z ^ (-c) := fun z =>
    mul_le_of_le_one_right (Real.rpow_nonneg (famSq_nonneg g z) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg z]) (by linarith))
  have hcut : Continuous (cutProd θ f) :=
    (contDiff_cutProd isOpen_ball (contDiff_cutoffAt y) hf htsW).continuous
  have hpt : ∀ᵐ z ∂(volume : Measure (ComplexModel N)),
      ENNReal.ofReal (‖G z‖ ^ 2) * ENNReal.ofReal (wt z) ≤
        2 * ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 * famSq g z ^ (-c)) +
          2 * ENNReal.ofReal Kc * (ENNReal.ofReal (‖u z‖ ^ 2) *
            ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z))) := by
    have := nontrivial_complexModel_of_pos hN
    filter_upwards [Measure.ae_ne volume y] with z hzy
    have h1 := norm_sq_le_two_mul_add (cutProd θ f z) (G z)
    calc ENNReal.ofReal (‖G z‖ ^ 2) * ENNReal.ofReal (wt z)
        ≤ ENNReal.ofReal ((2 * ‖cutProd θ f z‖ ^ 2 + 2 * ‖u z‖ ^ 2) * wt z) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h1 (hwt0 z))
      _ = ENNReal.ofReal (2 * (‖cutProd θ f z‖ ^ 2 * wt z)) +
          ENNReal.ofReal (2 * (‖u z‖ ^ 2 * wt z)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (hwt0 z)))
            (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (hwt0 z)))]
          congr 1; ring
      _ = 2 * ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 * wt z) +
          2 * (ENNReal.ofReal (‖u z‖ ^ 2) * ENNReal.ofReal (wt z)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖u z‖ ^ 2), ENNReal.ofReal_ofNat]
      _ ≤ _ := by
          refine add_le_add (mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hwtle z) (by positivity))) 2) ?_
          rw [mul_assoc 2, mul_left_comm (ENNReal.ofReal Kc)]
          exact mul_le_mul_right (mul_le_mul_right
            (ofReal_c0Weight_le_iSup g hc (hR y hy) hzy) _) 2
  have hm1 : AEMeasurable (fun z => 2 * ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 *
      famSq g z ^ (-c))) volume :=
    ((ENNReal.measurable_ofReal.comp (((hcut.norm.pow 2).measurable).mul
      ((continuous_famSq g).measurable.pow_const _))).const_mul 2).aemeasurable
  have hA : ∫⁻ z, ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 * famSq g z ^ (-c)) ≤
      ENNReal.ofReal C₁ * wg y := by
    refine le_trans (lintegral_mono fun z => ?_) ((lintegral_indicator measurableSet_ball
      (f := fun z => ENNReal.ofReal (‖f z‖ ^ 2) * wg z)).le.trans hfint)
    by_cases hz : z ∈ ball y 2
    · rw [indicator_of_mem hz, ENNReal.ofReal_mul (by positivity)]
      have hθf : ‖cutProd θ f z‖ ^ 2 ≤ ‖f z‖ ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [cutProd, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ θ z from cutoffAt_nonneg y z)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cutoffAt_le_one y z)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal hθf) ?_
      simp only [hwg, logNormSqFam_famFun]
      exact ofReal_rpow_neg_le_multiplierWeight (famSq_nonneg g z) hc
    · have : θ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (htsW h)
      simp [cutProd, this]
  calc ∫⁻ z, ENNReal.ofReal (‖G z‖ ^ 2) * ENNReal.ofReal (wt z)
      ≤ ∫⁻ z, (2 * ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 * famSq g z ^ (-c)) +
          2 * ENNReal.ofReal Kc * (ENNReal.ofReal (‖u z‖ ^ 2) *
            ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z)))) := lintegral_mono_ae hpt
    _ = 2 * (∫⁻ z, ENNReal.ofReal (‖cutProd θ f z‖ ^ 2 * famSq g z ^ (-c))) +
          2 * ENNReal.ofReal Kc * ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) *
            ⨆ i, ENNReal.ofReal (Real.exp (-regWeight g c y i z)) := by
        rw [lintegral_add_left' hm1, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ 2 * (ENNReal.ofReal C₁ * wg y) + 2 * ENNReal.ofReal Kc * (2 * I) := by
        gcongr
    _ = ENNReal.ofReal ((2 * C₁ + 4 * Kc * (B * C₁)) * sy) := by
        have e1 : ENNReal.ofReal (2 * C₁ * sy) = 2 * (ENNReal.ofReal C₁ * ENNReal.ofReal sy) := by
          rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_ofNat]
        have e2 : ENNReal.ofReal (4 * Kc * (B * C₁) * sy) = 2 * ENNReal.ofReal Kc *
            (2 * (ENNReal.ofReal B * (ENNReal.ofReal C₁ * ENNReal.ofReal sy))) := by
          rw [show 4 * Kc * (B * C₁) * sy = 2 * Kc * (2 * (B * (C₁ * sy))) by ring,
            ENNReal.ofReal_mul (mul_nonneg (by norm_num) hKc0),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hB0,
            ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_ofNat]
        rw [hI, hwgy, show (2 * C₁ + 4 * Kc * (B * C₁)) * sy =
            2 * C₁ * sy + 4 * Kc * (B * C₁) * sy by ring,
          ENNReal.ofReal_add (by positivity) (by positivity), e1, e2]

end Extension

/-! ### `prop:c0-l2-extension` and `cor:c0-bergman-lower` on `ℂ^{n+2}` -/

section Polynomial

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The weight `ω = |g|^{-2c} (1 + |z|²)^{-N-1}` (`N = n + 2`) of `prop:c0-l2-extension` on
`ℂ^{n+2}` (read as `0` on `Z(g)`, a null set). -/
def c0Weight (g : ι → MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) (w : Fin (n + 2) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (normSqFam g w ^ (-c) * (1 + ∑ i, ‖w i‖ ^ 2) ^ (-((n : ℝ) + 3)))

theorem measurable_c0Weight (g : ι → MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) :
    Measurable (c0Weight g c) := by
  have h : Continuous fun w : Fin (n + 2) → ℂ => 1 + ∑ i, ‖w i‖ ^ 2 := by fun_prop
  exact ENNReal.measurable_ofReal.comp
    (((continuous_normSqFam g).measurable.pow_const _).mul (h.measurable.pow_const _))

theorem c0Weight_ofLp (g : ι → MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ)
    (z : ComplexModel (n + 2)) :
    c0Weight g c z.ofLp =
      ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-(((n + 2 : ℕ) : ℝ) + 1))) := by
  rw [c0Weight, EuclideanSpace.norm_sq_eq]
  congr 3
  push_cast; ring

/-- The zero set `Z(g)` is null in `ComplexModel (n + 2)` as soon as some `g_j ≠ 0`. -/
theorem ae_famSq_ne_zero {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {j : ι} (hj : g j ≠ 0) :
    ∀ᵐ z ∂(volume : Measure (ComplexModel (n + 2))), famSq g z ≠ 0 := by
  have h0 := volume_normSqFam_eq_zero hj
  have hpre : volume ((WithLp.ofLp : ComplexModel (n + 2) → Fin (n + 2) → ℂ) ⁻¹'
      {z | normSqFam g z = 0}) = 0 := by
    rw [measurePreserving_euclideanSpace_ofLp.measure_preimage
      ((isClosed_eq (continuous_normSqFam g) continuous_const).measurableSet.nullMeasurableSet),
      h0]
  rw [ae_iff]
  simpa [famSq, normSqFam] using hpre

/-- **`L²` extension from a point with polynomial growth** (`prop:c0-l2-extension`). Let `g_j`
be polynomials on `ℂ^{n+2}` of `x`-degree `≤ D` and `t`-degree `≤ β`, `c > 0` and
`ω = |g|^{-2c} (1 + |z|²)^{-N-1}` (`c0Weight`). For every compact `K` there is `C_K ≥ 0` such
that for every `y ∈ K \ Z(g)` there is a polynomial `F` with `F(y) = 1`,
`∫ |F|² ω dλ ≤ C_K |g(y)|^{-2c}`, `x`-degree `≤ cD + 2` and `t`-degree `≤ cβ + N`. -/
theorem exists_polynomial_extension (g : ι → MvPolynomial (Fin (n + 2)) ℂ) {D β : ℕ}
    (hdeg : ∀ j, ∀ m ∈ (g j).support, ∑ i : Fin (n + 1), m i.succ ≤ D ∧ m 0 ≤ β) {c : ℝ}
    (hc : 0 < c) {K : Set (Fin (n + 2) → ℂ)} (hK : IsCompact K) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ y ∈ K, normSqFam g y ≠ 0 → ∃ F : MvPolynomial (Fin (n + 2)) ℂ,
      MvPolynomial.eval y F = 1 ∧
      wNormSq (c0Weight g c) F ≤ ENNReal.ofReal (CK * normSqFam g y ^ (-c)) ∧
      ∀ m ∈ F.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ c * D + 2 ∧
        (m 0 : ℝ) ≤ c * β + (n + 2) := by
  set e := EuclideanSpace.equiv (Fin (n + 2)) ℂ with he
  have hK' : IsCompact ((WithLp.toLp 2 : (Fin (n + 2) → ℂ) → ComplexModel (n + 2)) '' K) :=
    hK.image e.symm.continuous
  obtain ⟨CK, hCK0, hCK⟩ := exists_entire_extension (by omega) g hc hK'
  obtain ⟨Cg, hCg, hle⟩ := exists_normSqFam_le g hdeg
  refine ⟨CK, hCK0, fun y hy hSy => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ 0 := by
    by_contra h
    push Not at h
    exact hSy (by simp [normSqFam, h])
  obtain ⟨G, hGd, hGy, hGint⟩ := hCK (WithLp.toLp 2 y) (mem_image_of_mem _ hy) hSy
  set k : ℝ := (n : ℝ) + 3 with hk
  have hk0 : 0 ≤ k := by positivity
  -- `∫ |G|² (1 + |x|²)^{-cD-k} (1 + |t|²)^{-cβ-k} < ∞`
  have hI : ∫⁻ z, ENNReal.ofReal (‖G z‖ ^ 2 * polyWeight (c * D + k) (c * β + k) z.ofLp) < ⊤ := by
    have hpt : ∀ᵐ z ∂(volume : Measure (ComplexModel (n + 2))),
        ENNReal.ofReal (‖G z‖ ^ 2 * polyWeight (c * D + k) (c * β + k) z.ofLp) ≤
          ENNReal.ofReal (Cg ^ c) * (ENNReal.ofReal (‖G z‖ ^ 2) *
            ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-(((n + 2 : ℕ) : ℝ) + 1)))) := by
      filter_upwards [ae_famSq_ne_zero hj] with z hz
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := polyWeight_add_le (c * D) (c * β) hk0 z.ofLp
      have h2 := rpow_neg_le_normSqFam_rpow_neg hCg hc.le hle hz
      have hnorm : (1 + ∑ i, ‖z.ofLp i‖ ^ 2) = 1 + ‖z‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      have hkk : (-(((n + 2 : ℕ) : ℝ) + 1)) = -k := by rw [hk]; push_cast; ring
      rw [hnorm] at h1
      rw [hkk]
      have hCc : 0 < Cg ^ c := Real.rpow_pos_of_pos hCg c
      have h3 : polyWeight (c * D) (c * β) z.ofLp ≤ Cg ^ c * famSq g z ^ (-c) := by
        have : Cg ^ (-c) * Cg ^ c = 1 := by
          rw [← Real.rpow_add hCg, neg_add_cancel, Real.rpow_zero]
        calc polyWeight (c * D) (c * β) z.ofLp
            = Cg ^ c * (Cg ^ (-c) * polyWeight (c * D) (c * β) z.ofLp) := by
              rw [← mul_assoc, mul_comm (Cg ^ c), this, one_mul]
          _ ≤ Cg ^ c * famSq g z ^ (-c) := mul_le_mul_of_nonneg_left h2 hCc.le
      have hX : 0 ≤ (1 + ‖z‖ ^ 2) ^ (-k) := Real.rpow_nonneg (by positivity) _
      calc ‖G z‖ ^ 2 * polyWeight (c * D + k) (c * β + k) z.ofLp
          ≤ ‖G z‖ ^ 2 * (polyWeight (c * D) (c * β) z.ofLp * (1 + ‖z‖ ^ 2) ^ (-k)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ ‖G z‖ ^ 2 * ((Cg ^ c * famSq g z ^ (-c)) * (1 + ‖z‖ ^ 2) ^ (-k)) := by
            gcongr
        _ = _ := by ring
    calc ∫⁻ z, ENNReal.ofReal (‖G z‖ ^ 2 * polyWeight (c * D + k) (c * β + k) z.ofLp)
        ≤ ∫⁻ z, ENNReal.ofReal (Cg ^ c) * (ENNReal.ofReal (‖G z‖ ^ 2) *
            ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-(((n + 2 : ℕ) : ℝ) + 1)))) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (Cg ^ c) * ∫⁻ z, ENNReal.ofReal (‖G z‖ ^ 2) *
            ENNReal.ofReal (famSq g z ^ (-c) * (1 + ‖z‖ ^ 2) ^ (-(((n + 2 : ℕ) : ℝ) + 1))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hGint.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨P, hP, hdegP⟩ := exists_mvPolynomial_of_lintegral_polyWeight_euclidean hGd
    (by positivity) (by positivity) hI
  refine ⟨P, ?_, ?_, fun m hm => ?_⟩
  · have := hP (WithLp.toLp 2 y)
    rw [hGy] at this
    exact this.symm
  · have hmp := measurePreserving_euclideanSpace_ofLp (ι := Fin (n + 2))
    have hemb : MeasurableEmbedding (WithLp.ofLp : ComplexModel (n + 2) → Fin (n + 2) → ℂ) :=
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [wNormSq, ← hmp.lintegral_comp_emb hemb]
    refine le_of_eq_of_le (lintegral_congr fun z => ?_) hGint
    rw [c0Weight_ofLp, ← hP z, mul_comm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  · obtain ⟨h1, h2⟩ := hdegP m hm
    constructor
    · linarith
    · linarith

end Polynomial

section Corollary

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- `ω λ` is invariant under `x ↦ e^{iϑ} x` for bihomogeneous `g_j` of the same `x`-degree. -/
theorem c0Weight_xtRot {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {D : ℕ}
    (hg : ∀ j, ∃ l, IsXTBihomogeneous D l (g j)) (c ϑ : ℝ) (z : Fin (n + 2) → ℂ) :
    c0Weight g c (xtRot ϑ 0 z) = c0Weight g c z := by
  have hsum : ∑ i, ‖xtRot ϑ 0 z i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => ‖z i‖ ^ 2), xtRot_zero]
    simp only [xtRot_succ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [c0Weight, c0Weight, normSqFam_xtRot hg, hsum]

/-- `ω > 0` off the null set `Z(g)`. -/
theorem ae_c0Weight_ne_zero {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {j : ι} (hj : g j ≠ 0)
    (c : ℝ) : ∀ᵐ z, c0Weight g c z ≠ 0 := by
  have h0 := volume_normSqFam_eq_zero hj
  rw [← compl_mem_ae_iff] at h0
  filter_upwards [h0] with z hz
  have hS : 0 < normSqFam g z := lt_of_le_of_ne (normSqFam_nonneg g z) (Ne.symm hz)
  have hX : 0 < 1 + ∑ i, ‖z i‖ ^ 2 := by positivity
  rw [c0Weight, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact mul_pos (Real.rpow_pos_of_pos hS _) (Real.rpow_pos_of_pos hX _)

/-- **Polynomials dominating a fractional power** (`cor:c0-bergman-lower`). Let `g_j` be
bihomogeneous polynomials on `ℂ^{n+2}` of `x`-degree `D`, not all zero, and `c > 0`. There are
finitely many `x`-homogeneous polynomials `P_1, …, P_r` of `x`-degree `≤ cD + 2`, each square
integrable against `|g|^{-2c}` on every compact set, such that for every compact `K` there is
`c_K > 0` with `|P| ≥ c_K |g|^c` on `K` (`|P|² = ∑_k |P_k|²`, `|g|² = normSqFam g`). -/
theorem exists_homogeneous_lower_bound_of_bihomogeneous (g : ι → MvPolynomial (Fin (n + 2)) ℂ)
    {D : ℕ} (hg : ∀ j, ∃ l, IsXTBihomogeneous D l (g j)) {j₀ : ι} (hj₀ : g j₀ ≠ 0) {c : ℝ}
    (hc : 0 < c) :
    ∃ s : Finset (MvPolynomial (Fin (n + 2)) ℂ),
      (∀ P ∈ s, (∃ e : ℕ, P.IsWeightedHomogeneous xWeightFin e) ∧
        (∀ m ∈ P.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ c * D + 2) ∧
        ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K →
          ∫⁻ z in K, ENNReal.ofReal (normSqFam g z ^ (-c)) * ‖MvPolynomial.eval z P‖ₑ ^ 2 < ⊤) ∧
      ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
        cK * normSqFam g y ^ (c / 2) ≤ Real.sqrt (∑ P ∈ s, ‖MvPolynomial.eval y P‖ ^ 2) := by
  obtain ⟨β, hdeg⟩ := exists_degree_bounds_of_isBihomogeneous hg
  have hω := measurable_c0Weight g c
  have hext : ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ CK : ℝ, ∀ y ∈ K,
      normSqFam g y ≠ 0 → ∃ F ∈ bergmanSpace (c0Weight g c) (c * D + 2) (c * β + (n + 2)),
        MvPolynomial.eval y F = 1 ∧
        (wNormSq (c0Weight g c) F).toReal ≤ CK * normSqFam g y ^ (-c) := by
    intro K hK
    obtain ⟨CK, hCK0, hCK⟩ := exists_polynomial_extension g hdeg hc hK
    refine ⟨CK, fun y hy hSy => ?_⟩
    obtain ⟨F, hFy, hFn, hFdeg⟩ := hCK y hy hSy
    have hb : 0 ≤ CK * normSqFam g y ^ (-c) :=
      mul_nonneg hCK0 (Real.rpow_nonneg (normSqFam_nonneg g y) _)
    exact ⟨F, (mem_bergmanSpace_iff hω).2 ⟨hFdeg, hFn.trans_lt ENNReal.ofReal_lt_top⟩, hFy,
      ENNReal.toReal_le_of_le_ofReal hb hFn⟩
  obtain ⟨s, hs, hlow⟩ := exists_homogeneous_lower_bound g hc hω (ae_c0Weight_ne_zero hj₀ c)
    (c0Weight_xtRot hg c) _ _ hext
  refine ⟨s, fun P hP => ?_, hlow⟩
  obtain ⟨hPW, hPh⟩ := hs P hP
  obtain ⟨hPdeg, hPfin⟩ := (mem_bergmanSpace_iff hω).1 hPW
  refine ⟨hPh, fun m hm => (hPdeg m hm).1, fun K hK => ?_⟩
  have hXc : Continuous fun w : Fin (n + 2) → ℂ => (1 + ∑ i, ‖w i‖ ^ 2) ^ ((n : ℝ) + 3) :=
    (by fun_prop : Continuous fun w : Fin (n + 2) → ℂ => 1 + ∑ i, ‖w i‖ ^ 2).rpow_const
      fun w => Or.inr (by positivity)
  obtain ⟨Mr, hMr⟩ := hK.exists_bound_of_continuousOn hXc.continuousOn
  have hw : ∀ z ∈ K, ENNReal.ofReal (normSqFam g z ^ (-c)) ≤
      ENNReal.ofReal Mr * c0Weight g c z := by
    intro z hz
    have hX : 0 < 1 + ∑ i, ‖z i‖ ^ 2 := by positivity
    have hM := hMr z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hX.le _)] at hM
    have hMr0 : 0 ≤ Mr := (Real.rpow_nonneg hX.le _).trans hM
    rw [c0Weight, ← ENNReal.ofReal_mul hMr0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 + ∑ i, ‖z i‖ ^ 2) ^ ((n : ℝ) + 3) *
        (1 + ∑ i, ‖z i‖ ^ 2) ^ (-((n : ℝ) + 3)) = 1 := by
      rw [← Real.rpow_add hX, add_neg_cancel, Real.rpow_zero]
    have hs0 : 0 ≤ normSqFam g z ^ (-c) := Real.rpow_nonneg (normSqFam_nonneg g z) _
    have hX0 : 0 ≤ (1 + ∑ i, ‖z i‖ ^ 2) ^ (-((n : ℝ) + 3)) := Real.rpow_nonneg hX.le _
    calc normSqFam g z ^ (-c)
        = normSqFam g z ^ (-c) * ((1 + ∑ i, ‖z i‖ ^ 2) ^ ((n : ℝ) + 3) *
            (1 + ∑ i, ‖z i‖ ^ 2) ^ (-((n : ℝ) + 3))) := by rw [h1, mul_one]
      _ ≤ normSqFam g z ^ (-c) * (Mr * (1 + ∑ i, ‖z i‖ ^ 2) ^ (-((n : ℝ) + 3))) := by
          gcongr
      _ = Mr * (normSqFam g z ^ (-c) * (1 + ∑ i, ‖z i‖ ^ 2) ^ (-((n : ℝ) + 3))) := by ring
  exact (setLIntegral_le_wNormSq hω hK.measurableSet hw P).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPfin)

end Corollary

end EnvelopeProperty.Char0
