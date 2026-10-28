/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.CauchyN

/-!
# Square integrable entire functions of polynomial growth

This file proves `lem:c0-polynomial-growth` of the characteristic-zero blueprint
(`EnvelopeProperty/blueprint/src/char0.tex`): an entire function `F` on `ℂ^{n+1}_x × ℂ_t` with
`∫ |F|² (1 + |x|²)^{-a} (1 + |t|²)^{-b} dλ < ∞` (`a, b ≥ 0`) is a polynomial of `x`-degree
`≤ a - n - 1` and `t`-degree `≤ b - 1`.

## Conventions

Points of `ℂ^{n+2}` are functions `z : Fin (n + 2) → ℂ`; the coordinate `t` is `z 0` and the
coordinates `x_0, …, x_n` are `z i.succ`. This matches `MvPolynomial.finSuccEquiv ℂ (n + 1)`,
which identifies `MvPolynomial (Fin (n + 2)) ℂ` with `(MvPolynomial (Fin (n + 1)) ℂ)[X]`
(`X 0 ↦ X`, `X i.succ ↦ C (X i)`), the ring `R[t]` of `ProjBerk` after base change to `ℂ`.
Lebesgue measure is `volume` on `Fin (n + 2) → ℂ` (the product of the Lebesgue measures of `ℂ`).

## Proof

We follow the blueprint. The Taylor coefficients `c_γ` of `F` (`EnvelopeProperty.Char0.CauchyN`)
satisfy Cauchy's formula on every torus; integrating it over the polyradii in
`[ρ, 2ρ]^{n+1} × [σ, 2σ]` against `∏ r_i dr` (polar coordinates in each variable,
`lintegral_torusPt_le`) bounds `(2π)^{n+2} |c_γ| ρ^{|α|} σ^λ ρ^{2(n+1)} σ²` by `∫_T |F| dλ` on the
polydisc `T` of radii `2ρ, 2σ`. Instead of the Cauchy–Schwarz inequality we use the pointwise
inequality `2|F| ≤ (A w)⁻¹ + A |F|² w` with `A = ρ^{a+n+1} σ^{b+1}`, which gives the same bound
`|c_γ| ≤ K ρ^{a-n-1-|α|} σ^{b-1-λ}` (`taylorCoeff_estimate`). Letting `ρ → ∞` or `σ → ∞` kills
the coefficients of large degree, and the Taylor series is a finite sum.

## Main results

* `lintegral_torusPt_le`: polar coordinates, one variable at a time;
* `taylorCoeff_estimate`, `taylorCoeff_eq_zero_of_lintegral_polyWeight`;
* `exists_mvPolynomial_of_lintegral_polyWeight`: `lem:c0-polynomial-growth`.
-/

open scoped Real NNReal ENNReal Topology
open Complex MeasureTheory Set Filter

noncomputable section

namespace EnvelopeProperty.Char0

/-! ### Polar coordinates on `ℂ^N` in the form used for Cauchy's formula -/

theorem polarCoord_symm_eq_torusPt {N : ℕ} (p : Fin N → ℝ × ℝ) :
    (fun i => Complex.polarCoord.symm (p i)) = torusPt (fun i => (p i).1) (fun i => (p i).2) := by
  funext i
  simp only [Complex.polarCoord_symm_apply, torusPt]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem continuous_torusPt_uncurry {N : ℕ} :
    Continuous fun q : (Fin N → ℝ) × (Fin N → ℝ) => torusPt q.1 q.2 := by
  unfold torusPt
  fun_prop

/-- Integration in polar coordinates, one complex variable at a time, over a set of radii in
`(0, ∞)^N`: `∫_r ∏ r_i ∫_θ f(r e^{iθ}) dθ dr ≤ ∫ f dλ`. -/
theorem lintegral_torusPt_le {N : ℕ} {f : (Fin N → ℂ) → ℝ≥0∞} (hf : Measurable f)
    {B : Fin N → Set ℝ} (hB : ∀ i, B i ⊆ Ioi 0) :
    ∫⁻ r in Set.univ.pi B, ∫⁻ θ in Set.univ.pi (fun _ : Fin N => Ioo (-π) π),
      (∏ i, ENNReal.ofReal (r i)) * f (torusPt r θ) ≤ ∫⁻ z, f z := by
  set Θ : Set (Fin N → ℝ) := Set.univ.pi (fun _ : Fin N => Ioo (-π) π)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => volume)
    (fun _ => volume)
  have hpre : e ⁻¹' (Set.univ.pi B ×ˢ Θ) = Set.univ.pi (fun i => B i ×ˢ Ioo (-π) π) := by
    ext p
    simp [e, Θ, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      Set.mem_pi, forall_and]
  calc ∫⁻ r in Set.univ.pi B, ∫⁻ θ in Θ, (∏ i, ENNReal.ofReal (r i)) * f (torusPt r θ)
      = ∫⁻ q in Set.univ.pi B ×ˢ Θ, (∏ i, ENNReal.ofReal (q.1 i)) * f (torusPt q.1 q.2)
          ∂((Measure.pi fun _ => volume).prod (Measure.pi fun _ => volume)) := by
        rw [setLIntegral_prod]
        · rfl
        refine (Measurable.mul ?_ (hf.comp continuous_torusPt_uncurry.measurable)).aemeasurable
        exact Finset.measurable_prod _ fun i _ =>
          ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).comp measurable_fst)
    _ = ∫⁻ p in Set.univ.pi (fun i => B i ×ˢ Ioo (-π) π), (∏ i, ENNReal.ofReal (p i).1) *
          f (torusPt (fun i => (p i).1) (fun i => (p i).2))
          ∂(Measure.pi fun _ => (volume : Measure ℝ).prod volume) := by
        rw [← hpre]
        exact (he.setLIntegral_comp_preimage_emb e.measurableEmbedding
          (fun q => (∏ i, ENNReal.ofReal (q.1 i)) * f (torusPt q.1 q.2)) _).symm
    _ ≤ ∫⁻ p in Set.univ.pi (fun _ : Fin N => Complex.polarCoord.target),
          (∏ i, ENNReal.ofReal (p i).1) * f (fun i => Complex.polarCoord.symm (p i)) := by
        simp_rw [polarCoord_symm_eq_torusPt]
        refine lintegral_mono_set ?_
        intro p hp
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod] at hp ⊢
        intro i
        rw [Complex.polarCoord_target]
        exact ⟨hB i (hp i).1, (hp i).2⟩
    _ = ∫⁻ z, f z := Complex.lintegral_comp_pi_polarCoord_symm f

/-- Cauchy's formula, integrated against `|·|`:
`(2π)^N |c_γ| r^γ ≤ ∫_{(-π,π)^N} |F(r e^{iθ})| dθ`. -/
theorem ofReal_taylorCoeff_le_lintegral {N : ℕ} {F : (Fin N → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {r : Fin N → ℝ} (hr : ∀ i, 0 < r i) (γ : Fin N → ℕ) :
    ENNReal.ofReal ((2 * π) ^ N * ‖taylorCoeff F γ‖ * ∏ i, r i ^ γ i) ≤
      ∫⁻ θ in Set.univ.pi (fun _ : Fin N => Ioo (-π) π), ‖F (torusPt r θ)‖ₑ := by
  have h := setIntegral_Ioo_eq_taylorCoeff hF hr γ
  have h2 := enorm_integral_le_lintegral_enorm
    (μ := volume.restrict (Set.univ.pi fun _ : Fin N => Ioo (-π) π))
    (fun θ => torusChar γ θ * F (torusPt r θ))
  rw [h] at h2
  have h3 : ENNReal.ofReal ((2 * π) ^ N * ‖taylorCoeff F γ‖ * ∏ i, r i ^ γ i) =
      ‖(2 * π : ℂ) ^ N * taylorCoeff F γ * ∏ i, (r i : ℂ) ^ γ i‖ₑ := by
    rw [← ofReal_norm]
    congr 1
    simp [norm_prod, abs_of_pos (hr _), abs_of_pos Real.pi_pos]
  have h4 : ∀ θ, ‖torusChar γ θ * F (torusPt r θ)‖ₑ = ‖F (torusPt r θ)‖ₑ := fun θ => by
    rw [enorm_mul, ← ofReal_norm (torusChar γ θ), norm_torusChar]
    simp
  rw [h3]
  simp_rw [h4] at h2
  exact h2

/-! ### The weights `(1 + |x|²)^{-a} (1 + |t|²)^{-b}` -/

variable {n : ℕ}

/-- `|x|² = ∑_i |x_i|²` for a point `z = (t, x_0, …, x_n)` of `ℂ^{n+2}`; the coordinate `t` is
`z 0` and `x_i = z i.succ`, matching `MvPolynomial.finSuccEquiv`. -/
def xNormSq (z : Fin (n + 2) → ℂ) : ℝ := ∑ i : Fin (n + 1), ‖z i.succ‖ ^ 2

/-- `|t|² = |z 0|²`. -/
def tNormSq (z : Fin (n + 2) → ℂ) : ℝ := ‖z 0‖ ^ 2

/-- The weight `(1 + |x|²)^{-a} (1 + |t|²)^{-b}` of `lem:c0-polynomial-growth`. -/
def polyWeight (a b : ℝ) (z : Fin (n + 2) → ℂ) : ℝ :=
  (1 + xNormSq z) ^ (-a) * (1 + tNormSq z) ^ (-b)

theorem xNormSq_nonneg (z : Fin (n + 2) → ℂ) : 0 ≤ xNormSq z :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem tNormSq_nonneg (z : Fin (n + 2) → ℂ) : 0 ≤ tNormSq z := by
  unfold tNormSq; positivity

theorem polyWeight_pos (a b : ℝ) (z : Fin (n + 2) → ℂ) : 0 < polyWeight a b z := by
  unfold polyWeight
  have := xNormSq_nonneg z
  have := tNormSq_nonneg z
  positivity

/-- The `x`-degree `∑_i γ_{i+1}` of a multi-index on `ℂ^{n+2}`. -/
def xDegFin (γ : Fin (n + 2) → ℕ) : ℕ := ∑ i : Fin (n + 1), γ i.succ

/-- If `C ρ^k ≤ K ρ^a` for all `ρ ≥ 1` and `a < k`, then `C ≤ 0`. -/
theorem nonpos_of_forall_mul_pow_le {C K a : ℝ} {k : ℕ} (hk : a < k)
    (h : ∀ ρ : ℝ, 1 ≤ ρ → C * ρ ^ k ≤ K * ρ ^ a) : C ≤ 0 := by
  have hlim : Tendsto (fun ρ : ℝ => K * ρ ^ (-((k : ℝ) - a))) atTop (𝓝 (K * 0)) :=
    (tendsto_rpow_neg_atTop (by linarith)).const_mul K
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with ρ hρ
  have hρ0 : 0 < ρ := by linarith
  have h1 := h ρ hρ
  have hk' : (0 : ℝ) < ρ ^ k := pow_pos hρ0 k
  rw [neg_sub, Real.rpow_sub hρ0, Real.rpow_natCast, mul_div_assoc']
  rw [le_div_iff₀ hk']
  exact h1


/-- The key estimate in the proof of `lem:c0-polynomial-growth`: for `ρ, σ ≥ 1`,
`|c_γ| ρ^{|α| + n + 1} σ^{λ + 1} ≤ K ρ^a σ^b` where `γ = (λ, α)`. It comes from Cauchy's formula
integrated over the polyradii in `[ρ, 2ρ]^{n+1} × [σ, 2σ]` (polar coordinates) and the inequality
`2|F| ≤ (A w)⁻¹ + A |F|² w` on the polydisc of radii `2ρ, 2σ`. -/
theorem taylorCoeff_estimate {F : (Fin (n + 2) → ℂ) → ℂ} (hF : Differentiable ℂ F) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z) ≠ ∞) (γ : Fin (n + 2) → ℕ) :
    ∃ K : ℝ, ∀ ρ σ : ℝ, 1 ≤ ρ → 1 ≤ σ →
      ‖taylorCoeff F γ‖ * (ρ ^ (xDegFin γ + (n + 1)) * σ ^ (γ 0 + 1)) ≤ K * (ρ ^ a * σ ^ b) := by
  set I := ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z) with hI_def
  set IR := I.toReal with hIR
  have hIR0 : 0 ≤ IR := ENNReal.toReal_nonneg
  set c₁ : ℝ := (5 * (n + 1 : ℝ)) ^ a * 5 ^ b with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  refine ⟨(c₁ * (4 * π) ^ (n + 2) + IR) / (2 * (2 * π) ^ (n + 2)), ?_⟩
  intro ρ σ hρ hσ
  have hρ0 : 0 < ρ := by linarith
  have hσ0 : 0 < σ := by linarith
  set r0 : Fin (n + 2) → ℝ := Fin.cons σ (fun _ => ρ) with hr0_def
  have hr0 : ∀ i, 0 < r0 i := fun i =>
    Fin.cases (by simpa [r0] using hσ0) (fun j => by simpa [r0] using hρ0) i
  set α := ρ ^ a with hα_def
  set β := σ ^ b with hβ_def
  have hα : 0 < α := Real.rpow_pos_of_pos hρ0 a
  have hβ : 0 < β := Real.rpow_pos_of_pos hσ0 b
  set A := α * ρ ^ (n + 1) * (β * σ) with hA_def
  have hA : 0 < A := by positivity
  set Cw : ℝ := (1 + 4 * (n + 1) * ρ ^ 2) ^ a * (1 + 4 * σ ^ 2) ^ b with hCw_def
  set T : Set (Fin (n + 2) → ℂ) := Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (2 * r0 i)
    with hT_def
  have hT : MeasurableSet T := MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  -- (a) the lower bound, from Cauchy's formula and polar coordinates
  set B : Fin (n + 2) → Set ℝ := fun i => Icc (r0 i) (2 * r0 i) with hB_def
  have hB : ∀ i, B i ⊆ Ioi 0 := fun i x hx => lt_of_lt_of_le (hr0 i) hx.1
  have hBm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  set X0 : ℝ := (2 * π) ^ (n + 2) * ‖taylorCoeff F γ‖ * ∏ i, r0 i ^ γ i with hX0_def
  have hprod0 : 0 ≤ ∏ i, r0 i ^ γ i := Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i).le _
  have hX0 : 0 ≤ X0 := by positivity
  have hmeasT : Measurable (T.indicator fun z => ‖F z‖ₑ) :=
    (hF.continuous.measurable.enorm).indicator hT
  have hlow : ENNReal.ofReal ((∏ i, r0 i) ^ 2 * X0) ≤ ∫⁻ z, T.indicator (fun z => ‖F z‖ₑ) z := by
    calc ENNReal.ofReal ((∏ i, r0 i) ^ 2 * X0)
        = ∫⁻ r in Set.univ.pi B, (∏ i, ENNReal.ofReal (r0 i)) * ENNReal.ofReal X0 := by
          rw [setLIntegral_const, volume_pi_pi]
          have hvol : ∀ i, volume (B i) = ENNReal.ofReal (r0 i) := fun i => by
            simp only [hB_def, Real.volume_Icc]
            ring_nf
          simp_rw [hvol]
          rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (hr0 i).le),
            ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hr0 i).le),
            ← ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun i _ => (hr0 i).le) hX0)]
          congr 1
          ring
      _ ≤ ∫⁻ r in Set.univ.pi B, ∫⁻ θ in Set.univ.pi (fun _ : Fin (n + 2) => Ioo (-π) π),
            (∏ i, ENNReal.ofReal (r i)) * T.indicator (fun z => ‖F z‖ₑ) (torusPt r θ) := by
          refine lintegral_mono_ae ((ae_restrict_iff' hBm).2
            (Filter.Eventually.of_forall fun r hr => ?_))
          have hrB : ∀ i, r i ∈ B i := fun i => hr i (Set.mem_univ i)
          have hrpos : ∀ i, 0 < r i := fun i => hB i (hrB i)
          have hmem : ∀ θ, torusPt r θ ∈ T := fun θ i _ => by
            simp only [Metric.mem_closedBall, dist_zero_right,
              norm_torusPt (fun i => (hrpos i).le)]
            exact (hrB i).2
          simp_rw [Set.indicator_of_mem (hmem _)]
          rw [lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top)]
          refine mul_le_mul' ?_ ?_
          · exact Finset.prod_le_prod' fun i _ => ENNReal.ofReal_le_ofReal (hrB i).1
          · refine le_trans (ENNReal.ofReal_le_ofReal ?_)
              (ofReal_taylorCoeff_le_lintegral hF hrpos γ)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.prod_le_prod (fun i _ => pow_nonneg (hr0 i).le _)
              fun i _ => pow_le_pow_left₀ (hr0 i).le (hrB i).1 _
      _ ≤ ∫⁻ z, T.indicator (fun z => ‖F z‖ₑ) z := lintegral_torusPt_le hmeasT hB
  -- (b) the upper bound
  have hWCw : ∀ z ∈ T, 1 ≤ Cw * polyWeight a b z := by
    intro z hz
    have hzi : ∀ i, ‖z i‖ ≤ 2 * r0 i := fun i => by simpa using hz i (Set.mem_univ i)
    have hx : xNormSq z ≤ 4 * (n + 1) * ρ ^ 2 := by
      unfold xNormSq
      calc ∑ i : Fin (n + 1), ‖z i.succ‖ ^ 2 ≤ ∑ i : Fin (n + 1), (2 * ρ) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
              (by simpa [r0] using hzi i.succ) 2
        _ = 4 * (n + 1) * ρ ^ 2 := by simp; ring
    have ht : tNormSq z ≤ 4 * σ ^ 2 := by
      unfold tNormSq
      calc ‖z 0‖ ^ 2 ≤ (2 * σ) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (by simpa [r0] using hzi 0) 2
        _ = 4 * σ ^ 2 := by ring
    have hx1 : 0 < 1 + xNormSq z := by linarith [xNormSq_nonneg z]
    have ht1 : 0 < 1 + tNormSq z := by linarith [tNormSq_nonneg z]
    have h1 : (1 + xNormSq z) ^ a ≤ (1 + 4 * (n + 1) * ρ ^ 2) ^ a :=
      Real.rpow_le_rpow hx1.le (by linarith) ha
    have h2 : (1 + tNormSq z) ^ b ≤ (1 + 4 * σ ^ 2) ^ b :=
      Real.rpow_le_rpow ht1.le (by linarith) hb
    have hx0 : 0 < (1 + xNormSq z) ^ a := Real.rpow_pos_of_pos hx1 a
    have ht0 : 0 < (1 + tNormSq z) ^ b := Real.rpow_pos_of_pos ht1 b
    unfold polyWeight
    rw [Real.rpow_neg hx1.le, Real.rpow_neg ht1.le]
    have : Cw * (((1 + xNormSq z) ^ a)⁻¹ * ((1 + tNormSq z) ^ b)⁻¹) =
        ((1 + 4 * (n + 1) * ρ ^ 2) ^ a / (1 + xNormSq z) ^ a) *
          ((1 + 4 * σ ^ 2) ^ b / (1 + tNormSq z) ^ b) := by
      simp only [hCw_def]
      field_simp
    rw [this]
    exact one_le_mul_of_one_le_of_one_le ((one_le_div hx0).2 h1) ((one_le_div ht0).2 h2)
  have hpt : ∀ z, T.indicator (fun z => ‖F z‖ₑ) z ≤
      T.indicator (fun _ => ENNReal.ofReal (Cw / (2 * A))) z +
        ENNReal.ofReal (A / 2) * ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z) := by
    intro z
    by_cases hz : z ∈ T
    · have hW := polyWeight_pos a b z
      have hCw0 : 0 ≤ Cw := by positivity
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hWCw z hz
      set X := ‖F z‖
      set W := polyWeight a b z
      have hX : 0 ≤ X := norm_nonneg _
      have key : 0 ≤ Cw + A ^ 2 * X ^ 2 * W - 2 * A * X := by
        have e : W * (Cw + A ^ 2 * X ^ 2 * W - 2 * A * X) = (Cw * W - 1) + (A * X * W - 1) ^ 2 := by
          ring
        have h2 : 0 ≤ W * (Cw + A ^ 2 * X ^ 2 * W - 2 * A * X) := by
          rw [e]; nlinarith [sq_nonneg (A * X * W - 1)]
        exact (mul_nonneg_iff_of_pos_left hW).1 h2
      have e2 : Cw / (2 * A) + A / 2 * (X ^ 2 * W) - X =
          (Cw + A ^ 2 * X ^ 2 * W - 2 * A * X) / (2 * A) := by
        field_simp
      have := div_nonneg key (by positivity : (0 : ℝ) ≤ 2 * A)
      linarith
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  have hup : ∫⁻ z, T.indicator (fun z => ‖F z‖ₑ) z ≤
      ENNReal.ofReal (Cw / (2 * A) * ∏ i, (4 * r0 i ^ 2 * π) + A / 2 * IR) := by
    calc ∫⁻ z, T.indicator (fun z => ‖F z‖ₑ) z
        ≤ ∫⁻ z, (T.indicator (fun _ => ENNReal.ofReal (Cw / (2 * A))) z +
            ENNReal.ofReal (A / 2) * ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (Cw / (2 * A)) * volume T + ENNReal.ofReal (A / 2) * I := by
          rw [lintegral_add_left (measurable_const.indicator hT), lintegral_indicator_const hT,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Cw / (2 * A) * ∏ i, (4 * r0 i ^ 2 * π) + A / 2 * IR) := by
          have hvolT : volume T = ENNReal.ofReal (∏ i, (4 * r0 i ^ 2 * π)) := by
            rw [hT_def, volume_pi_pi]
            simp_rw [Complex.volume_closedBall]
            rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [← ENNReal.ofReal_pow (by linarith [hr0 i]), ← ENNReal.ofReal_coe_nnreal,
              NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
          rw [hvolT, ← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
  -- (c) the real inequality and (d) the algebra
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hlow.trans hup)
  have hprod1 : ∏ i, r0 i = σ * ρ ^ (n + 1) := by simp [r0, Fin.prod_univ_succ]
  have hprod2 : ∏ i, r0 i ^ γ i = σ ^ γ 0 * ρ ^ xDegFin γ := by
    simp [r0, Fin.prod_univ_succ, xDegFin, Finset.prod_pow_eq_pow_sum]
  have hprod3 : ∏ i, (4 * r0 i ^ 2 * π) = (4 * π) ^ (n + 2) * (σ ^ 2 * (ρ ^ (n + 1)) ^ 2) := by
    simp [r0, Fin.prod_univ_succ]
    ring
  have hCw : Cw ≤ c₁ * α ^ 2 * β ^ 2 := by
    have hρ2 : (1 : ℝ) ≤ ρ ^ 2 := one_le_pow₀ hρ
    have hσ2 : (1 : ℝ) ≤ σ ^ 2 := one_le_pow₀ hσ
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : (1 + 4 * (n + 1) * ρ ^ 2) ^ a ≤ (5 * (n + 1 : ℝ)) ^ a * α ^ 2 := by
      have hle : 1 + 4 * (n + 1) * ρ ^ 2 ≤ 5 * (n + 1 : ℝ) * ρ ^ 2 := by nlinarith
      calc _ ≤ (5 * (n + 1 : ℝ) * ρ ^ 2) ^ a := Real.rpow_le_rpow (by positivity) hle ha
        _ = (5 * (n + 1 : ℝ)) ^ a * α ^ 2 := by
          rw [Real.mul_rpow (by positivity) (by positivity), hα_def, ← Real.rpow_natCast ρ 2,
            ← Real.rpow_mul hρ0.le, ← Real.rpow_natCast (ρ ^ a) 2, ← Real.rpow_mul hρ0.le,
            mul_comm ((2 : ℕ) : ℝ) a]
    have e2 : (1 + 4 * σ ^ 2) ^ b ≤ 5 ^ b * β ^ 2 := by
      have hle : 1 + 4 * σ ^ 2 ≤ 5 * σ ^ 2 := by nlinarith
      calc _ ≤ (5 * σ ^ 2) ^ b := Real.rpow_le_rpow (by positivity) hle hb
        _ = 5 ^ b * β ^ 2 := by
          rw [Real.mul_rpow (by positivity) (by positivity), hβ_def, ← Real.rpow_natCast σ 2,
            ← Real.rpow_mul hσ0.le, ← Real.rpow_natCast (σ ^ b) 2, ← Real.rpow_mul hσ0.le,
            mul_comm ((2 : ℕ) : ℝ) b]
    calc Cw ≤ ((5 * (n + 1 : ℝ)) ^ a * α ^ 2) * (5 ^ b * β ^ 2) :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = c₁ * α ^ 2 * β ^ 2 := by rw [hc₁]; ring
  rw [hprod1, hprod3, hX0_def, hprod2] at hreal
  have hRHS : Cw / (2 * A) * ((4 * π) ^ (n + 2) * (σ ^ 2 * (ρ ^ (n + 1)) ^ 2)) + A / 2 * IR ≤
      (c₁ * (4 * π) ^ (n + 2) + IR) / 2 * A := by
    have h1 : Cw / (2 * A) * ((4 * π) ^ (n + 2) * (σ ^ 2 * (ρ ^ (n + 1)) ^ 2)) ≤
        c₁ * α ^ 2 * β ^ 2 / (2 * A) * ((4 * π) ^ (n + 2) * (σ ^ 2 * (ρ ^ (n + 1)) ^ 2)) := by
      gcongr
    have h2 : c₁ * α ^ 2 * β ^ 2 / (2 * A) * ((4 * π) ^ (n + 2) * (σ ^ 2 * (ρ ^ (n + 1)) ^ 2)) =
        c₁ * (4 * π) ^ (n + 2) / 2 * A := by
      rw [hA_def]
      field_simp
    linarith [h1, h2]
  have hfin := hreal.trans hRHS
  have hpos : 0 < σ * ρ ^ (n + 1) * (2 * π) ^ (n + 2) := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc σ * ρ ^ (n + 1) * (2 * π) ^ (n + 2) *
        (‖taylorCoeff F γ‖ * (ρ ^ (xDegFin γ + (n + 1)) * σ ^ (γ 0 + 1)))
      = (σ * ρ ^ (n + 1)) ^ 2 *
          ((2 * π) ^ (n + 2) * ‖taylorCoeff F γ‖ * (σ ^ γ 0 * ρ ^ xDegFin γ)) := by ring
    _ ≤ (c₁ * (4 * π) ^ (n + 2) + IR) / 2 * A := hfin
    _ = σ * ρ ^ (n + 1) * (2 * π) ^ (n + 2) *
          ((c₁ * (4 * π) ^ (n + 2) + IR) / (2 * (2 * π) ^ (n + 2)) * (α * β)) := by
      rw [hA_def]
      field_simp


/-- Taylor coefficients of an entire function which is square integrable against
`(1 + |x|²)^{-a}(1 + |t|²)^{-b}` vanish in `x`-degree `> a - n - 1` and in `t`-degree `> b - 1`. -/
theorem taylorCoeff_eq_zero_of_lintegral_polyWeight {F : (Fin (n + 2) → ℂ) → ℂ}
    (hF : Differentiable ℂ F) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z) ≠ ∞) (γ : Fin (n + 2) → ℕ)
    (hγ : a - (n + 1) < xDegFin γ ∨ b - 1 < γ 0) : taylorCoeff F γ = 0 := by
  obtain ⟨K, hK⟩ := taylorCoeff_estimate hF ha hb hI γ
  rw [← norm_le_zero_iff]
  rcases hγ with h | h
  · refine nonpos_of_forall_mul_pow_le (k := xDegFin γ + (n + 1)) (a := a) (K := K)
      (by push_cast; linarith) fun ρ hρ => ?_
    simpa using hK ρ 1 hρ le_rfl
  · refine nonpos_of_forall_mul_pow_le (k := γ 0 + 1) (a := b) (K := K)
      (by push_cast; linarith) fun σ hσ => ?_
    simpa using hK 1 σ le_rfl hσ

/-- **Square integrable entire functions of polynomial growth** (`lem:c0-polynomial-growth`).
Let `F` be entire on `ℂ^{n+2} = ℂ_t × ℂ^{n+1}_x` (coordinates `t = z 0`, `x_i = z i.succ`) and
`a, b ≥ 0` with `∫ |F|² (1 + |x|²)^{-a} (1 + |t|²)^{-b} dλ < ∞`. Then `F` is a polynomial whose
monomials have `x`-degree `≤ a - n - 1` and `t`-degree `≤ b - 1`. -/
theorem exists_mvPolynomial_of_lintegral_polyWeight {F : (Fin (n + 2) → ℂ) → ℂ}
    (hF : Differentiable ℂ F) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z) < ∞) :
    ∃ P : MvPolynomial (Fin (n + 2)) ℂ, (∀ z, F z = MvPolynomial.eval z P) ∧
      ∀ m ∈ P.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ a - (n + 1) ∧
        (m 0 : ℝ) ≤ b - 1 := by
  classical
  have hz : ∀ γ, taylorCoeff F γ ≠ 0 → (xDegFin γ : ℝ) ≤ a - (n + 1) ∧ (γ 0 : ℝ) ≤ b - 1 := by
    intro γ hγ
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    exact hγ (taylorCoeff_eq_zero_of_lintegral_polyWeight hF ha hb hI.ne γ h)
  set L : ℕ := ⌈a + b⌉₊
  set s : Finset (Fin (n + 2) → ℕ) := Fintype.piFinset fun _ => Finset.range (L + 1)
  have hs : ∀ γ ∉ s, taylorCoeff F γ = 0 := by
    intro γ hγ
    by_contra h
    obtain ⟨h1, h2⟩ := hz γ h
    apply hγ
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hL : a + b ≤ L := Nat.le_ceil (a + b)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine Fin.cases ?_ (fun j => ?_) i
    · have : (γ 0 : ℝ) ≤ L := by linarith
      exact_mod_cast this
    · have hj : (γ j.succ : ℝ) ≤ xDegFin γ := by
        unfold xDegFin
        exact_mod_cast Finset.single_le_sum (f := fun i : Fin (n + 1) => γ i.succ)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have : (γ j.succ : ℝ) ≤ L := by linarith
      exact_mod_cast this
  refine ⟨∑ γ ∈ s, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm γ) (taylorCoeff F γ),
    fun z => ?_, fun m hm => ?_⟩
  · rw [← (hasSum_taylorCoeff hF z).tsum_eq, tsum_eq_sum (fun γ hγ => by rw [hs γ hγ, zero_mul]),
      map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hm
    simp only [MvPolynomial.coeff_monomial] at hm
    obtain ⟨γ, -, hγ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    split_ifs at hγ with hγm
    · subst hγm
      simpa [xDegFin] using hz γ hγ
    · exact absurd rfl hγ

end EnvelopeProperty.Char0
