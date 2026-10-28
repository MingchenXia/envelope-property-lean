/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Cauchy's formula and Taylor expansion of entire functions on `ℂⁿ`

This file proves part (2) of `lem:c0-analytic-basics` of the characteristic-zero blueprint
(`EnvelopeProperty/blueprint/src/char0.tex`): an entire function `F` on `ℂⁿ` is the sum of its
Taylor series, absolutely and locally uniformly, and its Taylor coefficients are given by
Cauchy's formula on tori:
`c_γ ρ^γ = (2π)^{-n} ∫_{[0,2π]^n} F(ρ_1 e^{iθ_1}, …, ρ_n e^{iθ_n}) e^{-i⟨γ,θ⟩} dθ`.

Mathlib has the one-variable theory only. We follow the blueprint proof: iterate the one-variable
Cauchy formula on polydiscs (`torusIntegral_cauchy`, through Mathlib's `torusIntegral_succ`),
expand the Cauchy kernel `∏ (ζ_i - w_i)⁻¹` into a multiple geometric series and integrate term
by term (dominated convergence). Independence of the polyradius follows by integrating the
expansion against the characters `e^{-i⟨γ,θ⟩}` on smaller tori (orthogonality).

Points of `ℂⁿ` are functions `Fin n → ℂ` and multi-indices are functions `Fin n → ℕ`.

## Main definitions

* `EnvelopeProperty.Char0.torusPt ρ θ = (ρ_i e^{iθ_i})_i`, `torusChar γ θ = e^{-i⟨γ,θ⟩}`;
* `EnvelopeProperty.Char0.periodBox a = ∏_i (a_i, a_i + 2π]`;
* `EnvelopeProperty.Char0.taylorCoeff F γ`, the Taylor coefficients, defined by Cauchy's formula
  on the unit torus.

## Main results

* `torusIntegral_cauchy`: Cauchy's integral formula on polydiscs;
* `hasSum_taylorCoeff`, `summable_norm_taylorCoeff`, `tendstoUniformlyOn_taylorCoeff`: the Taylor
  expansion `F w = ∑_γ c_γ w^γ`, absolutely and uniformly on closed polydiscs;
* `setIntegral_periodBox_eq_taylorCoeff`, `setIntegral_Icc_eq_taylorCoeff`,
  `setIntegral_Ioo_eq_taylorCoeff`: Cauchy's formula for `c_γ ρ^γ` on every box of periods,
  in particular on `[0, 2π]^n` (the blueprint's form) and on `(-π, π)^n` (polar coordinates);
* `norm_taylorCoeff_mul_le`: Cauchy's estimates.
-/

open scoped Real NNReal ENNReal Topology
open Complex MeasureTheory Set Filter

noncomputable section

namespace EnvelopeProperty.Char0

/-! ### Products of absolutely summable series -/

/-- A finite product of absolutely summable complex series is absolutely summable, with sum the
product of the sums. -/
theorem hasSum_prod_fin {n : ℕ} {f : Fin n → ℕ → ℂ} {a : Fin n → ℂ}
    (hf : ∀ i, HasSum (f i) (a i)) (hs : ∀ i, Summable fun k => ‖f i k‖) :
    HasSum (fun γ : Fin n → ℕ => ∏ i, f i (γ i)) (∏ i, a i) ∧
      Summable (fun γ : Fin n → ℕ => ‖∏ i, f i (γ i)‖) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    refine ⟨?_, Summable.of_finite⟩
    simp
  | succ n ih =>
    have ih' := ih (f := fun i => f i.succ) (a := fun i => a i.succ)
      (fun i => hf i.succ) (fun i => hs i.succ)
    have h1 : HasSum (fun γ : Fin n → ℕ => ∏ i : Fin n, f i.succ (γ i)) (∏ i : Fin n, a i.succ) :=
      ih'.1
    have h2 : Summable (fun γ : Fin n → ℕ => ‖∏ i : Fin n, f i.succ (γ i)‖) := ih'.2
    have hp : ∀ p : ℕ × (Fin n → ℕ), ∏ i, f i ((Fin.cons p.1 p.2 : Fin (n + 1) → ℕ) i) =
        f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := fun p => by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    constructor
    · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
      have h3 : Summable fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) :=
        summable_mul_of_summable_norm (f := f 0)
          (g := fun γ : Fin n → ℕ => ∏ i : Fin n, f i.succ (γ i)) (hs 0) h2
      have := HasSum.mul (f := f 0) (g := fun γ : Fin n → ℕ => ∏ i : Fin n, f i.succ (γ i))
        (hf 0) h1 h3
      have hfun : (fun γ : Fin (n + 1) → ℕ => ∏ i, f i (γ i)) ∘ ⇑(Fin.consEquiv fun _ => ℕ) =
          fun x => f 0 x.1 * ∏ i, f i.succ (x.2 i) := by
        funext p
        exact hp p
      rw [hfun]
      exact this
    · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).summable_iff]
      have := summable_mul_of_summable_norm (f := fun k => ‖f 0 k‖)
        (g := fun γ : Fin n → ℕ => ‖∏ i : Fin n, f i.succ (γ i)‖)
        (by simpa using hs 0) (by simpa using h2)
      have hfun : (fun γ : Fin (n + 1) → ℕ => ‖∏ i, f i (γ i)‖) ∘ ⇑(Fin.consEquiv fun _ => ℕ) =
          fun x => ‖f 0 x.1‖ * ‖∏ i, f i.succ (x.2 i)‖ := by
        funext p
        rw [← norm_mul]
        exact congrArg norm (hp p)
      rw [hfun]
      exact this

/-! ### The torus and Cauchy's formula on polydiscs -/

/-- The point `(ρ_i e^{i θ_i})_i` of the torus of polyradius `ρ`. -/
def torusPt {n : ℕ} (ρ θ : Fin n → ℝ) : Fin n → ℂ := fun i => (ρ i : ℂ) * cexp (θ i * I)

theorem torusMap_zero_eq_torusPt {n : ℕ} (ρ : Fin n → ℝ) : torusMap 0 ρ = torusPt ρ := by
  funext θ i
  simp [torusMap, torusPt]

@[fun_prop]
theorem continuous_torusPt {n : ℕ} (ρ : Fin n → ℝ) : Continuous (torusPt ρ) := by
  unfold torusPt
  fun_prop

theorem norm_torusPt' {n : ℕ} (ρ θ : Fin n → ℝ) (i : Fin n) : ‖torusPt ρ θ i‖ = |ρ i| := by
  simp [torusPt, norm_exp_ofReal_mul_I]

theorem norm_torusPt {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusPt ρ θ i‖ = ρ i := by
  rw [norm_torusPt', abs_of_nonneg (hρ i)]

theorem torusPt_ne_zero {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (θ : Fin n → ℝ) (i : Fin n) :
    torusPt ρ θ i ≠ 0 := by
  intro h
  have := norm_torusPt' ρ θ i
  rw [h, norm_zero] at this
  exact (abs_pos.2 (hρ i).ne').ne this

/-- A continuous function is bounded on every torus. -/
theorem exists_bound_torus {n : ℕ} {F : (Fin n → ℂ) → ℂ} (hF : Continuous F) (ρ : Fin n → ℝ) :
    ∃ M, ∀ θ, ‖F (torusPt ρ θ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun i =>
    isCompact_sphere (0 : ℂ) |ρ i|).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨M, fun θ => hM _ ?_⟩
  intro i _
  simp [norm_torusPt']

theorem differentiable_finCons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ]
    exact differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => ℂ) j

theorem differentiable_finCons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- **Cauchy's integral formula on a polydisc**, by iterating the one-variable formula. -/
theorem torusIntegral_cauchy {n : ℕ} {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {R : Fin n → ℝ} {w : Fin n → ℂ} (hw : ∀ i, ‖w i‖ < R i) :
    (∯ ζ in T(0, R), (∏ i, (ζ i - w i))⁻¹ • F ζ) = (2 * π * I) ^ n * F w := by
  induction n with
  | zero =>
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim w 0]
  | succ n ih =>
    have hR : ∀ i, 0 ≤ R i := fun i => (norm_nonneg _).trans (hw i).le
    have hint : TorusIntegrable (fun ζ : Fin (n + 1) → ℂ => (∏ i, (ζ i - w i))⁻¹ • F ζ) 0 R := by
      have hcont : Continuous (fun θ : Fin (n + 1) → ℝ =>
          (∏ i, (torusMap 0 R θ i - w i))⁻¹ • F (torusMap 0 R θ)) := by
        rw [torusMap_zero_eq_torusPt]
        refine Continuous.smul (Continuous.inv₀ (continuous_finsetProd _ fun i _ =>
          ((continuous_apply i).comp (continuous_torusPt R)).sub continuous_const) ?_)
          (hF.continuous.comp (continuous_torusPt R))
        intro θ
        rw [Finset.prod_ne_zero_iff]
        intro i _ h
        simp only [Pi.sub_apply, Function.comp_apply, sub_eq_zero] at h
        have h1 := norm_torusPt hR θ i
        rw [h] at h1
        exact (hw i).ne h1
      exact hcont.integrableOn_Icc
    rw [torusIntegral_succ hint]
    have hinner : ∀ x : ℂ, (∯ y in T((0 : Fin (n + 1) → ℂ) ∘ Fin.succ, R ∘ Fin.succ),
        (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - w i))⁻¹ • F (Fin.cons x y)) =
        (x - w 0)⁻¹ * ((2 * π * I) ^ n * F (Fin.cons x (Fin.tail w))) := by
      intro x
      have h0 : ((0 : Fin (n + 1) → ℂ) ∘ Fin.succ) = 0 := rfl
      have hd : Differentiable ℂ (fun y : Fin n → ℂ => F (Fin.cons x y)) :=
        hF.comp (differentiable_finCons_right x)
      have := ih hd (R := R ∘ Fin.succ) (w := Fin.tail w) (fun i => hw i.succ)
      rw [h0, ← this, ← torusIntegral_const_mul]
      congr 1
      ext y
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, mul_inv, Fin.tail]
      ring
    simp_rw [hinner]
    have hdiff : DifferentiableOn ℂ (fun x : ℂ => F (Fin.cons x (Fin.tail w)))
        (Metric.closedBall 0 (R 0)) :=
      (hF.comp (differentiable_finCons_left (Fin.tail w))).differentiableOn
    have hmem : w 0 ∈ Metric.ball (0 : ℂ) (R 0) := by simpa using hw 0
    have hc := hdiff.circleIntegral_sub_inv_smul hmem
    have heq : (fun x : ℂ => (x - w 0)⁻¹ * ((2 * π * I) ^ n * F (Fin.cons x (Fin.tail w)))) =
        fun x => ((2 * π * I) ^ n) • ((x - w 0)⁻¹ • F (Fin.cons x (Fin.tail w))) := by
      ext x
      simp only [smul_eq_mul]
      ring
    simp only [Pi.zero_apply]
    rw [heq, circleIntegral.integral_smul, hc, Fin.cons_self_tail, smul_eq_mul, smul_eq_mul,
      pow_succ]
    ring


/-! ### Characters of the torus and orthogonality -/

/-- The character `θ ↦ e^{-i⟨γ,θ⟩} = ∏ i, e^{-i γ_i θ_i}` of the torus. -/
def torusChar {n : ℕ} (γ : Fin n → ℕ) (θ : Fin n → ℝ) : ℂ :=
  ∏ i, cexp (-((γ i : ℂ) * θ i * I))

theorem norm_torusChar {n : ℕ} (γ : Fin n → ℕ) (θ : Fin n → ℝ) : ‖torusChar γ θ‖ = 1 := by
  unfold torusChar
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have : -((γ i : ℂ) * θ i * I) = ((-(γ i * θ i) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_exp_ofReal_mul_I]

@[fun_prop]
theorem continuous_torusChar {n : ℕ} (γ : Fin n → ℕ) : Continuous (torusChar γ) := by
  unfold torusChar
  fun_prop

/-- The box `∏ i, (a i, a i + 2π]` of periods. -/
def periodBox {n : ℕ} (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun i => Ioc (a i) (a i + 2 * π)

theorem measurableSet_periodBox {n : ℕ} (a : Fin n → ℝ) : MeasurableSet (periodBox a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem volume_periodBox {n : ℕ} (a : Fin n → ℝ) :
    volume (periodBox a) = ENNReal.ofReal (2 * π) ^ n := by
  rw [periodBox, Real.volume_pi_Ioc]
  simp

theorem volume_periodBox_lt_top {n : ℕ} (a : Fin n → ℝ) : volume (periodBox a) < ∞ := by
  rw [volume_periodBox]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- Orthogonality of the characters `e^{ikθ}` on a period interval. -/
theorem integral_Ioc_exp_int_mul_I (a : ℝ) (k : ℤ) :
    ∫ θ in Ioc a (a + 2 * π), cexp (k * θ * I) = if k = 0 then (2 * π : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hk
  · subst hk
    simp
  · have hc : (k * I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have : (fun θ : ℝ => cexp (k * θ * I)) = fun θ : ℝ => cexp ((k * I) * θ) := by
      funext θ; ring_nf
    rw [this, integral_exp_mul_complex hc]
    have h2 : (k * I : ℂ) * ((a + 2 * π : ℝ) : ℂ) = (k * I) * a + k * (2 * π * I) := by
      push_cast; ring
    rw [h2, Complex.exp_add, exp_int_mul_two_pi_mul_I]
    simp

/-- Integral of a product function over a box of periods. -/
theorem setIntegral_periodBox_prod {n : ℕ} (a : Fin n → ℝ) (g : Fin n → ℝ → ℂ) :
    ∫ θ in periodBox a, ∏ i, g i (θ i) = ∏ i, ∫ t in Ioc (a i) (a i + 2 * π), g i t := by
  rw [periodBox, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (𝕜 := ℂ) g

theorem torusChar_mul_monomial {n : ℕ} (γ β : Fin n → ℕ) (r θ : Fin n → ℝ) :
    torusChar γ θ * ∏ i, torusPt r θ i ^ β i =
      ∏ i, ((r i : ℂ) ^ β i * cexp ((((β i : ℤ) - γ i : ℤ) : ℂ) * θ i * I)) := by
  unfold torusChar torusPt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : (-((γ i : ℂ) * θ i * I)) = -(γ i * (θ i * I)) := by ring
  rw [this]
  have h3 : ((((β i : ℤ) - γ i : ℤ) : ℂ) * θ i * I) = β i * (θ i * I) + -(γ i * (θ i * I)) := by
    push_cast; ring
  rw [h3, Complex.exp_add]
  ring

/-- Orthogonality of the torus characters against monomials. -/
theorem integral_periodBox_torusChar_mul_monomial {n : ℕ} (a : Fin n → ℝ) (γ β : Fin n → ℕ)
    (r : Fin n → ℝ) :
    ∫ θ in periodBox a, torusChar γ θ * ∏ i, torusPt r θ i ^ β i =
      if β = γ then (2 * π : ℂ) ^ n * ∏ i, (r i : ℂ) ^ γ i else 0 := by
  simp_rw [torusChar_mul_monomial]
  rw [setIntegral_periodBox_prod a
    (fun i t => (r i : ℂ) ^ β i * cexp ((((β i : ℤ) - γ i : ℤ) : ℂ) * t * I))]
  simp_rw [integral_const_mul, integral_Ioc_exp_int_mul_I]
  split_ifs with h
  · subst h
    simp only [sub_self, ↓reduceIte, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : ((β i : ℤ) - γ i) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hi
    simp [this]


/-- A finite product of geometric series with ratios in `[0, 1)` is summable. -/
theorem summable_prod_geometric {n : ℕ} {q : Fin n → ℝ} (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i < 1) :
    Summable fun γ : Fin n → ℕ => ∏ i, q i ^ γ i := by
  have hq : ∀ i, ‖((q i : ℝ) : ℂ)‖ < 1 := fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 i)]; exact h1 i
  have := (hasSum_prod_fin (f := fun i k => ((q i : ℝ) : ℂ) ^ k)
    (fun i => hasSum_geometric_of_norm_lt_one (hq i))
    (fun i => by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hq i))).2
  refine this.congr fun γ => ?_
  simp [norm_prod, norm_pow, abs_of_nonneg (h0 _)]

/-! ### Taylor expansion of entire functions -/

variable {n : ℕ}

/-- The integral `∫_{[0,2π]^n} e^{-i⟨γ,θ⟩} F(ρ e^{iθ}) dθ`. -/
def torusCoeffIntegral (F : (Fin n → ℂ) → ℂ) (ρ : Fin n → ℝ) (γ : Fin n → ℕ) : ℂ :=
  ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), torusChar γ θ * F (torusPt ρ θ)

theorem Icc_ae_eq_periodBox_zero :
    Icc (0 : Fin n → ℝ) (fun _ => 2 * π) =ᵐ[volume] periodBox 0 := by
  rw [← Set.pi_univ_Icc, periodBox, volume_pi]
  refine Measure.ae_eq_set_pi fun i _ => ?_
  simpa using (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 2 * π)).symm

theorem Ioo_ae_eq_periodBox_neg_pi :
    (Set.univ.pi fun _ : Fin n => Ioo (-π) π) =ᵐ[volume] periodBox fun _ => -π := by
  rw [periodBox, volume_pi]
  refine Measure.ae_eq_set_pi fun i _ => ?_
  have : -π + 2 * π = π := by ring
  rw [this]
  exact Ioo_ae_eq_Ioc

theorem norm_torusCoeffIntegral_le {F : (Fin n → ℂ) → ℂ} {ρ : Fin n → ℝ} {M : ℝ}
    (hM : ∀ θ, ‖F (torusPt ρ θ)‖ ≤ M) (γ : Fin n → ℕ) :
    ‖torusCoeffIntegral F ρ γ‖ ≤ (2 * π) ^ n * M := by
  unfold torusCoeffIntegral
  rw [setIntegral_congr_set Icc_ae_eq_periodBox_zero]
  have := norm_setIntegral_le_of_norm_le_const (volume_periodBox_lt_top 0)
    (f := fun θ => torusChar γ θ * F (torusPt ρ θ)) (C := M)
    (fun θ _ => by rw [norm_mul, norm_torusChar, one_mul]; exact hM θ)
  rw [Measure.real, volume_periodBox, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- Expansion on a polydisc: `(2π)^n F(w) = ∑_γ w^γ ρ^{-γ} ∫ e^{-i⟨γ,θ⟩} F(R e^{iθ}) dθ`. -/
theorem hasSum_torusCoeffIntegral {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {R : Fin n → ℝ} {w : Fin n → ℂ} (hw : ∀ i, ‖w i‖ < R i) :
    HasSum (fun γ : Fin n → ℕ =>
        (∏ i, w i ^ γ i) * ((∏ i, (R i : ℂ) ^ γ i)⁻¹ * torusCoeffIntegral F R γ))
      ((2 * π) ^ n * F w) := by
  have hR : ∀ i, 0 < R i := fun i => (norm_nonneg _).trans_lt (hw i)
  have hT := torusIntegral_cauchy hF hw
  rw [torusIntegral, torusMap_zero_eq_torusPt] at hT
  set q : (Fin n → ℝ) → Fin n → ℂ := fun θ i => w i / torusPt R θ i with hq
  have hqn : ∀ θ i, ‖q θ i‖ = ‖w i‖ / R i := fun θ i => by
    simp only [hq, norm_div, norm_torusPt (fun i => (hR i).le)]
  have hq1 : ∀ θ i, ‖q θ i‖ < 1 := fun θ i => by
    rw [hqn, div_lt_one (hR i)]; exact hw i
  have hpt : ∀ θ : Fin n → ℝ, (∏ i, (R i : ℂ) * cexp (θ i * I) * I) •
      ((∏ i, (torusPt R θ i - w i))⁻¹ • F (torusPt R θ)) =
      I ^ n * ((∏ i, (1 - q θ i)⁻¹) * F (torusPt R θ)) := by
    intro θ
    simp only [smul_eq_mul]
    have hne : ∀ i, torusPt R θ i ≠ 0 := torusPt_ne_zero hR θ
    rw [← mul_assoc, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      show I ^ n = ∏ _i : Fin n, I by simp, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    change torusPt R θ i * I * (torusPt R θ i - w i)⁻¹ = I * (1 - w i / torusPt R θ i)⁻¹
    rw [one_sub_div (hne i), inv_div]
    ring
  have hgeom : ∀ θ, HasSum (fun γ : Fin n → ℕ => ∏ i, q θ i ^ γ i) (∏ i, (1 - q θ i)⁻¹) ∧
      Summable fun γ : Fin n → ℕ => ‖∏ i, q θ i ^ γ i‖ := fun θ =>
    hasSum_prod_fin (f := fun i k => q θ i ^ k)
      (fun i => hasSum_geometric_of_norm_lt_one (hq1 θ i))
      (fun i => by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hq1 θ i))
  obtain ⟨M, hM⟩ := exists_bound_torus hF.continuous R
  set b : (Fin n → ℕ) → ℝ := fun γ => ‖∏ i, q 0 i ^ γ i‖ with hb_def
  have hb : ∀ θ γ, ‖∏ i, q θ i ^ γ i‖ = b γ := by
    intro θ γ
    simp only [hb_def, norm_prod, norm_pow, hqn]
  have hqc : ∀ i, Continuous fun θ => q θ i := fun i =>
    continuous_const.div ((continuous_apply i).comp (continuous_torusPt R))
      (fun θ => torusPt_ne_zero hR θ i)
  have hDC := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : Fin n → ℝ) fun _ => 2 * π))
    (F := fun γ θ => I ^ n * ((∏ i, q θ i ^ γ i) * F (torusPt R θ)))
    (f := fun θ => I ^ n * ((∏ i, (1 - q θ i)⁻¹) * F (torusPt R θ)))
    (fun γ _ => b γ * M)
    (fun γ => by
      refine Continuous.aestronglyMeasurable ?_
      exact continuous_const.mul ((continuous_finsetProd _ fun i _ => (hqc i).pow _).mul
        (hF.continuous.comp (continuous_torusPt R))))
    (fun γ => Filter.Eventually.of_forall fun θ => by
      rw [norm_mul, norm_pow, norm_I, one_pow, one_mul, norm_mul, hb]
      exact mul_le_mul_of_nonneg_left (hM θ) (norm_nonneg _))
    (Filter.Eventually.of_forall fun θ => ((hgeom 0).2.mul_right M))
    (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    (Filter.Eventually.of_forall fun θ => ((hgeom θ).1.mul_right _).mul_left _)
  have hRHS : ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
      I ^ n * ((∏ i, (1 - q θ i)⁻¹) * F (torusPt R θ)) = (2 * π * I) ^ n * F w := by
    rw [← hT]
    congr 1
    funext θ
    exact (hpt θ).symm
  have hqγ : ∀ θ (γ : Fin n → ℕ), ∏ i, q θ i ^ γ i =
      ((∏ i, w i ^ γ i) * (∏ i, (R i : ℂ) ^ γ i)⁻¹) * torusChar γ θ := by
    intro θ γ
    simp only [hq, torusChar, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [torusPt, div_pow, mul_pow, ← Complex.exp_nat_mul]
    have : -((γ i : ℂ) * θ i * I) = -(γ i * (θ i * I)) := by ring
    rw [this, Complex.exp_neg]
    field_simp
  have hLHS : ∀ γ : Fin n → ℕ, ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
      I ^ n * ((∏ i, q θ i ^ γ i) * F (torusPt R θ)) =
      I ^ n * ((∏ i, w i ^ γ i) * ((∏ i, (R i : ℂ) ^ γ i)⁻¹ * torusCoeffIntegral F R γ)) := by
    intro γ
    simp_rw [hqγ]
    have : ∀ θ, I ^ n * (((∏ i, w i ^ γ i) * (∏ i, (R i : ℂ) ^ γ i)⁻¹) * torusChar γ θ *
        F (torusPt R θ)) = (I ^ n * ((∏ i, w i ^ γ i) * (∏ i, (R i : ℂ) ^ γ i)⁻¹)) *
        (torusChar γ θ * F (torusPt R θ)) := fun θ => by ring
    simp_rw [this]
    rw [integral_const_mul, torusCoeffIntegral]
    ring
  simp_rw [hLHS, hRHS] at hDC
  have hI : (I ^ n : ℂ) ≠ 0 := pow_ne_zero _ I_ne_zero
  have := hDC.mul_left (I ^ n)⁻¹
  simp_rw [inv_mul_cancel_left₀ hI] at this
  rwa [show (I ^ n)⁻¹ * ((2 * π * I) ^ n * F w) = (2 * π) ^ n * F w by
    rw [mul_pow]; field_simp] at this


/-- Integration of the expansion against the characters, over any box of periods, at a radius
smaller than the radius of the expansion. -/
theorem setIntegral_periodBox_eq {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {r R : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R i) (a : Fin n → ℝ)
    (γ : Fin n → ℕ) :
    ∫ θ in periodBox a, torusChar γ θ * F (torusPt r θ) =
      (∏ i, (R i : ℂ) ^ γ i)⁻¹ * torusCoeffIntegral F R γ * ∏ i, (r i : ℂ) ^ γ i := by
  have hR : ∀ i, 0 < R i := fun i => (hr i).trans (hrR i)
  set d : (Fin n → ℕ) → ℂ := fun β => (∏ i, (R i : ℂ) ^ β i)⁻¹ * torusCoeffIntegral F R β
    with hd
  obtain ⟨M, hM⟩ := exists_bound_torus hF.continuous R
  have hdle : ∀ β, ‖d β‖ ≤ (∏ i, R i ^ β i)⁻¹ * ((2 * π) ^ n * M) := by
    intro β
    rw [hd, norm_mul, norm_inv, norm_prod]
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR _)]
    exact mul_le_mul_of_nonneg_left (norm_torusCoeffIntegral_le hM β)
      (inv_nonneg.2 (Finset.prod_nonneg fun i _ => pow_nonneg (hR i).le _))
  have hexp : ∀ θ, HasSum (fun β => torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β))
      (torusChar γ θ * ((2 * π) ^ n * F (torusPt r θ))) := fun θ =>
    (hasSum_torusCoeffIntegral hF (w := torusPt r θ)
      (fun i => by rw [norm_torusPt (fun i => (hr i).le)]; exact hrR i)).mul_left _
  set g : (Fin n → ℕ) → ℝ := fun β => ∏ i, (r i / R i) ^ β i with hg_def
  have hg : Summable g := summable_prod_geometric (fun i => (div_pos (hr i) (hR i)).le)
    (fun i => (div_lt_one (hR i)).2 (hrR i))
  have hbound : ∀ β θ, ‖torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β)‖ ≤
      g β * ((2 * π) ^ n * M) := by
    intro β θ
    rw [norm_mul, norm_torusChar, one_mul, norm_mul, norm_prod]
    simp only [norm_pow, norm_torusPt (fun i => (hr i).le)]
    calc (∏ i, r i ^ β i) * ‖d β‖
        ≤ (∏ i, r i ^ β i) * ((∏ i, R i ^ β i)⁻¹ * ((2 * π) ^ n * M)) :=
          mul_le_mul_of_nonneg_left (hdle β) (Finset.prod_nonneg fun i _ => pow_nonneg (hr i).le _)
      _ = g β * ((2 * π) ^ n * M) := by
          simp only [hg_def, div_pow, Finset.prod_div_distrib]
          ring
  have hcont : ∀ β, Continuous fun θ => torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β) :=
    fun β => (continuous_torusChar γ).mul ((continuous_finsetProd _ fun i _ =>
      ((continuous_apply i).comp (continuous_torusPt r)).pow _).mul continuous_const)
  have hDC := hasSum_integral_of_dominated_convergence (μ := volume.restrict (periodBox a))
    (F := fun β θ => torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β))
    (f := fun θ => torusChar γ θ * ((2 * π) ^ n * F (torusPt r θ)))
    (fun β _ => g β * ((2 * π) ^ n * M))
    (fun β => (hcont β).aestronglyMeasurable)
    (fun β => Filter.Eventually.of_forall fun θ => hbound β θ)
    (Filter.Eventually.of_forall fun θ => hg.mul_right _)
    (integrableOn_const (volume_periodBox_lt_top a).ne)
    (Filter.Eventually.of_forall hexp)
  have hterm : ∀ β, ∫ θ in periodBox a, torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β) =
      if β = γ then d γ * ((2 * π) ^ n * ∏ i, (r i : ℂ) ^ γ i) else 0 := by
    intro β
    have : (fun θ => torusChar γ θ * ((∏ i, torusPt r θ i ^ β i) * d β)) =
        fun θ => d β * (torusChar γ θ * ∏ i, torusPt r θ i ^ β i) := by
      funext θ; ring
    rw [this, integral_const_mul, integral_periodBox_torusChar_mul_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  simp_rw [hterm] at hDC
  have hlim := hDC.unique (hasSum_ite_eq γ _)
  have h2 : ∫ θ in periodBox a, torusChar γ θ * ((2 * π) ^ n * F (torusPt r θ)) =
      (2 * π) ^ n * ∫ θ in periodBox a, torusChar γ θ * F (torusPt r θ) := by
    rw [← integral_const_mul]
    congr 1
    funext θ
    ring
  rw [h2] at hlim
  have h2pi : ((2 * π : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  have := mul_left_cancel₀ h2pi (hlim.trans (by ring :
    d γ * ((2 * π) ^ n * ∏ i, (r i : ℂ) ^ γ i) = (2 * π) ^ n * (d γ * ∏ i, (r i : ℂ) ^ γ i)))
  rw [this]

/-- **Taylor coefficients** of `F : ℂⁿ → ℂ`, defined by Cauchy's formula on the unit torus:
`c_γ = (2π)^{-n} ∫_{[0,2π]^n} e^{-i⟨γ,θ⟩} F(e^{iθ}) dθ`. -/
def taylorCoeff (F : (Fin n → ℂ) → ℂ) (γ : Fin n → ℕ) : ℂ :=
  ((2 * π : ℂ) ^ n)⁻¹ * torusCoeffIntegral F 1 γ

/-- The normalized torus integrals of an entire function do not depend on the polyradius. -/
theorem torusCoeffIntegral_eq_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) (γ : Fin n → ℕ) :
    torusCoeffIntegral F R γ = (2 * π) ^ n * taylorCoeff F γ * ∏ i, (R i : ℂ) ^ γ i := by
  have step : ∀ {r R : Fin n → ℝ}, (∀ i, 0 < r i) → (∀ i, r i < R i) →
      torusCoeffIntegral F r γ =
        (∏ i, (R i : ℂ) ^ γ i)⁻¹ * torusCoeffIntegral F R γ * ∏ i, (r i : ℂ) ^ γ i := by
    intro r R hr hrR
    have h := setIntegral_periodBox_eq hF hr hrR 0 γ
    rw [← setIntegral_congr_set Icc_ae_eq_periodBox_zero] at h
    exact h
  set R' : Fin n → ℝ := fun i => max (R i) 1 + 1
  have hRR' : ∀ i, R i < R' i := fun i => by
    simp only [R']; linarith [le_max_left (R i) 1]
  have h1R' : ∀ i, (1 : Fin n → ℝ) i < R' i := fun i => by
    simp only [R', Pi.one_apply]; linarith [le_max_right (R i) 1]
  rw [step hR hRR']
  have h2 := step (r := 1) (fun _ => one_pos) h1R'
  simp only [Pi.one_apply, Complex.ofReal_one, one_pow, Finset.prod_const_one, mul_one] at h2
  rw [taylorCoeff, h2]
  have h2pi : ((2 * π : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  field_simp

/-- **Cauchy's formula for Taylor coefficients** (`lem:c0-analytic-basics` (2)), over any box of
periods: `∫_{box} e^{-i⟨γ,θ⟩} F(ρ e^{iθ}) dθ = (2π)^n c_γ ρ^γ`. -/
theorem setIntegral_periodBox_eq_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (a : Fin n → ℝ) (γ : Fin n → ℕ) :
    ∫ θ in periodBox a, torusChar γ θ * F (torusPt ρ θ) =
      (2 * π) ^ n * taylorCoeff F γ * ∏ i, (ρ i : ℂ) ^ γ i := by
  have hρR : ∀ i, ρ i < ρ i + 1 := fun i => by linarith
  rw [setIntegral_periodBox_eq hF hρ (R := fun i => ρ i + 1) hρR a γ,
    torusCoeffIntegral_eq_taylorCoeff hF (fun i => by linarith [hρ i])]
  have : (∏ i, (((ρ i + 1 : ℝ)) : ℂ) ^ γ i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (by exact_mod_cast (by linarith [hρ i]))
  field_simp

/-- Cauchy's formula on `[0, 2π]^n`: `(2π)^n c_γ ρ^γ = ∫_{[0,2π]^n} e^{-i⟨γ,θ⟩} F(ρ e^{iθ}) dθ`. -/
theorem setIntegral_Icc_eq_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (γ : Fin n → ℕ) :
    ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), torusChar γ θ * F (torusPt ρ θ) =
      (2 * π) ^ n * taylorCoeff F γ * ∏ i, (ρ i : ℂ) ^ γ i :=
  torusCoeffIntegral_eq_taylorCoeff hF hρ γ

/-- Cauchy's formula on `(-π, π)^n`, the angular range of polar coordinates. -/
theorem setIntegral_Ioo_eq_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (γ : Fin n → ℕ) :
    ∫ θ in Set.univ.pi (fun _ : Fin n => Ioo (-π) π), torusChar γ θ * F (torusPt ρ θ) =
      (2 * π) ^ n * taylorCoeff F γ * ∏ i, (ρ i : ℂ) ^ γ i := by
  rw [setIntegral_congr_set Ioo_ae_eq_periodBox_neg_pi]
  exact setIntegral_periodBox_eq_taylorCoeff hF hρ _ γ

/-- **Cauchy's estimates**: `|c_γ| ρ^γ ≤ sup_{torus ρ} |F|`. -/
theorem norm_taylorCoeff_mul_le {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {M : ℝ} (hM : ∀ θ, ‖F (torusPt ρ θ)‖ ≤ M)
    (γ : Fin n → ℕ) : ‖taylorCoeff F γ‖ * ∏ i, ρ i ^ γ i ≤ M := by
  have h := norm_torusCoeffIntegral_le hM γ
  rw [torusCoeffIntegral_eq_taylorCoeff hF hρ γ, norm_mul, norm_mul, norm_prod] at h
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ _),
    abs_of_pos Real.pi_pos, Complex.norm_ofNat, norm_mul] at h
  have h2pi : 0 < (2 * π) ^ n := by positivity
  nlinarith [h]

/-- **Taylor expansion** of an entire function on `ℂⁿ` (`lem:c0-analytic-basics` (2)):
`F(w) = ∑_γ c_γ w^γ`. -/
theorem hasSum_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F) (w : Fin n → ℂ) :
    HasSum (fun γ : Fin n → ℕ => taylorCoeff F γ * ∏ i, w i ^ γ i) (F w) := by
  set R : Fin n → ℝ := fun i => ‖w i‖ + 1
  have hw : ∀ i, ‖w i‖ < R i := fun i => by simp [R]
  have hR : ∀ i, 0 < R i := fun i => by positivity
  have h := hasSum_torusCoeffIntegral hF hw
  have hR0 : ∀ γ : Fin n → ℕ, (∏ i, (R i : ℂ) ^ γ i) ≠ 0 := fun γ =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (by exact_mod_cast (hR i).ne')
  have h2pi : ((2 * π : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  have hc : ∀ γ : Fin n → ℕ, (∏ i, w i ^ γ i) * ((∏ i, (R i : ℂ) ^ γ i)⁻¹ *
      torusCoeffIntegral F R γ) = (2 * π) ^ n * (taylorCoeff F γ * ∏ i, w i ^ γ i) := by
    intro γ
    rw [torusCoeffIntegral_eq_taylorCoeff hF hR γ]
    have := hR0 γ
    field_simp
  simp_rw [hc] at h
  have := h.mul_left ((2 * π : ℂ) ^ n)⁻¹
  simp_rw [inv_mul_cancel_left₀ h2pi] at this
  exact this

/-- The Taylor series of an entire function converges absolutely, with the explicit bound
`|c_γ w^γ| ≤ M ∏ (|w_i| / R_i)^{γ_i}` for `|w_i| < R_i` and `M ≥ sup_{torus R} |F|`. -/
theorem norm_taylorCoeff_mul_monomial_le {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) {M : ℝ} (hM : ∀ θ, ‖F (torusPt R θ)‖ ≤ M)
    (w : Fin n → ℂ) (γ : Fin n → ℕ) :
    ‖taylorCoeff F γ * ∏ i, w i ^ γ i‖ ≤ M * ∏ i, (‖w i‖ / R i) ^ γ i := by
  have h := norm_taylorCoeff_mul_le hF hR hM γ
  have hpos : 0 < ∏ i, R i ^ γ i := Finset.prod_pos fun i _ => pow_pos (hR i) _
  rw [norm_mul, norm_prod]
  simp only [norm_pow, div_pow, Finset.prod_div_distrib]
  rw [← le_div_iff₀ hpos] at h
  calc ‖taylorCoeff F γ‖ * ∏ i, ‖w i‖ ^ γ i ≤ M / (∏ i, R i ^ γ i) * ∏ i, ‖w i‖ ^ γ i :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = M * ((∏ i, ‖w i‖ ^ γ i) / ∏ i, R i ^ γ i) := by ring

theorem summable_norm_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (w : Fin n → ℂ) : Summable fun γ : Fin n → ℕ => ‖taylorCoeff F γ * ∏ i, w i ^ γ i‖ := by
  set R : Fin n → ℝ := fun i => ‖w i‖ + 1
  have hR : ∀ i, 0 < R i := fun i => by positivity
  obtain ⟨M, hM⟩ := exists_bound_torus hF.continuous R
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_taylorCoeff_mul_monomial_le hF hR hM w)
    ((summable_prod_geometric (fun i => by positivity) (fun i => ?_)).mul_left M)
  rw [div_lt_one (hR i)]
  simp [R]


/-- The Taylor series of an entire function converges uniformly on every closed polydisc, hence
locally uniformly on `ℂⁿ`. -/
theorem tendstoUniformlyOn_taylorCoeff {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (r : Fin n → ℝ) :
    TendstoUniformlyOn (fun (s : Finset (Fin n → ℕ)) (w : Fin n → ℂ) =>
        ∑ γ ∈ s, taylorCoeff F γ * ∏ i, w i ^ γ i) F atTop {w | ∀ i, ‖w i‖ ≤ r i} := by
  set R : Fin n → ℝ := fun i => |r i| + 1
  have hR : ∀ i, 0 < R i := fun i => by positivity
  obtain ⟨M, hM⟩ := exists_bound_torus hF.continuous R
  have hq : ∀ i, |r i| / R i < 1 := fun i => by rw [div_lt_one (hR i)]; simp [R]
  have h := tendstoUniformlyOn_tsum (f := fun γ (w : Fin n → ℂ) => taylorCoeff F γ * ∏ i, w i ^ γ i)
    ((summable_prod_geometric (fun i => by positivity) hq).mul_left M)
    (s := {w | ∀ i, ‖w i‖ ≤ r i}) (fun γ w hw => by
      refine (norm_taylorCoeff_mul_monomial_le hF hR hM w γ).trans ?_
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => by positivity)
        fun i _ => pow_le_pow_left₀ (by positivity) ?_ _) ?_
      · exact div_le_div_of_nonneg_right ((hw i).trans (le_abs_self _)) (hR i).le
      · exact (norm_nonneg _).trans (hM 0))
  have hF' : (fun w => ∑' γ, taylorCoeff F γ * ∏ i, w i ^ γ i) = F :=
    funext fun w => (hasSum_taylorCoeff hF w).tsum_eq
  rwa [hF'] at h

end EnvelopeProperty.Char0
