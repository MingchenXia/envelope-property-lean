/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.PolynomialGrowth

/-!
# Weights of bihomogeneous families and null zero sets

This file proves `lem:c0-weight` (all five parts) and part (4) of `lem:c0-analytic-basics` of the
characteristic-zero blueprint (`EnvelopeProperty/blueprint/src/char0.tex`).

Coordinates on `ℂ^{n+2}` are `z : Fin (n + 2) → ℂ` with `t = z 0` and `x_i = z i.succ`
(see `EnvelopeProperty.Char0.PolynomialGrowth`). A family `g = (g_j)` of polynomials is encoded as
`g : ι → MvPolynomial (Fin (n + 2)) ℂ`, and `|g|² = normSqFam g = ∑_j |g_j|²`; with `φ = c log|g|`
we have `e^{-2φ} = (normSqFam g)^{-c}`.

## Main results

* `volume_mvPolynomial_zeroSet_eq_zero`: the zero set of a nonzero polynomial on `ℂⁿ` is
  Lebesgue-null
  (`lem:c0-analytic-basics` (4)); `mvPolynomial_eq_zero_of_ae_eval_eq_zero`.
* `lem:c0-weight` (2): `normSqFam_xtRot`, `|g(e^{iϑ}x, e^{iη}t)| = |g(x,t)|` for bihomogeneous
  `g_j` (`IsXTBihomogeneous`) of the same `x`-degree.
* `lem:c0-weight` (3): `exists_normSqFam_le` (`|g|² ≤ C_g (1+|x|²)^D (1+|t|²)^β`),
  `exists_degree_bounds_of_isBihomogeneous` (existence of `β`) and
  `rpow_neg_le_normSqFam_rpow_neg` (`e^{-2φ} ≥ C_g^{-c} (1+|x|²)^{-cD} (1+|t|²)^{-cβ}`);
  `one_add_sum_norm_sq_le` (`1 + |z|² ≤ (1+|x|²)(1+|t|²)`).
* `lem:c0-weight` (4): `volume_normSqFam_eq_zero`, `exists_normSqFam_le_on_compact`.
* `lem:c0-weight` (1), (5): Levi forms, see below.

## The form chosen for the Levi-form inequalities

Plurisubharmonicity is only used through the Levi forms of the smooth weights, so no theory of
plurisubharmonic functions is introduced. For `u : E → ℝ` on a complex normed space `E`,
`leviFormC0 u x v = (D²u(x)(v, v) + D²u(x)(iv, iv)) / 4` with `D²u(x)(a, b) =
iteratedFDeriv ℝ 2 u x ![a, b]`; this is TranscendentalNakamaye's `leviForm` (same normalization,
both unfold to the same term), i.e. the complex Hessian `∑ ∂²u/∂z_j∂z̄_k v_j v̄_k`. We prove:

* `leviFormC0_log_add_sum_normSq`: for `h_j` of class `C²` over `ℂ` and `ε > 0`, with
  `S = ε + ∑ |h_j|²`, `L_{log S}(x)(v) = (S ∑ |Dh_j(x)v|² - |∑ h̄_j Dh_j(x)v|²) / S²`;
* `le_leviFormC0_log_add_sum_normSq`: `L_{log S}(x)(v) ≥ ε ∑ |Dh_j(x)v|² / S²`, hence
  `leviFormC0_log_add_sum_normSq_nonneg` (`lem:c0-weight` (1));
* `le_leviFormC0_log_one_add_norm_sq`: on `EuclideanSpace ℂ (Fin N)`,
  `L_{log(1+|z|²)}(z)(v) ≥ |v|² / (1 + |z|²)²` (`lem:c0-weight` (5));
* `le_leviFormC0_weight`, `contDiff_weight`: the weights
  `Φ_ε = ∑_a c_a log (ε + ∑_j |h_{a,j}|²) + log (1 + |z|²)` are smooth with
  `L_{Φ_ε}(z)(v) ≥ |v|² / (1 + |z|²)²`, as used in `lem:c0-hormander-global`;
* `log_add_le_log_add`, `tendsto_log_add_of_pos`, `tendsto_log_add_zero`: `log (ε + S)` decreases
  to `log S` (to `-∞` on `Z(g)`) as `ε ↓ 0`.
-/

open scoped Real NNReal ENNReal Topology ComplexConjugate
open Complex MeasureTheory Set Filter

noncomputable section

namespace EnvelopeProperty.Char0

/-! ### Zero sets of polynomials are Lebesgue-null (`lem:c0-analytic-basics` (4)) -/

/-- The zero set of a nonzero polynomial on `ℂⁿ` is Lebesgue-null (`lem:c0-analytic-basics` (4)).
Induction on `n` with Fubini: for all `y` off the (null) zero set of the leading coefficient in the
first variable, the polynomial in the first variable is nonzero and has finitely many roots. -/
theorem volume_mvPolynomial_zeroSet_eq_zero : ∀ {n : ℕ} {P : MvPolynomial (Fin n) ℂ}, P ≠ 0 →
    volume {z : Fin n → ℂ | MvPolynomial.eval z P = 0} = 0
  | 0, P, hP => by
    have h0 : MvPolynomial.coeff 0 P ≠ 0 := by
      intro h
      apply hP
      rw [MvPolynomial.eq_C_of_isEmpty P, h, map_zero]
    have : {z : Fin 0 → ℂ | MvPolynomial.eval z P = 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eval_C]
      exact h0
    rw [this, measure_empty]
  | n + 1, P, hP => by
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hQ0 : Q ≠ 0 := by
      rw [hQ]
      exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ n).injective).2 hP
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hQ0
    have hnull := volume_mvPolynomial_zeroSet_eq_zero hlc
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
    set Z := {z : Fin (n + 1) → ℂ | MvPolynomial.eval z P = 0} with hZ
    have hZm : MeasurableSet Z :=
      (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
    have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm ⁻¹' Z =
        {p : ℂ × (Fin n → ℂ) |
          Polynomial.eval p.1 (Polynomial.map (MvPolynomial.eval p.2) Q) = 0} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hZ, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero', hQ]
      rw [MvPolynomial.eval_eq_eval_mv_eval']
    rw [← he.measure_preimage hZm.nullMeasurableSet, hpre, Measure.volume_eq_prod,
      Measure.prod_apply_symm]
    · have hae : (fun y : Fin n → ℂ => volume ((fun x => (x, y)) ⁻¹'
          {p : ℂ × (Fin n → ℂ) |
            Polynomial.eval p.1 (Polynomial.map (MvPolynomial.eval p.2) Q) = 0}))
          =ᵐ[volume] 0 := by
        have : ∀ᵐ y : Fin n → ℂ ∂volume, MvPolynomial.eval y Q.leadingCoeff ≠ 0 := by
          rw [ae_iff]
          simpa using hnull
        filter_upwards [this] with y hy
        have hne : Polynomial.map (MvPolynomial.eval y) Q ≠ 0 := by
          intro h
          have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (MvPolynomial.eval y) hy
          rw [h, Polynomial.leadingCoeff_zero] at this
          exact hy this.symm
        exact (Polynomial.finite_setOfPred_isRoot hne).measure_zero volume
      rw [lintegral_congr_ae hae]
      simp
    · rw [← hpre]
      exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm.measurable hZm


theorem ae_eval_mvPolynomial_ne_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ} (hP : P ≠ 0) :
    ∀ᵐ z : Fin n → ℂ, MvPolynomial.eval z P ≠ 0 := by
  rw [ae_iff]
  simpa using volume_mvPolynomial_zeroSet_eq_zero hP

/-- A polynomial vanishing almost everywhere on `ℂⁿ` is zero. -/
theorem mvPolynomial_eq_zero_of_ae_eval_eq_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (h : ∀ᵐ z : Fin n → ℂ, MvPolynomial.eval z P = 0) : P = 0 := by
  by_contra hP
  have h2 := (ae_eval_mvPolynomial_ne_zero hP).and h
  have : (∀ᵐ z : Fin n → ℂ, False) := h2.mono fun z hz => hz.1 hz.2
  rw [ae_iff] at this
  simp only [not_false_eq_true, Set.ofPred_true, Measure.measure_univ_eq_zero] at this
  exact NeZero.ne _ this

/-! ### Bihomogeneous families (`lem:c0-weight` (2), (3), (4)) -/

/-- Weighted homogeneous polynomials scale: `p(c^{w_i} z_i) = c^d p(z)`. -/
theorem eval_weightedHomogeneous_smul {σ : Type*} [Fintype σ] {w : σ → ℕ}
    {p : MvPolynomial σ ℂ} {d : ℕ} (hp : p.IsWeightedHomogeneous w d) (c : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (fun i => c ^ w i * z i) p = c ^ d * MvPolynomial.eval z p := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight w m = d := hp (MvPolynomial.mem_support_iff.1 hm)
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have : ∑ i, w i * m i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • w i)
      (fun _ => zero_smul _ _)]
    simp [mul_comm]
  rw [this]
  ring

variable {n : ℕ}

/-- The weight `(0, 1, …, 1)` on the variables `(t, x_0, …, x_n)`: its weighted degree is the
`x`-degree (`weight_xWeightFin`). -/
def xWeightFin : Fin (n + 2) → ℕ := Fin.cons 0 fun _ => 1

/-- The weight `(1, 0, …, 0)`: its weighted degree is the `t`-degree (`weight_tWeightFin`). -/
def tWeightFin : Fin (n + 2) → ℕ := Fin.cons 1 fun _ => 0

theorem weight_xWeightFin (m : Fin (n + 2) →₀ ℕ) :
    Finsupp.weight xWeightFin m = ∑ i : Fin (n + 1), m i.succ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • xWeightFin i)
    (fun _ => zero_smul _ _), Fin.sum_univ_succ]
  simp [xWeightFin]

theorem weight_tWeightFin (m : Fin (n + 2) →₀ ℕ) : Finsupp.weight tWeightFin m = m 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • tWeightFin i)
    (fun _ => zero_smul _ _), Fin.sum_univ_succ]
  simp [tWeightFin]

/-- `p ∈ ℂ[x, t]` is bihomogeneous of `x`-degree `D` and `t`-degree `l`, i.e. of the form
`s(x) t^l` with `s` homogeneous of degree `D` (`conv:c0`). -/
def IsXTBihomogeneous (D l : ℕ) (p : MvPolynomial (Fin (n + 2)) ℂ) : Prop :=
  p.IsWeightedHomogeneous xWeightFin D ∧ p.IsWeightedHomogeneous tWeightFin l

/-- The torus action `(x, t) ↦ (e^{iϑ} x, e^{iη} t)` on `ℂ^{n+2}`. -/
def xtRot (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) : Fin (n + 2) → ℂ :=
  fun i => cexp (ϑ * I) ^ xWeightFin i * (cexp (η * I) ^ tWeightFin i * z i)

@[simp] theorem xtRot_zero (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) :
    xtRot ϑ η z 0 = cexp (η * I) * z 0 := by
  simp [xtRot, xWeightFin, tWeightFin]

@[simp] theorem xtRot_succ (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) (i : Fin (n + 1)) :
    xtRot ϑ η z i.succ = cexp (ϑ * I) * z i.succ := by
  simp [xtRot, xWeightFin, tWeightFin]

theorem eval_xtRot {D l : ℕ} {p : MvPolynomial (Fin (n + 2)) ℂ} (hp : IsXTBihomogeneous D l p)
    (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) :
    MvPolynomial.eval (xtRot ϑ η z) p =
      cexp (ϑ * I) ^ D * cexp (η * I) ^ l * MvPolynomial.eval z p := by
  show MvPolynomial.eval
    (fun i => cexp (ϑ * I) ^ xWeightFin i * (cexp (η * I) ^ tWeightFin i * z i)) p = _
  rw [eval_weightedHomogeneous_smul hp.1, eval_weightedHomogeneous_smul hp.2, mul_assoc]

/-- `lem:c0-weight` (2) for one bihomogeneous polynomial. -/
theorem norm_eval_xtRot {D l : ℕ} {p : MvPolynomial (Fin (n + 2)) ℂ} (hp : IsXTBihomogeneous D l p)
    (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) :
    ‖MvPolynomial.eval (xtRot ϑ η z) p‖ = ‖MvPolynomial.eval z p‖ := by
  rw [eval_xtRot hp, norm_mul, norm_mul, norm_pow, norm_pow, norm_exp_ofReal_mul_I,
    norm_exp_ofReal_mul_I]
  simp

/-- `|g|² = ∑_j |g_j|²` for a finite family of polynomials. -/
def normSqFam {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (z : Fin (n + 2) → ℂ) : ℝ :=
  ∑ j, ‖MvPolynomial.eval z (g j)‖ ^ 2

theorem normSqFam_nonneg {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (z : Fin (n + 2) → ℂ) : 0 ≤ normSqFam g z :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_normSqFam {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ) :
    Continuous (normSqFam g) :=
  continuous_finsetSum _ fun j _ => ((MvPolynomial.continuous_eval (g j)).norm.pow 2)

/-- **`lem:c0-weight` (2)**: `|g(e^{iϑ}x, e^{iη}t)| = |g(x, t)|` for a family of bihomogeneous
polynomials of the same `x`-degree. -/
theorem normSqFam_xtRot {ι : Type*} [Fintype ι] {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {D : ℕ}
    (hg : ∀ j, ∃ l, IsXTBihomogeneous D l (g j)) (ϑ η : ℝ) (z : Fin (n + 2) → ℂ) :
    normSqFam g (xtRot ϑ η z) = normSqFam g z := by
  unfold normSqFam
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨l, hl⟩ := hg j
  rw [norm_eval_xtRot hl]

/-- `|z^m|² ≤ (1 + |x|²)^{|α|} (1 + |t|²)^{λ}` for `m = (λ, α)`. -/
theorem prod_norm_pow_sq_le (m : Fin (n + 2) → ℕ) (z : Fin (n + 2) → ℂ) :
    (∏ i, ‖z i‖ ^ m i) ^ 2 ≤ (1 + xNormSq z) ^ (∑ i : Fin (n + 1), m i.succ) *
      (1 + tNormSq z) ^ m 0 := by
  have hx : 0 ≤ 1 + xNormSq z := by linarith [xNormSq_nonneg z]
  rw [← Finset.prod_pow, Fin.prod_univ_succ, ← Finset.prod_pow_eq_pow_sum, mul_comm]
  refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun i _ => pow_nonneg hx _)
  · refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : ‖z i.succ‖ ^ 2 ≤ xNormSq z :=
      Finset.single_le_sum (f := fun j : Fin (n + 1) => ‖z j.succ‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    linarith
  · rw [← pow_mul, mul_comm, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    unfold tNormSq
    linarith

/-- A polynomial of `x`-degree `≤ D` and `t`-degree `≤ β` satisfies
`|p(z)|² ≤ C (1 + |x|²)^D (1 + |t|²)^β`. -/
theorem norm_eval_sq_le {D β : ℕ} {p : MvPolynomial (Fin (n + 2)) ℂ}
    (hp : ∀ m ∈ p.support, ∑ i : Fin (n + 1), m i.succ ≤ D ∧ m 0 ≤ β) (z : Fin (n + 2) → ℂ) :
    ‖MvPolynomial.eval z p‖ ^ 2 ≤ (∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖) ^ 2 *
      ((1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β) := by
  have hS : 0 ≤ (1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β :=
    mul_nonneg (pow_nonneg (by linarith [xNormSq_nonneg z]) _)
      (pow_nonneg (by linarith [tNormSq_nonneg z]) _)
  set S := (1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β
  have hmono : ∀ m ∈ p.support, ∏ i, ‖z i‖ ^ m i ≤ Real.sqrt S := by
    intro m hm
    rw [Real.le_sqrt (by positivity) hS]
    refine (prod_norm_pow_sq_le m z).trans ?_
    obtain ⟨h1, h2⟩ := hp m hm
    exact mul_le_mul (pow_le_pow_right₀ (by linarith [xNormSq_nonneg z]) h1)
      (pow_le_pow_right₀ (by linarith [tNormSq_nonneg z]) h2)
      (pow_nonneg (by linarith [tNormSq_nonneg z]) _)
      (pow_nonneg (by linarith [xNormSq_nonneg z]) _)
  have h1 : ‖MvPolynomial.eval z p‖ ≤
      (∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖) * Real.sqrt S := by
    rw [MvPolynomial.eval_eq', Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_mul, norm_prod]
    simp only [norm_pow]
    exact mul_le_mul_of_nonneg_left (hmono m hm) (norm_nonneg _)
  calc ‖MvPolynomial.eval z p‖ ^ 2 ≤ ((∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖) *
        Real.sqrt S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hS]

/-- **`lem:c0-weight` (3)**, first half: `|g(x,t)|² ≤ C_g (1 + |x|²)^D (1 + |t|²)^β` for a family
of polynomials of `x`-degree `≤ D` and `t`-degree `≤ β`. -/
theorem exists_normSqFam_le {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ)
    {D β : ℕ} (hg : ∀ j, ∀ m ∈ (g j).support, ∑ i : Fin (n + 1), m i.succ ≤ D ∧ m 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, normSqFam g z ≤ C * ((1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β) := by
  refine ⟨∑ j, (∑ m ∈ (g j).support, ‖MvPolynomial.coeff m (g j)‖) ^ 2 + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _) one_pos, fun z => ?_⟩
  have hS : 0 ≤ (1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β := by
    have := xNormSq_nonneg z; have := tNormSq_nonneg z; positivity
  calc normSqFam g z ≤ ∑ j, (∑ m ∈ (g j).support, ‖MvPolynomial.coeff m (g j)‖) ^ 2 *
        ((1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β) :=
        Finset.sum_le_sum fun j _ => norm_eval_sq_le (hg j) z
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hS

/-- The `t`-degrees of a finite family of polynomials are bounded. -/
theorem exists_tDeg_le {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ) :
    ∃ β : ℕ, ∀ j, ∀ m ∈ (g j).support, m 0 ≤ β := by
  classical
  refine ⟨∑ j, ∑ m ∈ (g j).support, m 0, fun j m hm => ?_⟩
  calc m 0 ≤ ∑ m ∈ (g j).support, m 0 := Finset.single_le_sum (f := fun m => m 0)
        (fun _ _ => Nat.zero_le _) hm
    _ ≤ ∑ j, ∑ m ∈ (g j).support, m 0 :=
        Finset.single_le_sum (f := fun j => ∑ m ∈ (g j).support, m 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- For a family of bihomogeneous polynomials of `x`-degree `D`, the hypothesis of
`exists_normSqFam_le` holds with some `β` (`lem:c0-weight` (3)). -/
theorem exists_degree_bounds_of_isBihomogeneous {ι : Type*} [Fintype ι]
    {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {D : ℕ} (hg : ∀ j, ∃ l, IsXTBihomogeneous D l (g j)) :
    ∃ β : ℕ, ∀ j, ∀ m ∈ (g j).support, ∑ i : Fin (n + 1), m i.succ ≤ D ∧ m 0 ≤ β := by
  obtain ⟨β, hβ⟩ := exists_tDeg_le g
  refine ⟨β, fun j m hm => ⟨?_, hβ j m hm⟩⟩
  obtain ⟨l, hl⟩ := hg j
  rw [← weight_xWeightFin, hl.1 (MvPolynomial.mem_support_iff.1 hm)]

/-- **`lem:c0-weight` (3)**, second half: with `φ = c log|g|`, i.e. `e^{-2φ} = |g|^{-2c}`,
`e^{-2φ} ≥ C_g^{-c} (1 + |x|²)^{-cD} (1 + |t|²)^{-cβ}` off `Z(g)`. -/
theorem rpow_neg_le_normSqFam_rpow_neg {ι : Type*} [Fintype ι]
    {g : ι → MvPolynomial (Fin (n + 2)) ℂ} {D β : ℕ} {C c : ℝ} (hC : 0 < C) (hc : 0 ≤ c)
    (hle : ∀ z, normSqFam g z ≤ C * ((1 + xNormSq z) ^ D * (1 + tNormSq z) ^ β))
    {z : Fin (n + 2) → ℂ} (hz : normSqFam g z ≠ 0) :
    C ^ (-c) * polyWeight (c * D) (c * β) z ≤ normSqFam g z ^ (-c) := by
  have hpos : 0 < normSqFam g z := lt_of_le_of_ne (normSqFam_nonneg g z) (Ne.symm hz)
  have hx : 0 < 1 + xNormSq z := by linarith [xNormSq_nonneg z]
  have ht : 0 < 1 + tNormSq z := by linarith [tNormSq_nonneg z]
  have h := Real.rpow_le_rpow_of_nonpos hpos (hle z) (neg_nonpos.2 hc)
  refine le_trans (le_of_eq ?_) h
  rw [Real.mul_rpow hC.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_mul ht.le,
    polyWeight]
  congr 3 <;> ring

/-- `1 + |z|² ≤ (1 + |x|²)(1 + |t|²)`. -/
theorem one_add_sum_norm_sq_le (z : Fin (n + 2) → ℂ) :
    1 + ∑ i, ‖z i‖ ^ 2 ≤ (1 + xNormSq z) * (1 + tNormSq z) := by
  rw [Fin.sum_univ_succ]
  have := xNormSq_nonneg z
  have := tNormSq_nonneg z
  unfold xNormSq tNormSq at *
  nlinarith

/-- Comparison of polynomial weights used in `prop:c0-l2-extension` (6): for `k ≥ 0`,
`(1+|x|²)^{-(a+k)} (1+|t|²)^{-(b+k)} ≤ (1+|x|²)^{-a} (1+|t|²)^{-b} (1+|z|²)^{-k}`. -/
theorem polyWeight_add_le (a b : ℝ) {k : ℝ} (hk : 0 ≤ k) (z : Fin (n + 2) → ℂ) :
    polyWeight (a + k) (b + k) z ≤ polyWeight a b z * (1 + ∑ i, ‖z i‖ ^ 2) ^ (-k) := by
  have hx : 0 < 1 + xNormSq z := by linarith [xNormSq_nonneg z]
  have ht : 0 < 1 + tNormSq z := by linarith [tNormSq_nonneg z]
  have hz : 0 < 1 + ∑ i, ‖z i‖ ^ 2 := by
    have : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have h1 : ((1 + xNormSq z) * (1 + tNormSq z)) ^ (-k) ≤ (1 + ∑ i, ‖z i‖ ^ 2) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos hz (one_add_sum_norm_sq_le z) (neg_nonpos.2 hk)
  have h2 : polyWeight (a + k) (b + k) z =
      polyWeight a b z * ((1 + xNormSq z) * (1 + tNormSq z)) ^ (-k) := by
    rw [polyWeight, polyWeight, Real.mul_rpow hx.le ht.le, neg_add, neg_add,
      Real.rpow_add hx, Real.rpow_add ht]
    ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (polyWeight_pos a b z).le

/-- **`lem:c0-weight` (4)**: `Z(g)` is Lebesgue-null as soon as some `g_j ≠ 0`. -/
theorem volume_normSqFam_eq_zero {ι : Type*} [Fintype ι] {g : ι → MvPolynomial (Fin (n + 2)) ℂ}
    {j : ι} (hj : g j ≠ 0) : volume {z | normSqFam g z = 0} = 0 := by
  refine measure_mono_null (fun z hz => ?_) (volume_mvPolynomial_zeroSet_eq_zero hj)
  simp only [Set.mem_ofPred_eq] at hz ⊢
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hz j (Finset.mem_univ j)
  simpa using this

/-- **`lem:c0-weight` (4)**: `|g|` (hence `φ = c log |g|`) is bounded above on compact sets. -/
theorem exists_normSqFam_le_on_compact {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin (n + 2)) ℂ) {K : Set (Fin (n + 2) → ℂ)} (hK : IsCompact K) :
    ∃ M, ∀ z ∈ K, normSqFam g z ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_normSqFam g).continuousOn
  exact ⟨M, fun z hz => (le_abs_self _).trans (by simpa using hM z hz)⟩


/-! ### Levi forms of `log (ε + ∑ |h_j|²)` (`lem:c0-weight` (1), (5)) -/

section Levi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

/-- The Levi form `L_u(x)(v) = (D²u(x)(v, v) + D²u(x)(iv, iv)) / 4` of a real function on a
complex normed space, with the normalization of TranscendentalNakamaye's `leviForm` (the two
definitions unfold to the same term): for `C²` functions it is the complex Hessian
`∑ ∂²u/∂z_j∂z̄_k v_j v̄_k`, and `L_{|z|²}(v) = |v|²`. -/
def leviFormC0 (u : E → ℝ) (x v : E) : ℝ :=
  (iteratedFDeriv ℝ 2 u x ![v, v] + iteratedFDeriv ℝ 2 u x ![Complex.I • v, Complex.I • v]) / 4

omit [IsScalarTower ℝ ℂ E] in
theorem leviFormC0_add {u₁ u₂ : E → ℝ} {x : E} (h₁ : ContDiffAt ℝ 2 u₁ x)
    (h₂ : ContDiffAt ℝ 2 u₂ x) (v : E) :
    leviFormC0 (fun y => u₁ y + u₂ y) x v = leviFormC0 u₁ x v + leviFormC0 u₂ x v := by
  unfold leviFormC0
  rw [show (fun y => u₁ y + u₂ y) = u₁ + u₂ from rfl, iteratedFDeriv_add_apply h₁ h₂]
  simp only [add_apply]
  ring

omit [IsScalarTower ℝ ℂ E] in
theorem leviFormC0_sum {A : Type*} [Fintype A] {u : A → E → ℝ} {x : E}
    (hu : ∀ a, ContDiffAt ℝ 2 (u a) x) (v : E) :
    leviFormC0 (fun y => ∑ a, u a y) x v = ∑ a, leviFormC0 (u a) x v := by
  unfold leviFormC0
  rw [iteratedFDeriv_fun_sum_apply (fun a _ => hu a)]
  simp only [sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

omit [IsScalarTower ℝ ℂ E] in
theorem leviFormC0_const_mul {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (c : ℝ) (v : E) :
    leviFormC0 (fun y => c * u y) x v = c * leviFormC0 u x v := by
  unfold leviFormC0
  rw [show (fun y => c * u y) = c • u from rfl, iteratedFDeriv_const_smul_apply hu]
  simp only [smul_apply, smul_eq_mul]
  ring

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- The second derivative along a real line. -/
theorem iteratedFDeriv_two_apply_eq_deriv_deriv {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x w : E) :
    iteratedFDeriv ℝ 2 u x ![w, w] = deriv (deriv fun s : ℝ => u (x + s • w)) 0 := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • w) w s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const w).const_add x
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have h1 : ∀ s, HasDerivAt (fun s : ℝ => u (x + s • w)) (fderiv ℝ u (x + s • w) w) s := fun s =>
    (hdu (x + s • w)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have h2 : deriv (fun s : ℝ => u (x + s • w)) = fun s => fderiv ℝ u (x + s • w) w :=
    funext fun s => (h1 s).deriv
  have hdf : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg : Differentiable ℝ (fun y => fderiv ℝ u y w) := fun y =>
    (hdf y).clm_apply (differentiableAt_const w)
  have hgx : fderiv ℝ (fun y => fderiv ℝ u y w) x w = fderiv ℝ (fderiv ℝ u) x w w := by
    rw [fderiv_clm_apply (hdf x) (differentiableAt_const w)]
    simp
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ u (x + s • w) w)
      (fderiv ℝ (fderiv ℝ u) x w w) 0 := by
    have := (hg (x + (0 : ℝ) • w)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
    rw [zero_smul, add_zero] at this
    rw [← hgx]
    exact this
  rw [h2, h3.deriv, iteratedFDeriv_two_apply]
  simp

/-- One-variable computation: the second derivative of `log (ε + ∑ |φ_j|²)`. -/
theorem deriv_deriv_log_add_sum_norm_sq {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    {φ φ' φ'' : ι → ℝ → ℂ} (hφ : ∀ j s, HasDerivAt (φ j) (φ' j s) s)
    (hφ' : ∀ j s, HasDerivAt (φ' j) (φ'' j s) s) :
    deriv (deriv fun s => Real.log (ε + ∑ j, ‖φ j s‖ ^ 2)) 0 =
      ((∑ j, 2 * (‖φ' j 0‖ ^ 2 + inner ℝ (φ j 0) (φ'' j 0))) * (ε + ∑ j, ‖φ j 0‖ ^ 2) -
        (∑ j, 2 * inner ℝ (φ j 0) (φ' j 0)) ^ 2) / (ε + ∑ j, ‖φ j 0‖ ^ 2) ^ 2 := by
  set S : ℝ → ℝ := fun s => ε + ∑ j, ‖φ j s‖ ^ 2 with hS_def
  set S' : ℝ → ℝ := fun s => ∑ j, 2 * inner ℝ (φ j s) (φ' j s) with hS'_def
  have hSpos : ∀ s, 0 < S s := fun s =>
    add_pos_of_pos_of_nonneg hε (Finset.sum_nonneg fun _ _ => by positivity)
  have hS : ∀ s, HasDerivAt S (S' s) s := fun s =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hφ j s).norm_sq).const_add ε
  have hS' : ∀ s, HasDerivAt S' (∑ j, 2 * (‖φ' j s‖ ^ 2 + inner ℝ (φ j s) (φ'' j s))) s :=
    fun s => by
    refine (HasDerivAt.fun_sum (u := Finset.univ)
      fun j _ => ((hφ j s).inner ℝ (hφ' j s)).const_mul 2).congr_deriv ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_self_eq_norm_sq]
    ring
  have hlog : ∀ s, HasDerivAt (fun s => Real.log (S s)) (S' s / S s) s := fun s =>
    (hS s).log (hSpos s).ne'
  have hd : deriv (fun s => Real.log (S s)) = fun s => S' s / S s :=
    funext fun s => (hlog s).deriv
  have hdiv := (hS' 0).div (hS 0) (hSpos 0).ne'
  change deriv (deriv fun s => Real.log (S s)) 0 = _
  rw [hd]
  change deriv (S' / S) 0 = _
  rw [hdiv.deriv]
  simp only [S, S']
  ring

theorem contDiff_log_add_sum_normSq {ι : Type*} [Fintype ι] {h : ι → E → ℂ} {k : WithTop ℕ∞}
    (hh : ∀ j, ContDiff ℂ k (h j)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ k (fun y => Real.log (ε + ∑ j, ‖h j y‖ ^ 2)) := by
  refine ContDiff.log ?_ fun y =>
    (add_pos_of_pos_of_nonneg hε (Finset.sum_nonneg fun _ _ => by positivity)).ne'
  exact contDiff_const.add (ContDiff.sum fun j _ =>
    (contDiff_norm_sq ℂ).comp ((hh j).restrict_scalars ℝ))

/-- **The Levi form of `log (ε + ∑ |h_j|²)`** for `C²`-holomorphic `h_j` (`lem:c0-weight` (1)):
with `S = ε + ∑ |h_j|²` and `∂h_j(v) = Dh_j(x) v`,
`L(v) = (S ∑ |∂h_j(v)|² - |∑ h̄_j ∂h_j(v)|²) / S²`. -/
theorem leviFormC0_log_add_sum_normSq {ι : Type*} [Fintype ι] {h : ι → E → ℂ}
    (hh : ∀ j, ContDiff ℂ 2 (h j)) {ε : ℝ} (hε : 0 < ε) (x v : E) :
    leviFormC0 (fun y => Real.log (ε + ∑ j, ‖h j y‖ ^ 2)) x v =
      ((ε + ∑ j, ‖h j x‖ ^ 2) * ∑ j, ‖fderiv ℂ (h j) x v‖ ^ 2 -
        ‖∑ j, conj (h j x) * fderiv ℂ (h j) x v‖ ^ 2) / (ε + ∑ j, ‖h j x‖ ^ 2) ^ 2 := by
  have hu : ContDiff ℝ 2 (fun y => Real.log (ε + ∑ j, ‖h j y‖ ^ 2)) :=
    contDiff_log_add_sum_normSq hh hε
  have hline : ∀ (w : E) (s : ℝ), HasDerivAt (fun s : ℝ => x + s • w) w s := fun w s => by
    simpa using ((hasDerivAt_id s).smul_const w).const_add x
  have hdf : ∀ j, Differentiable ℂ (fderiv ℂ (h j)) := fun j =>
    ((hh j).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : ∀ w : E, deriv (deriv fun s : ℝ => Real.log (ε + ∑ j, ‖h j (x + s • w)‖ ^ 2)) 0 =
      ((∑ j, 2 * (‖fderiv ℂ (h j) x w‖ ^ 2 +
          inner ℝ (h j x) (fderiv ℂ (fun y => fderiv ℂ (h j) y w) x w))) *
          (ε + ∑ j, ‖h j x‖ ^ 2) -
        (∑ j, 2 * inner ℝ (h j x) (fderiv ℂ (h j) x w)) ^ 2) / (ε + ∑ j, ‖h j x‖ ^ 2) ^ 2 := by
    intro w
    have hφ : ∀ j s, HasDerivAt (fun s : ℝ => h j (x + s • w))
        (fderiv ℂ (h j) (x + s • w) w) s := fun j s => by
      exact ((((hh j).differentiable (by norm_num)) (x + s • w)).hasFDerivAt.restrictScalars
        ℝ).comp_hasDerivAt s (hline w s)
    have hφ' : ∀ j s, HasDerivAt (fun s : ℝ => fderiv ℂ (h j) (x + s • w) w)
        (fderiv ℂ (fun y => fderiv ℂ (h j) y w) (x + s • w) w) s := fun j s => by
      have hd : DifferentiableAt ℂ (fun y => fderiv ℂ (h j) y w) (x + s • w) :=
        (hdf j (x + s • w)).clm_apply (differentiableAt_const w)
      exact (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s (hline w s)
    have := deriv_deriv_log_add_sum_norm_sq hε hφ hφ'
    simpa using this
  unfold leviFormC0
  rw [iteratedFDeriv_two_apply_eq_deriv_deriv hu, iteratedFDeriv_two_apply_eq_deriv_deriv hu,
    key v, key (I • v)]
  -- complex linearity of the first and second derivatives
  have ha : ∀ j, fderiv ℂ (h j) x (I • v) = I * fderiv ℂ (h j) x v := fun j => by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  have hb : ∀ j, fderiv ℂ (fun y => fderiv ℂ (h j) y (I • v)) x (I • v) =
      -fderiv ℂ (fun y => fderiv ℂ (h j) y v) x v := fun j => by
    have hfun : (fun y => fderiv ℂ (h j) y (I • v)) = fun y => I * fderiv ℂ (h j) y v := by
      funext y
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    have hd : DifferentiableAt ℂ (fun y => fderiv ℂ (h j) y v) x :=
      (hdf j x).clm_apply (differentiableAt_const v)
    rw [hfun, fderiv_const_mul hd, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.map_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, I_mul_I, neg_one_mul]
  simp_rw [ha, hb]
  set S := ε + ∑ j, ‖h j x‖ ^ 2 with hS_def
  have hSpos : 0 < S := add_pos_of_pos_of_nonneg hε (Finset.sum_nonneg fun _ _ => by positivity)
  set X : ℂ := ∑ j, fderiv ℂ (h j) x v * conj (h j x) with hX_def
  have h1 : ∑ j, 2 * inner ℝ (h j x) (fderiv ℂ (h j) x v) = 2 * X.re := by
    simp only [Complex.inner, hX_def, Complex.re_sum, Finset.mul_sum]
  have h2 : ∑ j, 2 * inner ℝ (h j x) (I * fderiv ℂ (h j) x v) = -2 * X.im := by
    simp only [Complex.inner, hX_def, Complex.im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have h3 : ∑ j, 2 * (‖I * fderiv ℂ (h j) x v‖ ^ 2 +
      inner ℝ (h j x) (-fderiv ℂ (fun y => fderiv ℂ (h j) y v) x v)) =
      ∑ j, 2 * ‖fderiv ℂ (h j) x v‖ ^ 2 -
        ∑ j, 2 * inner ℝ (h j x) (fderiv ℂ (fun y => fderiv ℂ (h j) y v) x v) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, norm_I, one_mul, inner_neg_right]
    ring
  have h4 : ∑ j, 2 * (‖fderiv ℂ (h j) x v‖ ^ 2 +
      inner ℝ (h j x) (fderiv ℂ (fun y => fderiv ℂ (h j) y v) x v)) =
      ∑ j, 2 * ‖fderiv ℂ (h j) x v‖ ^ 2 +
        ∑ j, 2 * inner ℝ (h j x) (fderiv ℂ (fun y => fderiv ℂ (h j) y v) x v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h5 : ‖∑ j, conj (h j x) * fderiv ℂ (h j) x v‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have : ∑ j, conj (h j x) * fderiv ℂ (h j) x v = X := by
      rw [hX_def]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    ring
  rw [h1, h2, h3, h4, h5, ← Finset.mul_sum]
  field_simp
  ring

/-- Cauchy–Schwarz form of the Levi bound: `L(v) ≥ ε ∑ |∂h_j(v)|² / S²`. -/
theorem le_leviFormC0_log_add_sum_normSq {ι : Type*} [Fintype ι] {h : ι → E → ℂ}
    (hh : ∀ j, ContDiff ℂ 2 (h j)) {ε : ℝ} (hε : 0 < ε) (x v : E) :
    ε * (∑ j, ‖fderiv ℂ (h j) x v‖ ^ 2) / (ε + ∑ j, ‖h j x‖ ^ 2) ^ 2 ≤
      leviFormC0 (fun y => Real.log (ε + ∑ j, ‖h j y‖ ^ 2)) x v := by
  rw [leviFormC0_log_add_sum_normSq hh hε]
  have hSpos : 0 < ε + ∑ j, ‖h j x‖ ^ 2 :=
    add_pos_of_pos_of_nonneg hε (Finset.sum_nonneg fun _ _ => by positivity)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hCS : ‖∑ j, conj (h j x) * fderiv ℂ (h j) x v‖ ^ 2 ≤
      (∑ j, ‖h j x‖ ^ 2) * ∑ j, ‖fderiv ℂ (h j) x v‖ ^ 2 := by
    calc ‖∑ j, conj (h j x) * fderiv ℂ (h j) x v‖ ^ 2
        ≤ (∑ j, ‖h j x‖ * ‖fderiv ℂ (h j) x v‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  nlinarith

/-- **`lem:c0-weight` (1)**: for holomorphic `h_j` and `ε > 0`, the smooth function
`log (ε + ∑ |h_j|²)` has nonnegative Levi form. -/
theorem leviFormC0_log_add_sum_normSq_nonneg {ι : Type*} [Fintype ι] {h : ι → E → ℂ}
    (hh : ∀ j, ContDiff ℂ 2 (h j)) {ε : ℝ} (hε : 0 < ε) (x v : E) :
    0 ≤ leviFormC0 (fun y => Real.log (ε + ∑ j, ‖h j y‖ ^ 2)) x v :=
  le_trans (by positivity) (le_leviFormC0_log_add_sum_normSq hh hε x v)

end Levi

/-- **`lem:c0-weight` (1)**, monotonicity: `log (ε + S)` decreases as `ε ↓ 0`. -/
theorem log_add_le_log_add {S ε ε' : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) (hεε' : ε ≤ ε') :
    Real.log (ε + S) ≤ Real.log (ε' + S) :=
  Real.log_le_log (by linarith) (by linarith)

/-- **`lem:c0-weight` (1)**, limit: `log (ε + S) → log S` as `ε ↓ 0` when `S > 0`. -/
theorem tendsto_log_add_of_pos {S : ℝ} (hS : 0 < S) :
    Tendsto (fun ε => Real.log (ε + S)) (𝓝[>] 0) (𝓝 (Real.log S)) := by
  have hc : ContinuousAt (fun ε => Real.log (ε + S)) 0 :=
    (Real.continuousAt_log (by simp [hS.ne'])).comp (continuous_add_const S).continuousAt
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **`lem:c0-weight` (1)**, limit: `log (ε + 0) → -∞` as `ε ↓ 0` (the value `-∞` of `log |g|`
on `Z(g)`). -/
theorem tendsto_log_add_zero : Tendsto (fun ε => Real.log (ε + 0)) (𝓝[>] 0) atBot := by
  simpa using Real.tendsto_log_nhdsGT_zero

/-- **`lem:c0-weight` (5)**: on `ℂ^N` (TranscendentalNakamaye's `ComplexModel N`), `log (1 + |z|²)`
is smooth with Levi form `≥ (1 + |z|²)^{-2} |v|²`. -/
theorem le_leviFormC0_log_one_add_norm_sq {N : ℕ} (z v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤
      leviFormC0 (fun y : EuclideanSpace ℂ (Fin N) => Real.log (1 + ‖y‖ ^ 2)) z v := by
  have hnorm : ∀ y : EuclideanSpace ℂ (Fin N), ‖y‖ ^ 2 = ∑ j, ‖EuclideanSpace.proj j y‖ ^ 2 :=
    fun y => by rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; rfl
  have hfun : (fun y : EuclideanSpace ℂ (Fin N) => Real.log (1 + ‖y‖ ^ 2)) =
      fun y => Real.log (1 + ∑ j, ‖(fun j (y : EuclideanSpace ℂ (Fin N)) =>
        EuclideanSpace.proj (𝕜 := ℂ) j y) j y‖ ^ 2) := by
    funext y; rw [hnorm]
  have hh : ∀ j : Fin N, ContDiff ℂ 2 (fun y : EuclideanSpace ℂ (Fin N) =>
      EuclideanSpace.proj (𝕜 := ℂ) j y) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin N) j).contDiff
  have := le_leviFormC0_log_add_sum_normSq hh one_pos z v
  rw [hfun]
  refine le_trans (le_of_eq ?_) this
  simp only [ContinuousLinearMap.fderiv, one_mul]
  rw [hnorm z, hnorm v]

/-- `log (1 + |z|²)` is smooth on `ℂ^N`. -/
theorem contDiff_log_one_add_norm_sq {N : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun y : EuclideanSpace ℂ (Fin N) => Real.log (1 + ‖y‖ ^ 2)) :=
  ContDiff.log (contDiff_const.add (contDiff_norm_sq ℂ)) fun y => by positivity


/-- Polynomials are holomorphic on `ℂ^N`. -/
theorem contDiff_eval_mvPolynomial {N : ℕ} (P : MvPolynomial (Fin N) ℂ) {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Fin N → ℂ => MvPolynomial.eval z P) :=
  (AnalyticOnNhd.eval_mvPolynomial P).contDiff

/-- Polynomials are holomorphic on `EuclideanSpace ℂ (Fin N)` (TranscendentalNakamaye's
`ComplexModel N`). -/
theorem contDiff_eval_mvPolynomial_euclidean {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : EuclideanSpace ℂ (Fin N) =>
      MvPolynomial.eval (EuclideanSpace.equiv (Fin N) ℂ z) P) :=
  (contDiff_eval_mvPolynomial P).comp (EuclideanSpace.equiv (Fin N) ℂ).contDiff

/-- **The Levi form bound used for Hörmander's estimate** (`lem:c0-weight` (1) + (5), as used
in `lem:c0-hormander-global`): for `ε > 0`, `c_a ≥ 0` and holomorphic `h_{a,j}`, the weight
`Φ_ε = ∑_a c_a log (ε + ∑_j |h_{a,j}|²) + log (1 + |z|²)` on `ℂ^N` satisfies
`L_{Φ_ε}(z)(v) ≥ (1 + |z|²)^{-2} |v|²`. -/
theorem le_leviFormC0_weight {N : ℕ} {A : Type*} [Fintype A] {J : A → Type*}
    [∀ a, Fintype (J a)] {c : A → ℝ} (hc : ∀ a, 0 ≤ c a)
    {h : (a : A) → J a → EuclideanSpace ℂ (Fin N) → ℂ} (hh : ∀ a j, ContDiff ℂ 2 (h a j))
    {ε : ℝ} (hε : 0 < ε) (z v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤
      leviFormC0 (fun y => ∑ a, c a * Real.log (ε + ∑ j, ‖h a j y‖ ^ 2) +
        Real.log (1 + ‖y‖ ^ 2)) z v := by
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => c a * Real.log (ε + ∑ j, ‖h a j y‖ ^ 2)) z := fun a =>
    (contDiff_const.mul (contDiff_log_add_sum_normSq (hh a) hε)).contDiffAt
  rw [leviFormC0_add (by
      have := ContDiff.sum (s := Finset.univ) fun a _ =>
        contDiff_const.mul (contDiff_log_add_sum_normSq (hh a) hε) (f := fun _ => c a)
      exact this.contDiffAt) contDiff_log_one_add_norm_sq.contDiffAt,
    leviFormC0_sum hca]
  have hnn : 0 ≤ ∑ a, leviFormC0 (fun y => c a * Real.log (ε + ∑ j, ‖h a j y‖ ^ 2)) z v := by
    refine Finset.sum_nonneg fun a _ => ?_
    rw [leviFormC0_const_mul (contDiff_log_add_sum_normSq (hh a) hε).contDiffAt]
    exact mul_nonneg (hc a) (leviFormC0_log_add_sum_normSq_nonneg (hh a) hε z v)
  linarith [le_leviFormC0_log_one_add_norm_sq z v]

/-- The weights `Φ_ε` of `le_leviFormC0_weight` are smooth. -/
theorem contDiff_weight {N : ℕ} {A : Type*} [Fintype A] {J : A → Type*}
    [∀ a, Fintype (J a)] (c : A → ℝ) {h : (a : A) → J a → EuclideanSpace ℂ (Fin N) → ℂ}
    {k : WithTop ℕ∞} (hh : ∀ a j, ContDiff ℂ k (h a j)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ k (fun y => ∑ a, c a * Real.log (ε + ∑ j, ‖h a j y‖ ^ 2) +
      Real.log (1 + ‖y‖ ^ 2)) :=
  (ContDiff.sum fun a _ => contDiff_const.mul (contDiff_log_add_sum_normSq (hh a) hε)).add
    contDiff_log_one_add_norm_sq

end EnvelopeProperty.Char0
