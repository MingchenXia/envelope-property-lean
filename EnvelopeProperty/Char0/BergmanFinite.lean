/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.Weights

/-!
# Polynomials dominating a fractional power: the finite-dimensional part

This file proves the finite-dimensional part of `cor:c0-bergman-lower` of the characteristic-zero
blueprint (`blueprint/src/char0.tex`). The analytic input, the extension property of
`prop:c0-l2-extension` (`L²` extension from a point with polynomial growth, proved in
`EnvelopeProperty.Char0.L2Extension`), is a hypothesis of `exists_homogeneous_lower_bound`.

Let `ω ≥ 0` be a measurable weight on `ℂ^{n+2}` (coordinates `t = z 0`, `x_i = z i.succ`), positive
almost everywhere, such that `ω λ` is invariant under `x ↦ e^{iϑ}x` (`hrot`, where
`xtRot ϑ 0 z = (e^{iϑ}x, t)`). For `A, B ∈ ℝ` let `W = bergmanSpace ω A B` be the space of
polynomials of `x`-degree `≤ A` and `t`-degree `≤ B` with `‖F‖²_ω = ∫ |F|² ω dλ < ∞`
(`wNormSq ω F`). We prove, following the blueprint:

* `W` is finite dimensional (`bergmanSpace_le_restrictTotalDegree`);
* the `x`-homogeneous components `F_e` of `F ∈ W` lie in `W`, with `∑_e ‖F_e‖²_ω = ‖F‖²_ω`
  (`sum_wNormSq_weightedHomogeneousComponent`, from Parseval's identity
  `integral_norm_sq_sum_exp` in `ϑ` and the invariance of `ω λ`), hence `‖F_e‖_ω ≤ ‖F‖_ω`
  (`wNormSq_weightedHomogeneousComponent_le`, `weightedHomogeneousComponent_mem_bergmanSpace`);
  the blueprint uses Minkowski's inequality instead of Parseval;
* `W` has a basis of `x`-homogeneous polynomials (`exists_homogeneous_basis`);
* norms on `W` are equivalent: `∑ |a_k| ≤ C_W ‖∑ a_k P_k‖_ω` (`exists_sum_norm_le`), using
  `L²(ω λ)` and the nullity of zero sets of polynomials (`volume_mvPolynomial_zeroSet_eq_zero`);
* given the extension property, `|P(y)| ≥ c_K |g(y)|^c` on every compact `K`
  (`exists_homogeneous_lower_bound`).

`x`-homogeneous components are Mathlib's `MvPolynomial.weightedHomogeneousComponent` for the
weight `xWeightFin = (0, 1, …, 1)`.
-/

open scoped Real NNReal ENNReal Topology ComplexConjugate
open Complex MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty.Char0

variable {n : ℕ}

/-! ### The rotation `x ↦ e^{iϑ} x` -/

theorem xtRot_zero_right_eq (ϑ : ℝ) (z : Fin (n + 2) → ℂ) :
    xtRot ϑ 0 z = fun i => cexp (ϑ * I) ^ xWeightFin i * z i := by
  funext i
  simp [xtRot]

theorem continuous_xtRot_uncurry :
    Continuous fun q : ℝ × (Fin (n + 2) → ℂ) => xtRot q.1 0 q.2 := by
  unfold xtRot
  fun_prop

/-- The rotation `x ↦ e^{iϑ} x` preserves Lebesgue measure. -/
theorem measurePreserving_xtRot (ϑ : ℝ) :
    MeasurePreserving (xtRot ϑ 0 : (Fin (n + 2) → ℂ) → Fin (n + 2) → ℂ) volume volume := by
  have h : (xtRot ϑ 0 : (Fin (n + 2) → ℂ) → Fin (n + 2) → ℂ) =
      fun z i => rotation (Circle.exp (xWeightFin i * ϑ)) (z i) := by
    funext z i
    rw [xtRot_zero_right_eq]
    dsimp only
    rw [rotation_apply, Circle.coe_exp, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [h]
  exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
    fun i => (rotation (Circle.exp (xWeightFin i * ϑ))).measurePreserving

/-! ### Parseval's identity for trigonometric polynomials -/

theorem norm_sq_sum_exp (s : Finset ℕ) (a : ℕ → ℂ) (ϑ : ℝ) :
    ‖∑ e ∈ s, cexp (ϑ * I) ^ e * a e‖ ^ 2 =
      (∑ e ∈ s, ∑ e' ∈ s, cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e'))).re := by
  rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
    Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [map_mul, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : cexp (((e : ℤ) - e' : ℤ) * ϑ * I) =
      cexp (e * (ϑ * I)) * cexp (e' * conj (ϑ * I)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [this]
  ring

/-- **Parseval's identity**: `∫_0^{2π} |∑_e a_e e^{ieϑ}|² dϑ = 2π ∑_e |a_e|²`. -/
theorem integral_norm_sq_sum_exp (s : Finset ℕ) (a : ℕ → ℂ) :
    ∫ ϑ in Ioc 0 (2 * π), ‖∑ e ∈ s, cexp (ϑ * I) ^ e * a e‖ ^ 2 =
      2 * π * ∑ e ∈ s, ‖a e‖ ^ 2 := by
  simp_rw [norm_sq_sum_exp]
  have hint : ∀ e e' : ℕ, Integrable (fun ϑ : ℝ =>
      cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e')))
      (volume.restrict (Ioc 0 (2 * π))) := fun e e' =>
    (by fun_prop : Continuous fun ϑ : ℝ =>
      cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e'))).integrableOn_Ioc
  have h1 : (fun ϑ : ℝ => (∑ e ∈ s, ∑ e' ∈ s,
      cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e'))).re) =
      fun ϑ : ℝ => RCLike.re (∑ e ∈ s, ∑ e' ∈ s,
        cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e'))) := rfl
  rw [h1, integral_re (integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ =>
    hint e e')]
  rw [integral_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => hint e e']
  have h2 : ∀ e e' : ℕ, ∫ ϑ in Ioc 0 (2 * π),
      cexp ((((e : ℤ) - e' : ℤ) : ℂ) * ϑ * I) * (a e * conj (a e')) =
      if e' = e then 2 * π * (a e * conj (a e)) else 0 := by
    intro e e'
    rw [integral_mul_const]
    have := integral_Ioc_exp_int_mul_I 0 ((e : ℤ) - e')
    rw [zero_add] at this
    rw [this]
    by_cases h : e' = e
    · subst h; simp
    · have : (e : ℤ) - e' ≠ 0 := by
        rw [sub_ne_zero]
        intro h'
        exact h (by exact_mod_cast h'.symm)
      simp [this, h]
  rw [Finset.sum_congr rfl fun e _ => integral_finsetSum s fun e' _ => hint e e']
  simp_rw [h2, Finset.sum_ite_eq']
  rw [RCLike.re_to_complex, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [if_pos he, Complex.mul_conj, Complex.sq_norm]
  norm_cast


/-! ### `x`-homogeneous components -/

/-- A polynomial of `x`-degree `≤ L` is the sum of its `x`-homogeneous components of degree
`≤ L`. -/
theorem sum_weightedHomogeneousComponent_range {L : ℕ} {F : MvPolynomial (Fin (n + 2)) ℂ}
    (hF : ∀ m ∈ F.support, Finsupp.weight xWeightFin m ≤ L) :
    ∑ e ∈ Finset.range (L + 1), weightedHomogeneousComponent xWeightFin e F = F := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    by_contra hne
    have := hF d (mem_support_iff.2 (Ne.symm hne))
    omega

/-- The `x`-homogeneous expansion `F(e^{iϑ}x, t) = ∑_e e^{ieϑ} F_e(x, t)`. -/
theorem eval_xtRot_eq_sum {L : ℕ} {F : MvPolynomial (Fin (n + 2)) ℂ}
    (hF : ∀ m ∈ F.support, Finsupp.weight xWeightFin m ≤ L) (ϑ : ℝ) (z : Fin (n + 2) → ℂ) :
    eval (xtRot ϑ 0 z) F = ∑ e ∈ Finset.range (L + 1),
      cexp (ϑ * I) ^ e * eval z (weightedHomogeneousComponent xWeightFin e F) := by
  conv_lhs => rw [← sum_weightedHomogeneousComponent_range hF]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [xtRot_zero_right_eq, eval_weightedHomogeneous_smul
    (weightedHomogeneousComponent_isWeightedHomogeneous e F)]

/-- The weighted `L²` norm `‖F‖²_ω = ∫ |F|² ω dλ` of a polynomial (`cor:c0-bergman-lower`). -/
def wNormSq (ω : (Fin (n + 2) → ℂ) → ℝ≥0∞) (F : MvPolynomial (Fin (n + 2)) ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ω z * ‖eval z F‖ₑ ^ 2

theorem measurable_enorm_eval_sq (F : MvPolynomial (Fin (n + 2)) ℂ) :
    Measurable fun z : Fin (n + 2) → ℂ => ‖eval z F‖ₑ ^ 2 :=
  ((continuous_eval F).measurable.enorm).pow_const 2

/-- **Pythagoras for the `x`-homogeneous decomposition**: if the measure `ω λ` is invariant
under `x ↦ e^{iϑ}x`, then `∑_e ‖F_e‖²_ω = ‖F‖²_ω`. Proof: Parseval in `ϑ` pointwise, then
Tonelli and the invariance of `ω λ`. -/
theorem sum_wNormSq_weightedHomogeneousComponent {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞}
    (hω : Measurable ω) (hrot : ∀ ϑ z, ω (xtRot ϑ 0 z) = ω z) {L : ℕ}
    {F : MvPolynomial (Fin (n + 2)) ℂ} (hF : ∀ m ∈ F.support, Finsupp.weight xWeightFin m ≤ L) :
    ∑ e ∈ Finset.range (L + 1), wNormSq ω (weightedHomogeneousComponent xWeightFin e F) =
      wNormSq ω F := by
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π) with hc
  have hc0 : c ≠ 0 := by rw [hc]; simp [Real.pi_pos]
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcont : Continuous fun q : ℝ × (Fin (n + 2) → ℂ) => eval (xtRot q.1 0 q.2) F :=
    (continuous_eval F).comp continuous_xtRot_uncurry
  -- Parseval, pointwise in `z`
  have hpz : ∀ z, ∫⁻ ϑ in Ioc 0 (2 * π), ‖eval (xtRot ϑ 0 z) F‖ₑ ^ 2 =
      c * ∑ e ∈ Finset.range (L + 1),
        ‖eval z (weightedHomogeneousComponent xWeightFin e F)‖ₑ ^ 2 := by
    intro z
    have hint : IntegrableOn (fun ϑ : ℝ => ‖eval (xtRot ϑ 0 z) F‖ ^ 2) (Ioc 0 (2 * π)) :=
      ((hcont.comp (Continuous.prodMk_left z)).norm.pow 2).integrableOn_Ioc
    simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
    simp_rw [eval_xtRot_eq_sum hF]
    rw [integral_norm_sq_sum_exp, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  -- invariance
  have hinv : ∀ ϑ : ℝ, ∫⁻ z, ω z * ‖eval (xtRot ϑ 0 z) F‖ₑ ^ 2 = wNormSq ω F := by
    intro ϑ
    have := (measurePreserving_xtRot (n := n) ϑ).lintegral_comp
      (f := fun z => ω z * ‖eval z F‖ₑ ^ 2) (hω.mul (measurable_enorm_eval_sq F))
    simp only [hrot] at this
    exact this
  -- Tonelli
  have hmeas : AEMeasurable (Function.uncurry fun (ϑ : ℝ) (z : Fin (n + 2) → ℂ) =>
      ω z * ‖eval (xtRot ϑ 0 z) F‖ₑ ^ 2) ((volume.restrict (Ioc 0 (2 * π))).prod volume) :=
    ((hω.comp measurable_snd).mul ((hcont.measurable.enorm).pow_const 2)).aemeasurable
  have hswap := lintegral_lintegral_swap hmeas
  simp only [hinv, setLIntegral_const, Real.volume_Ioc, sub_zero] at hswap
  have key : c * ∑ e ∈ Finset.range (L + 1),
      wNormSq ω (weightedHomogeneousComponent xWeightFin e F) =
      c * wNormSq ω F := by
    rw [mul_comm c (wNormSq ω F), hswap, Finset.mul_sum]
    have hR : ∀ y, ∫⁻ x in Ioc 0 (2 * π), ω y * ‖eval (xtRot x 0 y) F‖ₑ ^ 2 =
        ω y * (c * ∑ e ∈ Finset.range (L + 1),
          ‖eval y (weightedHomogeneousComponent xWeightFin e F)‖ₑ ^ 2) := fun y => by
      rw [lintegral_const_mul (ω y) (f := fun x => ‖eval (xtRot x 0 y) F‖ₑ ^ 2)
        ((hcont.comp (Continuous.prodMk_left y)).measurable.enorm.pow_const 2), hpz]
    simp_rw [hR]
    unfold wNormSq
    simp_rw [← lintegral_const_mul' _ _ hctop]
    rw [← lintegral_finsetSum' (Finset.range (L + 1))
      (f := fun e z => c * (ω z * ‖eval z (weightedHomogeneousComponent xWeightFin e F)‖ₑ ^ 2))
      fun e _ => ((hω.mul (measurable_enorm_eval_sq _)).const_mul c).aemeasurable]
    congr 1
    funext z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  exact (ENNReal.mul_right_inj hc0 hctop).1 key


/-- `‖F_e‖_ω ≤ ‖F‖_ω` for the `x`-homogeneous components (`cor:c0-bergman-lower`). -/
theorem wNormSq_weightedHomogeneousComponent_le {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞}
    (hω : Measurable ω) (hrot : ∀ ϑ z, ω (xtRot ϑ 0 z) = ω z)
    (F : MvPolynomial (Fin (n + 2)) ℂ) (e : ℕ) :
    wNormSq ω (weightedHomogeneousComponent xWeightFin e F) ≤ wNormSq ω F := by
  set L := weightedTotalDegree xWeightFin F
  have hF : ∀ m ∈ F.support, Finsupp.weight xWeightFin m ≤ L := fun m hm =>
    le_weightedTotalDegree xWeightFin hm
  by_cases he : e ≤ L
  · rw [← sum_wNormSq_weightedHomogeneousComponent hω hrot hF]
    exact Finset.single_le_sum
      (f := fun e => wNormSq ω (weightedHomogeneousComponent xWeightFin e F))
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le he))
  · rw [weightedHomogeneousComponent_eq_zero' e F fun d hd h => he (h ▸ hF d hd)]
    simp [wNormSq]

/-! ### The space `W` -/

theorem lintegral_withDensity_enorm_eval_sq {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    (F : MvPolynomial (Fin (n + 2)) ℂ) :
    ∫⁻ z, ‖eval z F‖ₑ ^ 2 ∂(volume.withDensity ω) = wNormSq ω F := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hω (measurable_enorm_eval_sq F)]
  rfl

/-- `‖F‖_ω` is the `L²(ω λ)` norm. -/
theorem eLpNorm_eval_eq {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    (F : MvPolynomial (Fin (n + 2)) ℂ) :
    eLpNorm (fun z => eval z F) 2 (volume.withDensity ω) = wNormSq ω F ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_withDensity_enorm_eval_sq hω]

theorem memLp_eval_iff {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    (F : MvPolynomial (Fin (n + 2)) ℂ) :
    MemLp (fun z => eval z F) 2 (volume.withDensity ω) ↔ wNormSq ω F < ⊤ := by
  rw [MemLp, eLpNorm_eval_eq hω]
  simp only [(continuous_eval F).aestronglyMeasurable, true_and]
  constructor
  · intro h
    by_contra h'
    rw [not_lt, top_le_iff] at h'
    rw [h', ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/-- The space `W` of `cor:c0-bergman-lower`: polynomials of `x`-degree `≤ A` and `t`-degree `≤ B`
with `‖F‖²_ω = ∫ |F|² ω dλ < ∞` (encoded as `F ∈ L²(ω λ)`, see `mem_bergmanSpace_iff`). -/
def bergmanSpace (ω : (Fin (n + 2) → ℂ) → ℝ≥0∞) (A B : ℝ) :
    Submodule ℂ (MvPolynomial (Fin (n + 2)) ℂ) where
  carrier := {F | (∀ m ∈ F.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ A ∧
    (m 0 : ℝ) ≤ B) ∧ MemLp (fun z => eval z F) 2 (volume.withDensity ω)}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    classical
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    refine ⟨fun m hm => ?_, ?_⟩
    swap
    · have h : (fun z => eval z (F + G)) = (fun z => eval z F) + fun z => eval z G := by
        funext z; simp
      rw [h]
      exact hF2.add hG2
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hF1 m h
    · exact hG1 m h
  smul_mem' := by
    rintro c F ⟨hF1, hF2⟩
    refine ⟨fun m hm => hF1 m (support_smul hm), ?_⟩
    have h : (fun z => eval z (c • F)) = c • fun z => eval z F := by
      funext z; simp [smul_eval]
    rw [h]
    exact hF2.const_smul c

theorem mem_bergmanSpace_iff {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω) {A B : ℝ}
    {F : MvPolynomial (Fin (n + 2)) ℂ} :
    F ∈ bergmanSpace ω A B ↔ (∀ m ∈ F.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ A ∧
      (m 0 : ℝ) ≤ B) ∧ wNormSq ω F < ⊤ := by
  change (_ ∧ _) ↔ _
  rw [memLp_eval_iff hω]

/-- **The `x`-homogeneous components of elements of `W` lie in `W`** (`cor:c0-bergman-lower`),
with `‖F_e‖_ω ≤ ‖F‖_ω` (`wNormSq_weightedHomogeneousComponent_le`). -/
theorem weightedHomogeneousComponent_mem_bergmanSpace {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞}
    (hω : Measurable ω) (hrot : ∀ ϑ z, ω (xtRot ϑ 0 z) = ω z) {A B : ℝ}
    {F : MvPolynomial (Fin (n + 2)) ℂ} (hF : F ∈ bergmanSpace ω A B) (e : ℕ) :
    weightedHomogeneousComponent xWeightFin e F ∈ bergmanSpace ω A B := by
  classical
  rw [mem_bergmanSpace_iff hω] at hF ⊢
  refine ⟨fun m hm => hF.1 m ?_, (wNormSq_weightedHomogeneousComponent_le hω hrot F e).trans_lt
    hF.2⟩
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  rw [mem_support_iff]
  intro h
  rw [h, ite_self] at hm
  exact hm rfl


theorem bergmanSpace_le_restrictTotalDegree (ω : (Fin (n + 2) → ℂ) → ℝ≥0∞) (A B : ℝ) :
    bergmanSpace ω A B ≤ restrictTotalDegree (Fin (n + 2)) ℂ (⌊A⌋₊ + ⌊B⌋₊) := by
  intro F hF
  rw [mem_restrictTotalDegree, totalDegree]
  refine Finset.sup_le fun m hm => ?_
  obtain ⟨h1, h2⟩ := hF.1 m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, add_comm]
  exact add_le_add (Nat.le_floor h1) (Nat.le_floor h2)

instance (ω : (Fin (n + 2) → ℂ) → ℝ≥0∞) (A B : ℝ) :
    FiniteDimensional ℂ (bergmanSpace ω A B) :=
  Submodule.finiteDimensional_of_le (bergmanSpace_le_restrictTotalDegree ω A B)

/-- **`W` has a basis of `x`-homogeneous polynomials** (`cor:c0-bergman-lower`): a finite,
linearly independent family of `x`-homogeneous elements of `W` spanning `W`. -/
theorem exists_homogeneous_basis {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    (hrot : ∀ ϑ z, ω (xtRot ϑ 0 z) = ω z) (A B : ℝ) :
    ∃ s : Finset (MvPolynomial (Fin (n + 2)) ℂ),
      (∀ P ∈ s, P ∈ bergmanSpace ω A B ∧ ∃ e : ℕ, P.IsWeightedHomogeneous xWeightFin e) ∧
      LinearIndependent ℂ (fun P : s => (P : MvPolynomial (Fin (n + 2)) ℂ)) ∧
      ∀ F ∈ bergmanSpace ω A B, F ∈ Submodule.span ℂ (s : Set (MvPolynomial (Fin (n + 2)) ℂ)) := by
  classical
  set W := bergmanSpace ω A B
  let b := Module.finBasis ℂ W
  set L := ⌊A⌋₊
  set t : Finset (MvPolynomial (Fin (n + 2)) ℂ) :=
    Finset.image (fun p : Fin (Module.finrank ℂ W) × ℕ =>
      weightedHomogeneousComponent xWeightFin p.2 (b p.1 : MvPolynomial (Fin (n + 2)) ℂ))
      (Finset.univ ×ˢ Finset.range (L + 1))
  have ht : ∀ P ∈ t, P ∈ W ∧ ∃ e : ℕ, P.IsWeightedHomogeneous xWeightFin e := by
    intro P hP
    obtain ⟨⟨k, e⟩, _, rfl⟩ := Finset.mem_image.1 hP
    exact ⟨weightedHomogeneousComponent_mem_bergmanSpace hω hrot (b k).2 e, e,
      weightedHomogeneousComponent_isWeightedHomogeneous e _⟩
  have hspan : ∀ F ∈ W, F ∈ Submodule.span ℂ (t : Set (MvPolynomial (Fin (n + 2)) ℂ)) := by
    intro F hF
    have hb : ∀ k, (b k : MvPolynomial (Fin (n + 2)) ℂ) ∈
        Submodule.span ℂ (t : Set (MvPolynomial (Fin (n + 2)) ℂ)) := by
      intro k
      have hdeg : ∀ m ∈ (b k : MvPolynomial (Fin (n + 2)) ℂ).support,
          Finsupp.weight xWeightFin m ≤ L := by
        intro m hm
        rw [weight_xWeightFin]
        exact Nat.le_floor ((b k).2.1 m hm).1
      rw [← sum_weightedHomogeneousComponent_range hdeg]
      exact Submodule.sum_mem _ fun e he => Submodule.subset_span
        (Finset.mem_image.2 ⟨(k, e), by simpa using he, rfl⟩)
    have hrepr := congrArg Subtype.val (b.sum_repr ⟨F, hF⟩)
    rw [Submodule.coe_sum] at hrepr
    simp only [Submodule.coe_smul] at hrepr
    rw [← hrepr]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)
  obtain ⟨s', hs't, hspan', hli⟩ :=
    exists_linearIndependent ℂ (t : Set (MvPolynomial (Fin (n + 2)) ℂ))
  have hfin : s'.Finite := t.finite_toSet.subset hs't
  refine ⟨hfin.toFinset, fun P hP => ht P (hs't (hfin.mem_toFinset.1 hP)), ?_, ?_⟩
  · exact hli.comp (fun P : hfin.toFinset => (⟨P.1, hfin.mem_toFinset.1 P.2⟩ : s'))
      fun P Q h => Subtype.ext (congrArg Subtype.val h :)
  · intro F hF
    rw [hfin.coe_toFinset, hspan']
    exact hspan F hF

/-- **Equivalence of norms on `W`**: for a linearly independent finite family `P_k` of polynomials
with `‖P_k‖_ω < ∞` and `ω > 0` a.e., `∑ |a_k| ≤ C ‖∑ a_k P_k‖_ω`. The weighted norm is the norm of
`L²(ω λ)` (Mathlib's `Lp`), injective on polynomials since nonzero polynomials vanish only on null
sets (`volume_mvPolynomial_zeroSet_eq_zero`). -/
theorem exists_sum_norm_le {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    (hpos : ∀ᵐ z, ω z ≠ 0) {ι : Type*} [Fintype ι] {P : ι → MvPolynomial (Fin (n + 2)) ℂ}
    (hP : LinearIndependent ℂ P) (hmem : ∀ k, wNormSq ω (P k) < ⊤) :
    ∃ C : ℝ, ∀ a : ι → ℂ,
      ∑ k, ‖a k‖ ≤ C * Real.sqrt (wNormSq ω (∑ k, a k • P k)).toReal := by
  set μ := volume.withDensity ω
  have hk : ∀ k, MemLp (fun z => eval z (P k)) 2 μ := fun k => (memLp_eval_iff hω _).2 (hmem k)
  have hfun : ∀ a : ι → ℂ, (fun z => eval z (∑ k, a k • P k)) =
      ∑ k, a k • (fun z => eval z (P k)) := fun a => by
    funext z
    simp [map_sum, smul_eval]
  have hmemLp : ∀ a : ι → ℂ, MemLp (fun z => eval z (∑ k, a k • P k)) 2 μ := fun a => by
    rw [hfun a]
    exact memLp_finsetSum' _ fun k _ => (hk k).const_smul (a k)
  let Lmap : (ι → ℂ) →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun a => (hmemLp a).toLp _
      map_add' := fun a b => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => ?_)
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => ?_)
        simp [Finset.mul_sum, mul_smul, smul_eval] }
  have hnorm : ∀ a, ‖Lmap a‖ = Real.sqrt (wNormSq ω (∑ k, a k • P k)).toReal := by
    intro a
    change ‖(hmemLp a).toLp _‖ = _
    rw [Lp.norm_toLp, eLpNorm_eval_eq hω, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
  have hinj : Function.Injective Lmap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h0 : (fun z => eval z (∑ k, a k • P k)) =ᵐ[μ] 0 := by
      have h1 := (hmemLp a).coeFn_toLp
      have h2 : (hmemLp a).toLp _ = 0 := ha
      rw [h2] at h1
      exact h1.symm.trans (Lp.coeFn_zero ℂ 2 μ)
    have h1 : ∀ᵐ z ∂volume, eval z (∑ k, a k • P k) = 0 :=
      (withDensity_absolutelyContinuous' hω.aemeasurable hpos).ae_le h0
    exact funext (Fintype.linearIndependent_iff.1 hP a (mvPolynomial_eq_zero_of_ae_eval_eq_zero h1))
  let e := (LinearEquiv.ofInjective Lmap hinj).toContinuousLinearEquiv
  refine ⟨Fintype.card ι * ‖(e.symm : LinearMap.range Lmap →L[ℂ] ι → ℂ)‖, fun a => ?_⟩
  have h1 : ‖a‖ ≤ ‖(e.symm : LinearMap.range Lmap →L[ℂ] ι → ℂ)‖ * ‖Lmap a‖ := by
    have := (e.symm : LinearMap.range Lmap →L[ℂ] ι → ℂ).le_opNorm (e a)
    simpa [e] using this
  have h2 : ∑ k, ‖a k‖ ≤ Fintype.card ι * ‖a‖ := by
    calc ∑ k, ‖a k‖ ≤ ∑ _k : ι, ‖a‖ := Finset.sum_le_sum fun k _ => norm_le_pi_norm a k
      _ = Fintype.card ι * ‖a‖ := by simp
  rw [← hnorm]
  calc ∑ k, ‖a k‖ ≤ Fintype.card ι * ‖a‖ := h2
    _ ≤ Fintype.card ι * (‖(e.symm : LinearMap.range Lmap →L[ℂ] ι → ℂ)‖ * ‖Lmap a‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring


/-- The coefficient bound turns `F(y) = 1` into a lower bound for `|P(y)|`. -/
theorem one_le_sum_norm_mul_sqrt {s : Finset (MvPolynomial (Fin (n + 2)) ℂ)} (a : s → ℂ)
    {F : MvPolynomial (Fin (n + 2)) ℂ} (ha : ∑ P : s, a P • (P : MvPolynomial (Fin (n + 2)) ℂ) = F)
    {y : Fin (n + 2) → ℂ} (hFy : eval y F = 1) :
    1 ≤ (∑ P : s, ‖a P‖) * Real.sqrt (∑ P ∈ s, ‖eval y P‖ ^ 2) := by
  have hPR : ∀ P ∈ s, ‖eval y P‖ ≤ Real.sqrt (∑ P ∈ s, ‖eval y P‖ ^ 2) := fun P hP => by
    rw [Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.single_le_sum (f := fun P => ‖eval y P‖ ^ 2) (fun _ _ => by positivity) hP
  have : ‖eval y F‖ ≤ ∑ P : s, ‖a P‖ * Real.sqrt (∑ P ∈ s, ‖eval y P‖ ^ 2) := by
    rw [← ha, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
    rw [smul_eval, norm_mul]
    exact mul_le_mul_of_nonneg_left (hPR P P.2) (norm_nonneg _)
  rw [hFy, norm_one, ← Finset.sum_mul] at this
  exact this

/-- The final estimate of `cor:c0-bergman-lower`, as real arithmetic. -/
theorem lower_bound_arith {S R W Nn C1 C2 CK c : ℝ} (hN : 0 < Nn) (hR : 0 ≤ R)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hCK : CK ≤ C2)
    (h1 : 1 ≤ S * R) (hS : S ≤ C1 * Real.sqrt W) (hW : W ≤ CK * Nn ^ (-c)) :
    (C1 * Real.sqrt C2)⁻¹ * Nn ^ (c / 2) ≤ R := by
  have hW' : Real.sqrt W ≤ Real.sqrt C2 * Nn ^ (-(c / 2)) := by
    have h2 : W ≤ C2 * Nn ^ (-c) :=
      hW.trans (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hN.le _))
    calc Real.sqrt W ≤ Real.sqrt (C2 * Nn ^ (-c)) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt C2 * Nn ^ (-(c / 2)) := by
        rw [Real.sqrt_mul hC2.le, Real.sqrt_eq_rpow (Nn ^ (-c)), ← Real.rpow_mul hN.le]
        congr 2
        ring
  have h3 : 1 ≤ C1 * Real.sqrt C2 * Nn ^ (-(c / 2)) * R := by
    calc (1 : ℝ) ≤ S * R := h1
      _ ≤ C1 * (Real.sqrt C2 * Nn ^ (-(c / 2))) * R :=
        mul_le_mul_of_nonneg_right (hS.trans (mul_le_mul_of_nonneg_left hW' hC1.le)) hR
      _ = _ := by ring
  have hpow : Nn ^ (-(c / 2)) * Nn ^ (c / 2) = 1 := by
    rw [← Real.rpow_add hN, neg_add_cancel, Real.rpow_zero]
  have hNc : 0 < Nn ^ (c / 2) := Real.rpow_pos_of_pos hN _
  have hsq : 0 < Real.sqrt C2 := Real.sqrt_pos.2 hC2
  rw [inv_mul_le_iff₀ (mul_pos hC1 hsq)]
  calc Nn ^ (c / 2) = 1 * Nn ^ (c / 2) := (one_mul _).symm
    _ ≤ C1 * Real.sqrt C2 * Nn ^ (-(c / 2)) * R * Nn ^ (c / 2) :=
        mul_le_mul_of_nonneg_right h3 hNc.le
    _ = C1 * Real.sqrt C2 * R * (Nn ^ (-(c / 2)) * Nn ^ (c / 2)) := by ring
    _ = C1 * Real.sqrt C2 * R := by rw [hpow, mul_one]

/-- **Polynomials dominating a fractional power** (`cor:c0-bergman-lower`, finite-dimensional
part). Let `ω λ` be invariant under `x ↦ e^{iϑ}x` with `ω > 0` a.e., and let `W =
bergmanSpace ω A B`. Assume the extension property of `prop:c0-l2-extension`: for every compact
`K` there is `C_K` such that every `y ∈ K \ Z(g)` admits `F ∈ W` with `F(y) = 1` and
`‖F‖²_ω ≤ C_K |g(y)|^{-2c}`. Then there are finitely many `x`-homogeneous `P_1, …, P_r ∈ W`
(independent of `K`) such that for every compact `K` there is `c_K > 0` with
`|P(y)| ≥ c_K |g(y)|^c` on `K`, where `|P|² = ∑ |P_k|²` and `|g|² = normSqFam g`. -/
theorem exists_homogeneous_lower_bound {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    {ω : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω) (hpos : ∀ᵐ z, ω z ≠ 0)
    (hrot : ∀ ϑ z, ω (xtRot ϑ 0 z) = ω z) (A B : ℝ)
    (hext : ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ CK : ℝ, ∀ y ∈ K,
      normSqFam g y ≠ 0 → ∃ F ∈ bergmanSpace ω A B, eval y F = 1 ∧
        (wNormSq ω F).toReal ≤ CK * normSqFam g y ^ (-c)) :
    ∃ s : Finset (MvPolynomial (Fin (n + 2)) ℂ),
      (∀ P ∈ s, P ∈ bergmanSpace ω A B ∧ ∃ e : ℕ, P.IsWeightedHomogeneous xWeightFin e) ∧
      ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
        cK * normSqFam g y ^ (c / 2) ≤ Real.sqrt (∑ P ∈ s, ‖eval y P‖ ^ 2) := by
  classical
  obtain ⟨s, hs, hli, hspan⟩ := exists_homogeneous_basis hω hrot A B
  have hmem : ∀ P : s, wNormSq ω P.1 < ⊤ := fun P =>
    ((mem_bergmanSpace_iff hω).1 (hs P.1 P.2).1).2
  have hli' : LinearIndependent ℂ (fun P : s => P.1) := hli
  obtain ⟨CW, hCW⟩ := exists_sum_norm_le (ι := s) hω hpos hli' hmem
  refine ⟨s, hs, fun K hK => ?_⟩
  obtain ⟨CK, hCK⟩ := hext K hK
  have hC1pos : 0 < max CW 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC2pos : 0 < max CK 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max CW 1 * Real.sqrt (max CK 1))⁻¹, by positivity, fun y hy => ?_⟩
  by_cases hy0 : normSqFam g y = 0
  · rw [hy0, Real.zero_rpow (by positivity), mul_zero]
    exact Real.sqrt_nonneg _
  · have hN : 0 < normSqFam g y := lt_of_le_of_ne (normSqFam_nonneg g y) (Ne.symm hy0)
    obtain ⟨F, hFW, hFy, hFn⟩ := hCK y hy hy0
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 (hspan F hFW)
    have ha : ∑ P : s, f P.1 • P.1 = F := by
      rw [← hf]
      exact Finset.sum_coe_sort s (fun P => f P • P)
    have hsum : ∑ P : s, ‖f P.1‖ ≤ max CW 1 * Real.sqrt (wNormSq ω F).toReal := by
      have := hCW (fun P => f P.1)
      rw [ha] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    exact lower_bound_arith hN (Real.sqrt_nonneg _) hC1pos hC2pos (le_max_left _ _)
      (one_le_sum_norm_mul_sqrt (fun P => f P.1) ha hFy) hsum hFn


/-- Elements of `W` are square integrable against any weight dominated by a multiple of `ω` on a
set `K` (in `cor:c0-bergman-lower`: `|g|^{-2c} ≤ sup_K (1 + |z|²)^{N+1} ω` on compact `K`). -/
theorem setLIntegral_le_wNormSq {ω w : (Fin (n + 2) → ℂ) → ℝ≥0∞} (hω : Measurable ω)
    {K : Set (Fin (n + 2) → ℂ)} {M : ℝ≥0∞} (hK : MeasurableSet K) (hw : ∀ z ∈ K, w z ≤ M * ω z)
    (F : MvPolynomial (Fin (n + 2)) ℂ) :
    ∫⁻ z in K, w z * ‖eval z F‖ₑ ^ 2 ≤ M * wNormSq ω F := by
  calc ∫⁻ z in K, w z * ‖eval z F‖ₑ ^ 2 ≤ ∫⁻ z in K, M * (ω z * ‖eval z F‖ₑ ^ 2) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hK).2 (Filter.Eventually.of_forall
          fun z hz => ?_))
        rw [← mul_assoc]
        exact mul_le_mul_left (hw z hz) _
    _ ≤ ∫⁻ z, M * (ω z * ‖eval z F‖ₑ ^ 2) := setLIntegral_le_lintegral _ _
    _ = M * wNormSq ω F := by
        rw [lintegral_const_mul M (f := fun z => ω z * ‖eval z F‖ₑ ^ 2)
          (hω.mul (measurable_enorm_eval_sq F))]
        rfl

end EnvelopeProperty.Char0
