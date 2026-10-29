/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Compactification
import EnvelopeProperty.Projective.SubvarietyPSH
import EnvelopeProperty.Projective.SubvarietyDivision

/-!
# The compactification lemma on a projectively normal `V(I) ⊆ ℙᴹ`, regularizable functions

Let `k` be a field with the trivial absolute value, `X = V(I) ⊆ ℙᴹ` a projective subvariety
(`EnvelopeProperty.ProjSubvariety`) which is **projectively normal** (`ProjSubvariety.IsProjNormal`:
`S = R_M / I` integrally closed), `σ ∉ I` a form of degree `e ≥ 1`, and
`Y = Spec A_σ` the affine chart `{σ ≠ 0}` of `X`, with `A_σ = QuotChartAlg I σ e` and chart
`ι_σ : U_σ ∩ X^an ≃ Y^an` (`ProjSubvariety.chartMap`, inverse `ProjSubvariety.chartInv`). This file
proves Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX),
Lemma 5.10(2) (`lem:compactification`) on `X` for regularizable inputs: blueprint node
`lem:pg-compactification-extend` (`projective-general.tex`, subsection `subsec:pg-normal`). It is
the analogue on `X` of the `ℙⁿ` version `ProjBerk.isPSH_chartExt`
(`EnvelopeProperty.Projective.Compactification`, `lem:bj-compactification-extend`), with
factoriality of `k[x₀, …, xₙ]` replaced by the division lemma `lem:pg-division`
(`ProjSubvariety.exists_isHomogeneous_sub_pow_mul_mem_of_log_le`), which uses the normality of
`S`, and with psh functions on `X^an` in the sense of `def:pg-subvariety-psh`
(`ProjSubvariety.IsPSH`).

For `w : Y^an → [-∞, ∞)` and `a ∈ ℝ`, `ProjSubvariety.chartExt X σ e w a : X^an → EReal` is the
function equal to `w ∘ ι_σ + a log|σ|` on `U_σ ∩ X^an` and to `-∞` on its complement.

## Main results

* `ProjSubvariety.isPSH_chartExt_of_fs` (FS form): if `w` is the limit of a
  decreasing sequence `u_j ∈ FS(Y)` with `u_j ≤ -α log|σ| + C_j`, `w ≢ -∞`, and `a > max(α, 0)`,
  then `chartExt X σ e w a ∈ PSH(X, a e)`. Each term `a_t log|f_t| + b_t` of `u_j`, with
  `f_t = τ̄_t / σ̄^{N_t} ≠ 0`, satisfies `log|τ_t| - N_t log|σ| ≤ -(α / a_t) log|σ| + C`, so the
  division lemma applied to `τ_t^r` gives `τ_t^r ≡ σ^{N'_t} τ'_t (mod I)`, and on `X^an`
  `a_t log|f_t| + a log|σ| = ε_t log|τ'_t| + δ_t log|σ| + b_t` with `ε_t, δ_t > 0` and
  `ε_t deg τ'_t + δ_t e = a e` (`ProjSubvariety.isPSH_chartExt_fsTerm`). The extension of `u_j` is
  the maximum of these psh functions of class `a e` and of `a log|σ| + b_0`, and PSH2
  (`ProjSubvariety.isPSH_of_antitone_seq`, `thm:pg-psh2`) passes to the limit.
* `ProjSubvariety.isPSH_chartExt` (`lem:pg-compactification-extend`): under the instance argument
  `WuRegularization` (through its growth control `WuRegularization.growthControl`, FHX
  Lemma 5.11(5), `thm:import-growth-control`), for `k` algebraically closed, `X` projectively
  normal, `w ∈ ℛ(Y)` with `w ≤ -κ log|σ| + B` on `Y^an`, `κ ∈ ℚ_{>0}` and a rational `a > κ`,
  `chartExt X σ e w a ∈ PSH(X, a e)`. The growth control is applied on the normal affine variety `Y`
  (`lem:pg-chart-normal`, `ProjSubvariety.isIntegrallyClosed_quotChartAlg_and`) to
  `g = max{0, max_{|α| = e} κ log|x̄^α / σ̄|} = -κ log|σ|` (`ProjSubvariety.growthFSData`,
  `ProjSubvariety.eval_growthFSData`) and a rational `c ∈ (1, a / κ)`.

## Deviations from the blueprint

* As in the `ℙⁿ` version, the Fubini–Study functions `Ψ_j` of the blueprint are not
  assembled into a single FS datum: each term is shown to be psh of class `a e` (sums, positive
  real multiples and constants of FS functions of `X` are psh, `thm:pg-psh-basic`) and `Ψ_j` is
  their finite maximum (`ProjSubvariety.isPSH_max_finset_sup`). Terms with `f_t = 0` (i.e.
  `τ_t ∈ I`) are `-∞` and are absorbed by the constant term. The integer `r` (the blueprint's
  `ϱ`) is chosen per term; it is used uniformly, also when `N_t < α / a_t` (then
  `⌊r (N_t - α / a_t)⌋₊ = 0`).
* Finiteness of the limit: the blueprint uses `φ(⋆) = w(v_triv) > -∞` (`lem:reg-triv-finite`);
  here `w ≢ -∞` (part of `w ∈ ℛ(Y)`) is transported directly through `ι_σ⁻¹`.
* The FS form is stated for real `a > 0` and real `α < a` (the division lemma needs
  `β ≥ 0`; a negative `α` is replaced by `0`, using `log|σ| ≤ 0`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter MvPolynomial

open EnvelopeProperty.ProjBerk (QuotChartAlg quotChartMk quotChartGen)

noncomputable section

namespace EnvelopeProperty

namespace ProjSubvariety

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
  {σ : MvPolynomial (Fin (M + 1)) k} {e : ℕ}

/-! ### Preliminaries -/

/-- Forms congruent modulo `I` have the same absolute value at every point of `X^an`. -/
theorem val_eq_of_sub_mem (v : X.an) {f g : MvPolynomial (Fin (M + 1)) k}
    (h : f - g ∈ X.ideal) : (v : ProjBerk k M).1.val f = (v : ProjBerk k M).1.val g := by
  have h₁ : (v : ProjBerk k M).1.val (f - g) = 0 := v.2 _ h
  have h₂ : (v : ProjBerk k M).1.val (g - f) = 0 :=
    v.2 _ (by rw [← neg_sub]; exact X.ideal.neg_mem h)
  refine le_antisymm ?_ ?_
  · calc (v : ProjBerk k M).1.val f = (v : ProjBerk k M).1.val (f - g + g) := by
          rw [sub_add_cancel]
      _ ≤ max ((v : ProjBerk k M).1.val (f - g)) ((v : ProjBerk k M).1.val g) :=
          Valuation.map_add _ _ _
      _ = (v : ProjBerk k M).1.val g := by rw [h₁, max_eq_right (by positivity)]
  · calc (v : ProjBerk k M).1.val g = (v : ProjBerk k M).1.val (g - f + f) := by
          rw [sub_add_cancel]
      _ ≤ max ((v : ProjBerk k M).1.val (g - f)) ((v : ProjBerk k M).1.val f) :=
          Valuation.map_add _ _ _
      _ = (v : ProjBerk k M).1.val f := by rw [h₂, max_eq_right (by positivity)]

variable (X) in
/-- `log|s|` is a Fubini–Study function of class `d` on `X^an` for a form `s ∉ I` of degree
`d`. -/
theorem isFS_logAbs {d : ℕ} {s : MvPolynomial (Fin (M + 1)) k} (hs : s.IsHomogeneous d)
    (hsI : s ∉ X.ideal) : X.IsFS (d : ℚ) fun v => ProjBerk.logAbs s v.1 := by
  have hs0 : s ≠ 0 := fun h => hsI (h ▸ X.ideal.zero_mem)
  refine isFS_iff_exists_restrict.2 ⟨ProjBerk.logAbs s, ProjBerk.isFS_logAbs hs hs0, ?_,
    fun _ => rfl⟩
  rw [X.logAbs_triv_of_notMem hsI]
  exact EReal.zero_ne_bot

/-- Every element of `A_σ = QuotChartAlg I σ e` is `τ̄ / σ̄^N` for a form `τ` of degree `N e`. -/
theorem exists_eq_quotChartMk (hσ : σ.IsHomogeneous e) (f : QuotChartAlg X.ideal σ e) :
    ∃ (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k), τ.IsHomogeneous (N * e) ∧
      f = quotChartMk X.ideal σ e N τ := by
  obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨N, τ, hτ, rfl⟩ := ProjBerk.exists_eq_chartMk hσ f'
  exact ⟨N, τ, hτ, rfl⟩

/-- A finite maximum `max(B, maxᵢ Fᵢ)` is `θ`-psh on `X^an` if all `max(B, Fᵢ)` are. -/
theorem isPSH_max_finset_sup {θ : ℝ} {ι : Type*} (s : Finset ι) {B : X.an → EReal}
    (hB : X.IsPSH θ B) {F : ι → X.an → EReal}
    (hF : ∀ i ∈ s, X.IsPSH θ fun v => max (B v) (F i v)) :
    X.IsPSH θ fun v => max (B v) (s.sup fun i => F i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, max_bot_right] using hB
  | insert i s hi ih =>
    simp only [Finset.sup_insert]
    have h := (hF i (Finset.mem_insert_self i s)).max
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have e : (fun v => max (B v) (max (F i v) (s.sup fun i => F i v))) =
        fun v => max (max (B v) (F i v)) (max (B v) (s.sup fun i => F i v)) := by
      funext v
      exact sup_sup_distrib_left _ _ _
    rw [e]
    exact h

/-! ### The extension `chartExt` -/

variable (X σ e) in
open Classical in
/-- The function on `X^an` equal to `w ∘ ι_σ + a log|σ|` on `U_σ ∩ X^an = {|σ| ≠ 0}` and to
`-∞` on its complement (FHX Lemma 5.10(2), `lem:pg-compactification-extend`). -/
def chartExt (w : Berk k (QuotChartAlg X.ideal σ e) → EReal) (a : ℝ) (v : X.an) : EReal :=
  if hv : (v : ProjBerk k M).1.val σ ≠ 0 then
    w (X.chartMap σ e v hv) + (a : EReal) * ProjBerk.logAbs σ v.1
  else ⊥

theorem chartExt_of_ne_zero (w : Berk k (QuotChartAlg X.ideal σ e) → EReal) (a : ℝ) {v : X.an}
    (hv : (v : ProjBerk k M).1.val σ ≠ 0) :
    X.chartExt σ e w a v = w (X.chartMap σ e v hv) + (a : EReal) * ProjBerk.logAbs σ v.1 :=
  dif_pos hv

theorem chartExt_of_eq_zero (w : Berk k (QuotChartAlg X.ideal σ e) → EReal) (a : ℝ) {v : X.an}
    (hv : (v : ProjBerk k M).1.val σ = 0) : X.chartExt σ e w a v = ⊥ :=
  dif_neg (not_not.2 hv)

theorem chartExt_chartInv (hσ : σ.IsHomogeneous e) (he : 0 < e)
    (w : Berk k (QuotChartAlg X.ideal σ e) → EReal) (a : ℝ)
    (y : Berk k (QuotChartAlg X.ideal σ e)) :
    X.chartExt σ e w a (X.chartInv σ e hσ he y) =
      w y + (a : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 := by
  rw [chartExt_of_ne_zero w a (chartInv_val_ne_zero hσ he y), chartMap_chartInv]

/-- The extension of a constant `b`: `a log|σ| + b`, of class `a e`. -/
theorem isPSH_chartExt_const (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) {a : ℝ} (ha : 0 < a)
    (b : ℝ) : X.IsPSH (a * e) (X.chartExt σ e (fun _ => (b : EReal)) a) := by
  have h : X.chartExt σ e (fun _ => (b : EReal)) a =
      fun v => (a : EReal) * ProjBerk.logAbs σ v.1 + b := by
    funext v
    by_cases hv : (v : ProjBerk k M).1.val σ = 0
    · rw [chartExt_of_eq_zero _ _ hv, (ProjBerk.logAbs_eq_bot_iff σ v.1).2 hv,
        EReal.coe_mul_bot_of_pos ha, EReal.bot_add]
    · rw [chartExt_of_ne_zero _ _ hv, add_comm]
  rw [h]
  have := ((X.isFS_logAbs hσ hσI).isPSH.smul ha).add_const b
  simpa only [Rat.cast_natCast] using this

/-- **The division step** of `lem:pg-compactification-extend`: if a term `a_t log|f| + b_t` of an
affine FS function on `Y = Spec A_σ`, with `f ≠ 0`, satisfies `a_t log|f| + b_t ≤ -α log|σ| + C`
on `Y^an`, with `0 ≤ α < a`, then its extension `chartExt X σ e (fsTerm t) a` is psh of class
`a e`. Writing `f = τ̄ / σ̄^N`, the division lemma (`lem:pg-division`) applied to `τ^r` gives
`τ^r ≡ σ^{N'} τ' (mod I)` and the extension is
`(a_t / r) log|τ'| + (a - a_t N + a_t N' / r) log|σ| + b_t` on `X^an`, with positive
coefficients for `r` large. -/
theorem isPSH_chartExt_fsTerm (hX : X.IsProjNormal) (hσ : σ.IsHomogeneous e) (he : 0 < e)
    (hσI : σ ∉ X.ideal) {t : QuotChartAlg X.ideal σ e × ℚ × ℚ} (ht : 0 < t.2.1) (hf : t.1 ≠ 0)
    {α a C : ℝ} (hα : 0 ≤ α) (hαa : α < a)
    (hbound : ∀ y, fsTerm t y ≤
      -(α : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 + (C : EReal)) :
    X.IsPSH (a * e) (X.chartExt σ e (fsTerm t) a) := by
  obtain ⟨f, a₁, b₁⟩ := t
  simp only at ht hf
  obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_quotChartMk hσ f
  have hτI : τ ∉ X.ideal := fun h => hf ((ProjBerk.quotChartMk_eq_zero_iff hσI hτ).2 h)
  have hat : (0 : ℝ) < a₁ := by exact_mod_cast ht
  -- the growth bound in real form
  have hreal : ∀ v : X.an, (v : ProjBerk k M).1.val σ ≠ 0 → (v : ProjBerk k M).1.val τ ≠ 0 →
      (a₁ : ℝ) * (Real.log ((v : ProjBerk k M).1.val τ) -
        N * Real.log ((v : ProjBerk k M).1.val σ)) + b₁ ≤
        -α * Real.log ((v : ProjBerk k M).1.val σ) + C := by
    intro v hσv hτv
    have h1 := hbound (X.chartMap σ e v hσv)
    rw [chartInv_chartMap, fsTerm_def, logAbs_chartMap_quotChartMk v hσv hτ,
      ProjBerk.logAbs_eq_coe_log hσv, ProjBerk.logAbs_eq_coe_log hτv] at h1
    exact_mod_cast h1
  -- the integer `r`
  have haα : 0 < a - α := sub_pos.2 hαa
  obtain ⟨r, hr⟩ := exists_nat_gt ((a₁ : ℝ) / (a - α))
  have hr0 : (0 : ℝ) < r := lt_trans (div_pos hat haα) hr
  have hr0' : r ≠ 0 := by rintro rfl; simp at hr0
  -- division
  have hτr : (τ ^ r).IsHomogeneous ((N * r) * e) := by
    have h := hτ.pow r
    rwa [show N * e * r = N * r * e by ring] at h
  obtain ⟨τ', hτ', hmem⟩ := exists_isHomogeneous_sub_pow_mul_mem_of_log_le
    (C := r * (C - b₁) / a₁) hX hσ hσI hτr (β := r * α / a₁) (by positivity)
    fun v hσv hτv => by
      have hτv' : (v : ProjBerk k M).1.val τ ≠ 0 := fun h0 =>
        hτv (by rw [map_pow, h0, zero_pow hr0'])
      have h1 := hreal v hσv hτv'
      rw [map_pow, NNReal.coe_pow, Real.log_pow]
      refine le_of_mul_le_mul_left ?_ hat
      have key := mul_le_mul_of_nonneg_left h1 hr0.le
      have e1 : (a₁ : ℝ) * (-(r * α / a₁) * Real.log ((v : ProjBerk k M).1.val σ) +
          r * (C - b₁) / a₁) =
          r * (-α * Real.log ((v : ProjBerk k M).1.val σ) + C) - r * b₁ := by
        field_simp
        ring
      rw [e1]
      push_cast
      nlinarith [key]
  set N' := ⌊((N * r : ℕ) : ℝ) - r * α / a₁⌋₊ with hN'
  have hle : N' ≤ N * r := Nat.floor_le_of_le (by
    have : 0 ≤ (r : ℝ) * α / a₁ := by positivity
    linarith)
  have hτ'I : τ' ∉ X.ideal := by
    intro h
    have hmem' : τ ^ r ∈ X.ideal := by
      have := X.ideal.add_mem hmem (X.ideal.mul_mem_left (σ ^ N') h)
      rwa [sub_add_cancel] at this
    exact hτI (X.isPrime.mem_of_pow_mem r hmem')
  have hD' : (((N * r - N') * e : ℕ) : ℝ) = (N * r - N') * e := by
    rw [Nat.cast_mul, Nat.cast_sub hle]
    push_cast
    ring
  -- the coefficients `ε = a_t / r` and `δ = a - a_t N + a_t N' / r`
  have hε : 0 < (a₁ : ℝ) / r := div_pos hat hr0
  have hδ : 0 < a - a₁ * N + a₁ * N' / r := by
    rcases le_or_gt 0 (((N * r : ℕ) : ℝ) - r * α / a₁) with h | h
    · have h1 : ((N * r : ℕ) : ℝ) - r * α / a₁ < N' + 1 := Nat.lt_floor_add_one _
      have h2 : 0 < ((a₁ : ℝ) / r) * (N' - (N * r - r * α / a₁ - 1)) := by
        refine mul_pos hε ?_
        push_cast at h1
        linarith
      have hrat : (a₁ : ℝ) / r < a - α := by
        rw [div_lt_iff₀ hr0]
        rw [div_lt_iff₀ haα] at hr
        linarith
      have e2 : ((a₁ : ℝ) / r) * (N' - (N * r - r * α / a₁ - 1)) =
          a₁ * N' / r - a₁ * N + α + a₁ / r := by
        field_simp
        ring
      linarith
    · have hN0 : N' = 0 := Nat.floor_eq_zero.2 (h.trans one_pos)
      have h2 : ((a₁ : ℝ) / r) * (N * r - r * α / a₁) < 0 := by
        refine mul_neg_of_pos_of_neg hε ?_
        push_cast at h
        linarith
      have e2 : ((a₁ : ℝ) / r) * (N * r - r * α / a₁) = a₁ * N - α := by
        field_simp
      rw [hN0, Nat.cast_zero, mul_zero, zero_div, add_zero]
      linarith
  have hclass : (a₁ : ℝ) / r * (((N * r - N') * e : ℕ) : ℝ) +
      (a - a₁ * N + a₁ * N' / r) * e = a * e := by
    rw [hD']
    field_simp
    ring
  -- the psh function
  have hψ : X.IsPSH (a * e) fun v => (((a₁ : ℝ) / r : ℝ) : EReal) * ProjBerk.logAbs τ' v.1 +
      ((a - a₁ * N + a₁ * N' / r : ℝ) : EReal) * ProjBerk.logAbs σ v.1 + ((b₁ : ℝ) : EReal) := by
    have h1 := (((X.isFS_logAbs hτ' hτ'I).isPSH.smul hε).add
      ((X.isFS_logAbs hσ hσI).isPSH.smul hδ)).add_const b₁
    rw [Rat.cast_natCast, Rat.cast_natCast, hclass] at h1
    exact h1
  convert hψ using 1
  funext v
  by_cases hσv : (v : ProjBerk k M).1.val σ = 0
  · rw [chartExt_of_eq_zero _ _ hσv, (ProjBerk.logAbs_eq_bot_iff σ v.1).2 hσv,
      EReal.coe_mul_bot_of_pos hδ, EReal.add_bot, EReal.bot_add]
  rw [chartExt_of_ne_zero _ _ hσv, fsTerm_def, logAbs_chartMap_quotChartMk v hσv hτ]
  have hfacv : (v : ProjBerk k M).1.val τ ^ r =
      (v : ProjBerk k M).1.val σ ^ N' * (v : ProjBerk k M).1.val τ' := by
    rw [← map_pow, val_eq_of_sub_mem v hmem, map_mul, map_pow]
  by_cases hτv : (v : ProjBerk k M).1.val τ = 0
  · have hτ'v : (v : ProjBerk k M).1.val τ' = 0 := by
      rw [hτv, zero_pow hr0'] at hfacv
      exact (mul_eq_zero.1 hfacv.symm).resolve_left (pow_ne_zero _ hσv)
    rw [(ProjBerk.logAbs_eq_bot_iff τ v.1).2 hτv, (ProjBerk.logAbs_eq_bot_iff τ' v.1).2 hτ'v]
    simp only [EReal.bot_sub, EReal.coe_mul_bot_of_pos hat, EReal.coe_mul_bot_of_pos hε,
      EReal.bot_add]
  have hτ'v : (v : ProjBerk k M).1.val τ' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfacv
    exact pow_ne_zero r hτv hfacv
  have hrel : (r : ℝ) * Real.log ((v : ProjBerk k M).1.val τ) =
      N' * Real.log ((v : ProjBerk k M).1.val σ) + Real.log ((v : ProjBerk k M).1.val τ') := by
    have h1 := congrArg (fun x : ℝ≥0 => Real.log (x : ℝ)) hfacv
    simp only [NNReal.coe_pow, NNReal.coe_mul] at h1
    rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by exact_mod_cast hσv))
      (by exact_mod_cast hτ'v), Real.log_pow] at h1
    exact h1
  rw [ProjBerk.logAbs_eq_coe_log hσv, ProjBerk.logAbs_eq_coe_log hτv,
    ProjBerk.logAbs_eq_coe_log hτ'v]
  have hLτ' : Real.log ((v : ProjBerk k M).1.val τ' : ℝ) =
      r * Real.log ((v : ProjBerk k M).1.val τ) - N' * Real.log ((v : ProjBerk k M).1.val σ) := by
    linarith
  have key : (a₁ : ℝ) * (Real.log ((v : ProjBerk k M).1.val τ) -
      N * Real.log ((v : ProjBerk k M).1.val σ)) + b₁ + a * Real.log ((v : ProjBerk k M).1.val σ) =
      a₁ / r * Real.log ((v : ProjBerk k M).1.val τ') +
        (a - a₁ * N + a₁ * N' / r) * Real.log ((v : ProjBerk k M).1.val σ) + b₁ := by
    rw [hLτ']
    field_simp
    ring
  exact_mod_cast key

/-- The extension of an affine FS function on `Y` is the maximum of the extensions of its
constant and of its terms. -/
theorem chartExt_eval (g : EnvelopeProperty.FSData k (QuotChartAlg X.ideal σ e)) (a : ℝ) :
    X.chartExt σ e g.eval a = fun v => max (X.chartExt σ e (fun _ => ((g.const : ℝ) : EReal)) a v)
      (g.terms.sup fun t => X.chartExt σ e (fsTerm t) a v) := by
  funext v
  by_cases hv : (v : ProjBerk k M).1.val σ = 0
  · simp only [chartExt_of_eq_zero _ _ hv, Finset.sup_bot, max_self]
  · simp only [chartExt_of_ne_zero _ _ hv]
    rw [EnvelopeProperty.FSData.eval_def, ← max_add_add_right,
      EnvelopeProperty.FSData.sup_add_coe]

/-- `-α log|σ| ≤ -max(α, 0) log|σ|` on the chart, since `log|σ| ≤ 0`. -/
theorem neg_mul_logAbs_le_max (hσ : σ.IsHomogeneous e) (he : 0 < e) (α : ℝ)
    (y : Berk k (QuotChartAlg X.ideal σ e)) :
    -(α : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 ≤
      -((max α 0 : ℝ) : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 := by
  rw [ProjBerk.logAbs_eq_coe_log (chartInv_val_ne_zero hσ he y), ← EReal.coe_neg,
    ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hL := ProjBerk.real_log_val_le_zero σ (X.chartInv σ e hσ he y).1
  have hm := le_max_left α 0
  nlinarith

/-- **Compactification, part (2)** on `X`, FS form (`lem:pg-compactification-extend`):
let `X` be projectively normal, `σ ∉ I` a form of degree `e ≥ 1`, and `w` the limit of a
decreasing sequence of affine FS functions `u_j` on `Y = Spec A_σ` with `u_j ≤ -α log|σ| + C_j`,
`w ≢ -∞`. For every real `a > max(α, 0)`, the function equal to `w + a log|σ|` on
`Y^an = U_σ ∩ X^an` and to `-∞` elsewhere lies in `PSH(X, a e)`. -/
theorem isPSH_chartExt_of_fs (hX : X.IsProjNormal) (hσ : σ.IsHomogeneous e) (he : 0 < e)
    (hσI : σ ∉ X.ideal) {g : ℕ → EnvelopeProperty.FSData k (QuotChartAlg X.ideal σ e)}
    (hanti : ∀ y, Antitone fun j => (g j).eval y)
    {w : Berk k (QuotChartAlg X.ideal σ e) → EReal} (hw : ∀ y, w y = ⨅ j, (g j).eval y)
    (hfin : ∃ y, w y ≠ ⊥) {α a : ℝ} (ha : 0 < a) (hαa : α < a)
    (hgrowth : ∀ j, ∃ C : ℝ, ∀ y,
      (g j).eval y ≤ -(α : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 + (C : EReal)) :
    X.IsPSH (a * e) (X.chartExt σ e w a) := by
  have hα' : 0 ≤ max α 0 := le_max_right _ _
  have hαa' : max α 0 < a := max_lt hαa ha
  have hΨ : ∀ j, X.IsPSH (a * e) (X.chartExt σ e (g j).eval a) := by
    intro j
    obtain ⟨C, hC⟩ := hgrowth j
    rw [chartExt_eval]
    refine isPSH_max_finset_sup _ (isPSH_chartExt_const hσ hσI ha _) fun t ht => ?_
    by_cases hf : t.1 = 0
    · have h0 : X.chartExt σ e (fsTerm t) a = fun _ => ⊥ := by
        funext v
        by_cases hv : (v : ProjBerk k M).1.val σ = 0
        · exact chartExt_of_eq_zero _ _ hv
        · rw [chartExt_of_ne_zero _ _ hv, fsTerm_eq_bot ((g j).pos t ht) (by rw [hf, map_zero]),
            EReal.bot_add]
      rw [h0]
      simpa only [max_bot_right] using isPSH_chartExt_const hσ hσI ha _
    · exact (isPSH_chartExt_const hσ hσI ha _).max (isPSH_chartExt_fsTerm hX hσ he hσI
        ((g j).pos t ht) hf hα' hαa' fun y => ((g j).fsTerm_le_eval ht y).trans
          ((hC y).trans (add_le_add_left (neg_mul_logAbs_le_max hσ he α y) _)))
  refine isPSH_of_antitone_seq (θ := fun _ => a * e) tendsto_const_nhds hΨ
    (fun v j j' hjj' => ?_) (fun v => ?_) ?_
  · dsimp only
    by_cases hv : (v : ProjBerk k M).1.val σ = 0
    · rw [chartExt_of_eq_zero _ _ hv, chartExt_of_eq_zero _ _ hv]
    · rw [chartExt_of_ne_zero _ _ hv, chartExt_of_ne_zero _ _ hv]
      exact add_le_add_left (hanti _ hjj') _
  · by_cases hv : (v : ProjBerk k M).1.val σ = 0
    · simp only [chartExt_of_eq_zero _ _ hv, iInf_const]
    · simp only [chartExt_of_ne_zero _ _ hv]
      rw [ProjBerk.logAbs_eq_coe_log hv, ← EReal.coe_mul, iInf_add_coe_of_antitone (hanti _)
        ((g 0).eval_ne_top _), hw]
  · obtain ⟨y, hy⟩ := hfin
    refine ⟨X.chartInv σ e hσ he y, ?_⟩
    rw [chartExt_chartInv, ProjBerk.logAbs_eq_coe_log (chartInv_val_ne_zero hσ he y),
      ← EReal.coe_mul]
    exact EReal.add_ne_bot_iff.2 ⟨hy, EReal.coe_ne_bot _⟩

/-! ### The growth function `-κ log|σ|` on the chart -/

variable (X) in
/-- The affine FS function `max{0, max_{|α| = e} κ log|x̄^α / σ̄|}` on `Y = Spec A_σ`, equal to
`-κ log|σ|` on `Y^an = U_σ ∩ X^an` (`eval_growthFSData`). -/
def growthFSData (hσ : σ.IsHomogeneous e) {κ : ℚ} (hκ : 0 < κ) :
    EnvelopeProperty.FSData k (QuotChartAlg X.ideal σ e) := by
  classical
  exact
  { terms := (Finset.finsuppAntidiag Finset.univ e).image fun α =>
      (quotChartGen X.ideal σ e α, κ, 0)
    const := 0
    pos := fun t ht => by
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 ht
      exact hκ
    gen := by
      refine eq_top_iff.2 ((ProjBerk.adjoin_quotChartGen (I := X.ideal) hσ).symm.le.trans
        (Algebra.adjoin_mono ?_))
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨(quotChartGen X.ideal σ e α, κ, 0),
        Finset.mem_image.2 ⟨α, ProjBerk.mem_finsuppAntidiag_univ.2 hα, rfl⟩, rfl⟩ }

theorem eval_growthFSData (hσ : σ.IsHomogeneous e) (he : 0 < e) {κ : ℚ} (hκ : 0 < κ)
    (y : Berk k (QuotChartAlg X.ideal σ e)) :
    (X.growthFSData hσ hκ).eval y =
      -((κ : ℝ) : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 := by
  classical
  set v := X.chartInv σ e hσ he y with hv_def
  have hσv : (v : ProjBerk k M).1.val σ ≠ 0 := chartInv_val_ne_zero hσ he y
  have hy : X.chartMap σ e v hσv = y := chartMap_chartInv hσ he y
  have hL0 : Real.log ((v : ProjBerk k M).1.val σ : ℝ) ≤ 0 :=
    ProjBerk.real_log_val_le_zero σ v.1
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  rw [EnvelopeProperty.FSData.eval_def]
  dsimp only [growthFSData]
  rw [Finset.sup_image]
  simp only [Function.comp_def, fsTerm_def, Rat.cast_zero, EReal.coe_zero, add_zero]
  rw [← EnvelopeProperty.FSData.coe_mul_sup _ _ hκ', ← hy, sup_logAbs_chartMap_quotChartGen v hσv,
    ProjBerk.logAbs_eq_coe_log hσv, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_neg,
    ← EReal.coe_mul, max_eq_right (by exact_mod_cast (mul_nonneg hκ'.le (neg_nonneg.2 hL0)))]
  congr 1
  ring

/-! ### Regularizable functions (`lem:pg-compactification-extend`) -/

/-- **Compactification, part (2), for regularizable functions** on a projectively normal
`X = V(I)` (FHX Lemma 5.10(2) for `w ∈ ℛ(Y)`, `lem:pg-compactification-extend`),
under the instance argument `WuRegularization` (through `WuRegularization.growthControl`, FHX
Lemma 5.11(5), `thm:import-growth-control`). Let `k` be
algebraically closed, `X` projectively normal, `σ ∉ I` a form of degree `e ≥ 1`, `w ∈ ℛ(Y)` on
the chart `Y = Spec A_σ`, and `κ ∈ ℚ_{>0}`, `B₀ ∈ ℝ` with `w ≤ -κ log|σ| + B₀` on `Y^an`. For every
rational `a > κ`, the function equal to `w + a log|σ|` on `Y^an = U_σ ∩ X^an` and to `-∞`
elsewhere lies in `PSH(X, a e)`. -/
theorem isPSH_chartExt [IsAlgClosed k] [WuRegularization.{u, u} k] (hX : X.IsProjNormal)
    (hσ : σ.IsHomogeneous e) (he : 0 < e) (hσI : σ ∉ X.ideal)
    {w : Berk k (QuotChartAlg X.ideal σ e) → EReal} (hw : IsRegularizable w) {κ : ℚ}
    (hκ : 0 < κ) {B₀ : ℝ}
    (hwB : ∀ y, w y ≤ -((κ : ℝ) : EReal) * ProjBerk.logAbs σ (X.chartInv σ e hσ he y).1 +
      (B₀ : EReal))
    {a : ℚ} (ha : κ < a) : X.IsPSH ((a : ℝ) * e) (X.chartExt σ e w a) := by
  obtain ⟨hdom, hft, hic⟩ := isIntegrallyClosed_quotChartAlg_and hX hσ hσI
  obtain ⟨c, hc1, hca⟩ := exists_rat_btwn (show (1 : ℚ) < a / κ from (one_lt_div hκ).2 ha)
  have hcκ : c * κ < a := (lt_div_iff₀ hκ).1 hca
  obtain ⟨h, hanti, hinf, hbd⟩ := WuRegularization.growthControl (QuotChartAlg X.ideal σ e) w
    (X.growthFSData hσ hκ) B₀ hw (fun y => by rw [eval_growthFSData hσ he]; exact hwB y) c hc1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hκ.trans ha
  refine isPSH_chartExt_of_fs hX hσ he hσI hanti hinf hw.1 (α := ((c * κ : ℚ) : ℝ)) ha0
    (by exact_mod_cast hcκ) fun j => ?_
  obtain ⟨C, hC⟩ := hbd j
  refine ⟨C, fun y => (hC y).trans_eq ?_⟩
  rw [eval_growthFSData hσ he, ProjBerk.logAbs_eq_coe_log (chartInv_val_ne_zero hσ he y),
    ProjBerk.ereal_coe_mul_neg_coe_mul, Rat.cast_mul]

end ProjSubvariety

end EnvelopeProperty
