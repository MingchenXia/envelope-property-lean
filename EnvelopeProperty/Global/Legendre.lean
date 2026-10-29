/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Data.EReal.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A one-variable Legendre formula

This file implements the blueprint node `lem:gl-legendre` of the global chapter `global.tex` of
the formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX). It is an elementary one-variable replacement for Boucksom–Jonsson,
*Global pluripotential theory over a trivially valued field* (BJ22), Lemma 6.20,
which is used in the proof of BJ22 Theorem 6.15 (homogenization of Fubini–Study
functions, `thm:gl-homog-fs` here).

For finitely many reals `λ_i` and `y_i ∈ [-∞, +∞)`,
```
inf_{t > 0} max_i (y_i + t λ_i) = max ( max_{λ_i ≥ 0} y_i,
                                        max_{λ_i > 0 > λ_l} (λ_i y_l - λ_l y_i) / (λ_i - λ_l) ),
```
where `(λ_i y_l - λ_l y_i) / (λ_i - λ_l)` is written as the convex combination
`w y_l + w' y_i` with `w = λ_i / (λ_i - λ_l) > 0`, `w' = -λ_l / (λ_i - λ_l) > 0`, `w + w' = 1`
(`EnvelopeProperty.legendrePairTerm`). The right-hand side is
`EnvelopeProperty.legendreMax`, and the formula is
`EnvelopeProperty.iInf_sup_add_mul_eq_legendreMax`. The weights are rational when the `λ_i` are
(`EnvelopeProperty.legendre_weights_pos`).

## Deviations from the blueprint and BJ22

* BJ22 Lemma 6.20 is stated for `x ∈ ℝ^r` but applied (in the proof of BJ22 Theorem 6.15)
  to `x_i = log |s_i|(v)`, which is `-∞` at zeros of `s_i` ( §9, literature issue 6). The
  formula here allows `y_i = -∞` directly; the finite set of weights `W` is explicit and no
  polyhedral theory is needed.
* The hypothesis `max_i λ_i ≥ 0` of the blueprint is not needed: if all `λ_i < 0` both sides
  are `-∞`.

## Proof

`F(t) = max_i (y_i + t λ_i)`. The right-hand side `ρ` is `≤ F(t)` for every `t ≥ 0`
(`EnvelopeProperty.legendreMax_le`): `y_i ≤ y_i + t λ_i` for `λ_i ≥ 0`, and the convex
combination with weights `w, w'` of `y_l + t λ_l` and `y_i + t λ_i` is the pair term. Conversely,
`inf_{t > 0} F ≤ F(t₀)` for every `t₀ ≥ 0` (`F(t₀ + δ) ≤ F(t₀) + δ Λ`), and an explicit `t₀ ≥ 0`
with `F(t₀) ≤ ρ` is constructed: with `P` (resp. `N`) the indices with `λ ≥ 0` (resp. `λ < 0`)
and `y ≠ -∞`, and `τ_{il}` the time where the lines `i ∈ P` and `l ∈ N` cross,
`t₀ = max(0, max_{l ∈ N} min_{i ∈ P} τ_{il})`; every line of `N` is below some line of `P` at
`t₀`, and the lines of `P` are below the crossing value of the extremal pair, which is either a
value `y_i` (`λ_i = 0`) or a pair term. If `P = ∅`, both sides are `-∞`.
-/

open Finset

noncomputable section

namespace EnvelopeProperty

variable {ι : Type*}

/-! ### Auxiliary facts on `EReal` -/

/-- `x ≤ y` in `EReal` as soon as `x ≤ y + ε` for all real `ε > 0`. -/
theorem legendre_ereal_le_of_forall_pos_le_add {x y : EReal}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ y + (ε : EReal)) : x ≤ y := by
  induction y using EReal.rec with
  | bot => simpa using h 1 one_pos
  | top => exact le_top
  | coe b =>
    induction x using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add, top_le_iff] at this
      exact absurd this (EReal.coe_ne_top _)
    | coe a =>
      refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun ε hε => ?_)
      have := h ε hε
      rwa [← EReal.coe_add, EReal.coe_le_coe_iff] at this

/-! ### The right-hand side -/

/-- The pair term `(λ_i y_l - λ_l y_i) / (λ_i - λ_l)` of `lem:gl-legendre` for `p = (i, l)`,
written as the convex combination `w y_l + w' y_i` with `w = λ_i / (λ_i - λ_l)` and
`w' = -λ_l / (λ_i - λ_l)`. -/
def legendrePairTerm (lam : ι → ℝ) (y : ι → EReal) (p : ι × ι) : EReal :=
  ((lam p.1 / (lam p.1 - lam p.2) : ℝ) : EReal) * y p.2 +
    ((-lam p.2 / (lam p.1 - lam p.2) : ℝ) : EReal) * y p.1

open Classical in
/-- The right-hand side of the **one-variable Legendre formula** (`lem:gl-legendre`):
`max (max_{λ_i ≥ 0} y_i, max_{λ_i > 0 > λ_l} (λ_i y_l - λ_l y_i) / (λ_i - λ_l))`. -/
def legendreMax (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal) : EReal :=
  max ((s.filter fun i => 0 ≤ lam i).sup y)
    (((s ×ˢ s).filter fun p => 0 < lam p.1 ∧ lam p.2 < 0).sup (legendrePairTerm lam y))

/-- The weights of a pair term are positive, sum to `1`, and annihilate the slopes:
`w λ_l + w' λ_i = 0`. -/
theorem legendre_weights_pos {li ll : ℝ} (hi : 0 < li) (hl : ll < 0) :
    0 < li / (li - ll) ∧ 0 < -ll / (li - ll) ∧ li / (li - ll) + -ll / (li - ll) = 1 ∧
      li / (li - ll) * ll + -ll / (li - ll) * li = 0 := by
  have hd : 0 < li - ll := by linarith
  refine ⟨div_pos hi hd, div_pos (by linarith) hd, ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hd.ne']
    ring
  · field_simp
    ring

/-- The real value of a pair term with finite entries. -/
theorem legendrePairTerm_coe (lam : ι → ℝ) (Y : ι → ℝ) (p : ι × ι) :
    legendrePairTerm lam (fun i => (Y i : EReal)) p =
      (((lam p.1 * Y p.2 - lam p.2 * Y p.1) / (lam p.1 - lam p.2) : ℝ) : EReal) := by
  rw [legendrePairTerm, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  ring

/-- A pair term is at most every common upper bound of the two lines at any time `t`. -/
theorem legendrePairTerm_le {lam : ι → ℝ} {y : ι → EReal} {p : ι × ι} (hi : 0 < lam p.1)
    (hl : lam p.2 < 0) (hyi : y p.1 ≠ ⊤) (hyl : y p.2 ≠ ⊤) {t : ℝ} {M : EReal}
    (h₁ : y p.1 + ((t * lam p.1 : ℝ) : EReal) ≤ M) (h₂ : y p.2 + ((t * lam p.2 : ℝ) : EReal) ≤ M) :
    legendrePairTerm lam y p ≤ M := by
  obtain ⟨hw, hw', -, -⟩ := legendre_weights_pos hi hl
  rw [legendrePairTerm]
  by_cases hbl : y p.2 = ⊥
  · rw [hbl, EReal.coe_mul_bot_of_pos hw, EReal.bot_add]
    exact bot_le
  by_cases hbi : y p.1 = ⊥
  · rw [hbi, EReal.coe_mul_bot_of_pos hw', EReal.add_bot]
    exact bot_le
  lift y p.1 to ℝ using ⟨hyi, hbi⟩ with Yi hYi
  lift y p.2 to ℝ using ⟨hyl, hbl⟩ with Yl hYl
  rw [← EReal.coe_add] at h₁ h₂
  induction M using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 h₁) (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe M =>
    rw [EReal.coe_le_coe_iff] at h₁ h₂
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hd : 0 < lam p.1 - lam p.2 := by linarith
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left h₂ hi.le, mul_le_mul_of_nonneg_left h₁ (neg_nonneg.2 hl.le)]

/-! ### The two inequalities -/

/-- The right-hand side is a lower bound of `max_i (y_i + t λ_i)` for every `t ≥ 0`. -/
theorem legendreMax_le (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal) (hy : ∀ i ∈ s, y i ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    legendreMax s lam y ≤ s.sup fun i => y i + ((t * lam i : ℝ) : EReal) := by
  classical
  refine max_le (Finset.sup_le fun i hi => ?_) (Finset.sup_le fun p hp => ?_)
  · obtain ⟨hi, hli⟩ := Finset.mem_filter.1 hi
    refine le_trans ?_ (Finset.le_sup (f := fun i => y i + ((t * lam i : ℝ) : EReal)) hi)
    exact le_add_of_nonneg_right (EReal.coe_nonneg.2 (mul_nonneg ht hli))
  · obtain ⟨hp, hpi, hpl⟩ := Finset.mem_filter.1 hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    exact legendrePairTerm_le hpi hpl (hy _ h₁) (hy _ h₂)
      (Finset.le_sup (f := fun i => y i + ((t * lam i : ℝ) : EReal)) h₁)
      (Finset.le_sup (f := fun i => y i + ((t * lam i : ℝ) : EReal)) h₂)

/-- `inf_{t > 0} F(t) ≤ F(t₀)` for every `t₀ ≥ 0`, since `F(t₀ + δ) ≤ F(t₀) + δ Λ`. -/
theorem iInf_sup_add_mul_le (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) :
    ⨅ (t : ℝ) (_ : 0 < t), s.sup (fun i => y i + ((t * lam i : ℝ) : EReal)) ≤
      s.sup fun i => y i + ((t₀ * lam i : ℝ) : EReal) := by
  set Λ : ℝ := ∑ i ∈ s, |lam i| + 1 with hΛ
  have hΛpos : 0 < Λ := by
    have : 0 ≤ ∑ i ∈ s, |lam i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  refine legendre_ereal_le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / Λ := div_pos hε hΛpos
  refine (iInf₂_le (t₀ + ε / Λ) (by linarith)).trans ?_
  refine Finset.sup_le fun i hi => ?_
  have hli : lam i ≤ Λ := by
    have := Finset.single_le_sum (f := fun i => |lam i|) (fun _ _ => abs_nonneg _) hi
    have := le_abs_self (lam i)
    linarith
  rw [add_mul, EReal.coe_add, ← add_assoc]
  refine add_le_add (Finset.le_sup (f := fun i => y i + ((t₀ * lam i : ℝ) : EReal)) hi) ?_
  rw [EReal.coe_le_coe_iff]
  calc ε / Λ * lam i ≤ ε / Λ * Λ := mul_le_mul_of_nonneg_left hli hδ.le
    _ = ε := div_mul_cancel₀ ε hΛpos.ne'

/-- If no index has `λ_i ≥ 0` and `y_i ≠ -∞`, the infimum is `-∞`. -/
theorem iInf_sup_add_mul_eq_bot (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal)
    (hy : ∀ i ∈ s, y i ≠ ⊤) (hP : ∀ i ∈ s, 0 ≤ lam i → y i = ⊥) :
    ⨅ (t : ℝ) (_ : 0 < t), s.sup (fun i => y i + ((t * lam i : ℝ) : EReal)) = ⊥ := by
  refine (EReal.eq_bot_iff_forall_lt _).2 fun M => ?_
  set t : ℝ := 1 + ∑ j ∈ s, |(y j).toReal - (M - 1)| / |lam j| with ht
  have hsum : 0 ≤ ∑ j ∈ s, |(y j).toReal - (M - 1)| / |lam j| :=
    Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (abs_nonneg _)
  have htpos : 0 < t := by linarith
  refine lt_of_le_of_lt (iInf₂_le t htpos) ?_
  refine lt_of_le_of_lt (Finset.sup_le fun i hi => ?_) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
  by_cases hbi : y i = ⊥
  · rw [hbi, EReal.bot_add]
    exact bot_le
  have hli : lam i < 0 := by
    by_contra h
    exact hbi (hP i hi (not_lt.1 h))
  lift y i to ℝ using ⟨hy i hi, hbi⟩ with Yi hYi
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hterm : |Yi - (M - 1)| / |lam i| ≤ t := by
    have := Finset.single_le_sum (f := fun j => |(y j).toReal - (M - 1)| / |lam j|)
      (fun j _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) hi
    simp only [← hYi, EReal.toReal_coe] at this
    linarith
  have habs : |lam i| = -lam i := abs_of_neg hli
  rw [habs, div_le_iff₀ (by linarith)] at hterm
  nlinarith [le_abs_self (Yi - (M - 1))]

/-- The main construction: if some index has `λ_i ≥ 0` and `y_i ≠ -∞`, there is `t₀ ≥ 0` with
`max_i (y_i + t₀ λ_i) ≤ ρ`. -/
theorem exists_sup_add_mul_le_legendreMax (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal)
    (hy : ∀ i ∈ s, y i ≠ ⊤) (hP : ∃ i ∈ s, 0 ≤ lam i ∧ y i ≠ ⊥) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      (s.sup fun i => y i + ((t₀ * lam i : ℝ) : EReal)) ≤ legendreMax s lam y := by
  classical
  set ρ := legendreMax s lam y with hρ
  set P := s.filter fun i => 0 ≤ lam i ∧ y i ≠ ⊥ with hPdef
  set N := s.filter fun l => lam l < 0 ∧ y l ≠ ⊥ with hNdef
  have hPne : P.Nonempty := by
    obtain ⟨i, hi, h⟩ := hP
    exact ⟨i, Finset.mem_filter.2 ⟨hi, h⟩⟩
  set Y : ι → ℝ := fun i => (y i).toReal with hYdef
  have hYP : ∀ i ∈ P, y i = (Y i : EReal) := fun i hi => by
    obtain ⟨hi, -, hb⟩ := Finset.mem_filter.1 hi
    exact (EReal.coe_toReal (hy i hi) hb).symm
  have hYN : ∀ l ∈ N, y l = (Y l : EReal) := fun l hl => by
    obtain ⟨hl, -, hb⟩ := Finset.mem_filter.1 hl
    exact (EReal.coe_toReal (hy l hl) hb).symm
  -- values `y_i ≤ ρ` for `i ∈ P`
  have hvalP : ∀ i ∈ P, (Y i : EReal) ≤ ρ := fun i hi => by
    obtain ⟨his, hli, -⟩ := Finset.mem_filter.1 hi
    rw [← hYP i hi]
    exact le_max_of_le_left (Finset.le_sup (f := y) (Finset.mem_filter.2 ⟨his, hli⟩))
  -- pair values `≤ ρ`
  have hvalPair : ∀ i ∈ P, ∀ l ∈ N, 0 < lam i →
      (((lam i * Y l - lam l * Y i) / (lam i - lam l) : ℝ) : EReal) ≤ ρ := by
    intro i hi l hl hli
    obtain ⟨his, -, -⟩ := Finset.mem_filter.1 hi
    obtain ⟨hls, hll, -⟩ := Finset.mem_filter.1 hl
    have hmem : (i, l) ∈ (s ×ˢ s).filter fun p => 0 < lam p.1 ∧ lam p.2 < 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨his, hls⟩, hli, hll⟩
    have h := Finset.le_sup (f := legendrePairTerm lam y) hmem
    refine le_trans (le_of_eq ?_) (le_max_of_le_right h)
    rw [legendrePairTerm, hYP i hi, hYN l hl, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add]
    congr 1
    field_simp
    ring
  -- crossing times
  set τ : ι → ι → ℝ := fun i l => (Y l - Y i) / (lam i - lam l) with hτ
  have hden : ∀ i ∈ P, ∀ l ∈ N, 0 < lam i - lam l := fun i hi l hl => by
    have := (Finset.mem_filter.1 hi).2.1
    have := (Finset.mem_filter.1 hl).2.1
    linarith
  -- `t ≤ τ i l` iff line `i` is below line `l` at `t`
  have hle_τ : ∀ i ∈ P, ∀ l ∈ N, ∀ t : ℝ, t ≤ τ i l → Y i + t * lam i ≤ Y l + t * lam l := by
    intro i hi l hl t h
    rw [hτ, le_div_iff₀ (hden i hi l hl)] at h
    linarith
  have hτ_le : ∀ i ∈ P, ∀ l ∈ N, ∀ t : ℝ, τ i l ≤ t → Y l + t * lam l ≤ Y i + t * lam i := by
    intro i hi l hl t h
    rw [hτ, div_le_iff₀ (hden i hi l hl)] at h
    linarith
  set m : ι → ℝ := fun l => P.inf' hPne fun i => τ i l with hm
  set t₀ : ℝ := if hN : N.Nonempty then max 0 (N.sup' hN m) else 0 with ht₀
  have ht₀nn : 0 ≤ t₀ := by
    rw [ht₀]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  -- lines of `P` at `t₀`
  have hclaimP : ∀ i ∈ P, ((Y i + t₀ * lam i : ℝ) : EReal) ≤ ρ := by
    intro i hi
    by_cases hzero : t₀ = 0
    · rw [hzero, zero_mul, add_zero]
      exact hvalP i hi
    have hN : N.Nonempty := by
      by_contra hN
      exact hzero (by rw [ht₀, dif_neg hN])
    have ht₀eq : t₀ = N.sup' hN m := by
      have h₁ : t₀ = max 0 (N.sup' hN m) := by rw [ht₀, dif_pos hN]
      rcases le_total (N.sup' hN m) 0 with h | h
      · exact absurd (by rw [h₁, max_eq_left h]) hzero
      · rw [h₁, max_eq_right h]
    obtain ⟨l₀, hl₀, hl₀eq⟩ := Finset.exists_mem_eq_sup' hN m
    obtain ⟨i₀, hi₀, hi₀eq⟩ := Finset.exists_mem_eq_inf' hPne fun i => τ i l₀
    have ht₀τ : t₀ = τ i₀ l₀ := by rw [ht₀eq, hl₀eq]; exact hi₀eq
    have hmin : t₀ ≤ τ i l₀ := by
      rw [ht₀eq, hl₀eq]
      exact Finset.inf'_le (fun i => τ i l₀) hi
    have h₁ : Y i + t₀ * lam i ≤ Y l₀ + t₀ * lam l₀ := hle_τ i hi l₀ hl₀ t₀ hmin
    have h₂ : Y l₀ + t₀ * lam l₀ = Y i₀ + t₀ * lam i₀ :=
      le_antisymm (hτ_le i₀ hi₀ l₀ hl₀ t₀ ht₀τ.ge) (hle_τ i₀ hi₀ l₀ hl₀ t₀ ht₀τ.le)
    refine le_trans (EReal.coe_le_coe_iff.2 (h₁.trans h₂.le)) ?_
    rcases (Finset.mem_filter.1 hi₀).2.1.lt_or_eq with hpos | hzero'
    · refine le_trans (le_of_eq ?_) (hvalPair i₀ hi₀ l₀ hl₀ hpos)
      congr 1
      have hd := hden i₀ hi₀ l₀ hl₀
      rw [ht₀τ, hτ]
      field_simp
      ring
    · rw [← hzero', mul_zero, add_zero]
      exact hvalP i₀ hi₀
  -- lines of `N` at `t₀`
  have hclaimN : ∀ l ∈ N, ((Y l + t₀ * lam l : ℝ) : EReal) ≤ ρ := by
    intro l hl
    have hN : N.Nonempty := ⟨l, hl⟩
    obtain ⟨i₁, hi₁, hi₁eq⟩ := Finset.exists_mem_eq_inf' hPne fun i => τ i l
    have hge : τ i₁ l ≤ t₀ := by
      rw [← hi₁eq]
      calc P.inf' hPne (fun i => τ i l) = m l := rfl
        _ ≤ N.sup' hN m := Finset.le_sup' m hl
        _ ≤ max 0 (N.sup' hN m) := le_max_right _ _
        _ = t₀ := by rw [ht₀, dif_pos hN]
    exact le_trans (EReal.coe_le_coe_iff.2 (hτ_le i₁ hi₁ l hl t₀ hge)) (hclaimP i₁ hi₁)
  refine ⟨t₀, ht₀nn, Finset.sup_le fun i hi => ?_⟩
  by_cases hbi : y i = ⊥
  · rw [hbi, EReal.bot_add]
    exact bot_le
  rcases le_or_gt 0 (lam i) with hli | hli
  · have hiP : i ∈ P := Finset.mem_filter.2 ⟨hi, hli, hbi⟩
    rw [hYP i hiP, ← EReal.coe_add]
    exact hclaimP i hiP
  · have hiN : i ∈ N := Finset.mem_filter.2 ⟨hi, hli, hbi⟩
    rw [hYN i hiN, ← EReal.coe_add]
    exact hclaimN i hiN

/-- **The one-variable Legendre formula** (`lem:gl-legendre`; BJ22 Lemma 6.20 with `-∞`
entries allowed): for finitely many `λ_i ∈ ℝ` and `y_i ∈ [-∞, +∞)`,
`inf_{t > 0} max_i (y_i + t λ_i) = max (max_{λ_i ≥ 0} y_i,
max_{λ_i > 0 > λ_l} (λ_i y_l - λ_l y_i) / (λ_i - λ_l))`. -/
theorem iInf_sup_add_mul_eq_legendreMax (s : Finset ι) (lam : ι → ℝ) (y : ι → EReal)
    (hy : ∀ i ∈ s, y i ≠ ⊤) :
    ⨅ (t : ℝ) (_ : 0 < t), s.sup (fun i => y i + ((t * lam i : ℝ) : EReal)) =
      legendreMax s lam y := by
  refine le_antisymm ?_ (le_iInf₂ fun t ht => legendreMax_le s lam y hy ht.le)
  by_cases hP : ∃ i ∈ s, 0 ≤ lam i ∧ y i ≠ ⊥
  · obtain ⟨t₀, ht₀, h⟩ := exists_sup_add_mul_le_legendreMax s lam y hy hP
    exact (iInf_sup_add_mul_le s lam y ht₀).trans h
  · simp only [not_exists, not_and, not_not] at hP
    rw [iInf_sup_add_mul_eq_bot s lam y hy hP]
    exact bot_le

end EnvelopeProperty
