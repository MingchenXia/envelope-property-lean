/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.AdditiveSandwich
import EnvelopeProperty.Global.MultDiagonal

/-!
# Psh functions descend through the normalization of a unibranch model (FHX Theorem 8.3)

This file implements the blueprint nodes `thm:gl-normalization-reflection` (`global.tex`,
subsection `subsec:gl-main`) and `thm:nn-normalization-reflection` (`nonnef.tex`, subsection
`subsec:nn-main`) for the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, §8, Theorem 8.3 `thm:normalization-reflection`), for
every class `θ ∈ ℝ^r`, and the unibranch-to-normal step of the main
theorem (`thm:gl-main`, `thm:nn-main`).

Let `𝒳` be a unibranch model over an algebraically closed field `k`, `𝒴 = 𝒳^ν` its
normalization and `ν^an: 𝒴^an ≃ₜ 𝒳^an` (`MultiModel.IsUnibranch.anHomeomorph`,
`lem:gl-unibranch-universal`).

## Main results

* `MultiModel.IsUnibranch.exists_isFS_sandwich` (characteristic `0`): for `φ ∈ 𝓗(𝒴, b)` with
  `φ(⋆) ≤ C`, every rational `δ ∈ (0, 1)` and `η > 0`, there are `b'` with `|b' - b| < η` and
  `G ∈ 𝓗(𝒳, b')` with `u ≤ G ≤ (1 - δ) u` for `u = (φ - C) ∘ (ν^an)⁻¹` (the sandwiched
  approximants of the proof of `thm:nn-normalization-reflection`, built from
  `lem:nn-additive-sandwich`).
* `MultiModel.IsUnibranch.isPSH_comp_symm_of_charZero` (**`thm:nn-normalization-reflection`,
  characteristic `0`**): `ψ ∘ (ν^an)⁻¹ ∈ PSH(𝒳, θ)` for `ψ ∈ PSH(𝒴, θ)`, every `θ ∈ ℝ^r`, by the
  multiplicatively sandwiched diagonal lemma `FSSystemC.isPSH_of_sandwich`
  (`cor:nn-sandwich-diagonal`).
* `MultiModel.IsUnibranch.isPSH_comp_symm` (**FHX Theorem 8.3**, any characteristic): the
  characteristic-free combination with `MultiModel.IsUnibranch.isPSH_comp_symm_of_charP`
  (`EnvelopeProperty.Global.NormalizationDescentCharP`). No hypothesis besides the model data:
  Frobenius descent (`thm:gl-frobenius-descent`) and additive powers (`thm:gl-additive-powers`)
  are theorems.
* `MultiModel.IsUnibranch.isPSH_comp_iff`: `PSH(𝒴, θ) = PSH(𝒳, θ) ∘ ν^an`.
* `MultiModel.IsUnibranch.hasEnvelopeProperty_of_normalization` (the step
  "`EP_{𝒳^ν}(θ) ⇒ EP_𝒳(θ)`" of `thm:gl-main`/`thm:nn-main`), and
  `MultiModel.IsUnibranch.hasEnvelopeProperty_normalization_iff`.

## Deviations from the blueprint proof

* Characteristic `0`: the blueprint fixes `α₀` and works with the net `(ψ_α - C)_{α ≥ α₀}`; here
  the tail `{α // α₀ ≤ α}` is used with `C = ψ_{α₀}(⋆)`. Terms `(s_t, λ_t)` of the
  Fubini–Study data with `s_t = 0` (allowed by `MultiModel.FSData`) are discarded; the others
  satisfy `μ_t = λ_t/m - C ≤ 0`. The common class is `b' = b + ε 𝟙` with
  `ε = max_t 3R_t/(m(n + 2d_t))` (the blueprint's `b`), reached from the classes of the
  `m⁻¹ F^{(t)}` by `IsFS.mono_class`.
* The blueprint's integer `n` is chosen with `n ≥ n_t`, `2d_t ≤ δ n` and `3R_t < m η n` for all
  `t`, which gives `n/(n + 2d_t) ≥ 1 - δ` and `3R_t/(m(n + 2d_t)) < η`.
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-- `max_t f_t + c = max_t (f_t + c)` in `EReal` for a real constant `c` (also for the empty
family, `⊥ + c = ⊥`). -/
theorem ereal_finset_sup_add_coe {ι : Type*} (s : Finset ι) (f : ι → EReal) (c : ℝ) :
    s.sup f + (c : EReal) = s.sup fun i => f i + (c : EReal) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sup_cons, Finset.sup_cons, ← ih]
    exact (max_add_add_right (f a) (s.sup f) (c : EReal)).symm

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-- Finite maxima of Fubini–Study functions of one class `b`: `max_{i ∈ s} φ_i ∈ 𝓗(𝒳, b)` for a
nonempty finite family (`lem:gl-fs-system`, (FS4)). -/
theorem isFS_finset_sup {X : MultiModel k K r} {b : Fin r → ℚ} {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {φ : ι → X.an → EReal} (h : ∀ i ∈ s, X.IsFS b (φ i)) :
    X.IsFS b fun v => s.sup fun i => φ i v := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup_singleton] using h a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h' : ∀ v, (Finset.cons a s ha).sup (fun i => φ i v) =
        max (φ a v) (s.sup fun i => φ i v) := fun v => Finset.sup_cons ha
    simp only [h']
    exact (h a (Finset.mem_cons_self a s)).max (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

section Unibranch

variable {X : MultiModel k K r} [Infinite k] [PerfectField k]

namespace IsUnibranch

variable (hX : X.IsUnibranch)

include hX

/-- **Sandwiched approximants in characteristic `0`** (proof of
`thm:nn-normalization-reflection`). Let `φ = m⁻¹ max_t (log |s_t| + λ_t) ∈ 𝓗(𝒴, b)` with
`φ(⋆) ≤ C`, put `u = (φ - C) ∘ (ν^an)⁻¹`, and let `δ ∈ (0, 1)` be rational and `η > 0`. There are
`b' ∈ ℚ^r` with `|b' - b| < η` and `G ∈ 𝓗(𝒳, b')` with `u ≤ G ≤ (1 - δ) u` on `𝒳^an`:
`G = max_t (m⁻¹ F^{(t)} + μ_t)` with `μ_t = λ_t/m - C ≤ 0` and `F^{(t)}` the additive-power
sandwich of `s_t` (`lem:nn-additive-sandwich`, `exists_isHomFS_sandwich`). -/
theorem exists_isFS_sandwich [IsAlgClosed k] [CharZero k] {b : Fin r → ℚ}
    {φ : X.normalization.an → EReal} (hφ : X.normalization.IsFS b φ) {C : ℝ}
    (hC : φ X.normalization.triv ≤ C) {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ (b' : Fin r → ℚ) (G : X.an → EReal),
      dist (fun c => (b' c : ℝ)) (fun c => (b c : ℝ)) < η ∧ X.IsFS b' G ∧
        ∀ v : X.an, φ (hX.anHomeomorph.symm v) + ((-C : ℝ) : EReal) ≤ G v ∧
          G v ≤ (((1 - δ : ℚ) : ℝ) : EReal) *
            (φ (hX.anHomeomorph.symm v) + ((-C : ℝ) : EReal)) := by
  classical
  obtain ⟨Dt, ⟨t₀, ht₀, ht₀0⟩, hDt⟩ := hφ
  set terms' := Dt.terms.filter fun t => t.1 ≠ 0 with hterms'
  have hmem : ∀ t ∈ terms', t ∈ Dt.terms ∧ t.1 ≠ 0 := fun t ht => Finset.mem_filter.1 ht
  have ht₀' : t₀ ∈ terms' := Finset.mem_filter.2 ⟨ht₀, ht₀0⟩
  have hne : terms'.Nonempty := ⟨t₀, ht₀'⟩
  -- the additive-power sandwich of every nonzero term
  have hS : ∀ t : K × ℝ, ∃ D R n₀ : ℕ, t ∈ terms' → ∀ n, n₀ ≤ n → ∃ F : X.an → EReal,
      X.IsHomFS (fun c => (Dt.deg c : ℚ) + 3 * R / (n + 2 * D)) F ∧
      ∀ w : X.normalization.an,
        X.normalization.logSecAbs w.1 Dt.deg t.1 ≤ F (hX.anHomeomorph w) ∧
          F (hX.anHomeomorph w) ≤
            (((n : ℝ) / (n + 2 * D) : ℝ) : EReal) * X.normalization.logSecAbs w.1 Dt.deg t.1 := by
    intro t
    by_cases ht : t ∈ terms'
    · obtain ⟨D, R, n₀, h⟩ :=
        hX.exists_isHomFS_sandwich (Dt.mem_sections t (hmem t ht).1) (hmem t ht).2
      exact ⟨D, R, n₀, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h ht⟩
  choose D R n₀ hS using hS
  set m : ℕ := Dt.m with hmdef
  have hm0 : 0 < m := Dt.m_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  -- the choice of `n`
  have hev : ∀ t ∈ terms', ∀ᶠ n : ℕ in atTop, n₀ t ≤ n ∧ 1 ≤ n ∧
      (2 * D t : ℝ) ≤ δ * n ∧ (3 * R t : ℝ) < m * η * n := by
    intro t _
    obtain ⟨K₁, hK₁⟩ := exists_nat_ge ((2 * D t : ℝ) / δ)
    obtain ⟨K₂, hK₂⟩ := exists_nat_gt ((3 * R t : ℝ) / (m * η))
    refine eventually_atTop.2 ⟨n₀ t + 1 + K₁ + K₂, fun n hn => ⟨by omega, by omega, ?_, ?_⟩⟩
    · have h1 : (K₁ : ℝ) ≤ n := by exact_mod_cast (show K₁ ≤ n by omega)
      rw [div_le_iff₀ hδR] at hK₁
      nlinarith
    · have hmη : 0 < (m : ℝ) * η := mul_pos hmR hη
      have h1 : (K₂ : ℝ) ≤ n := by exact_mod_cast (show K₂ ≤ n by omega)
      rw [div_lt_iff₀ hmη] at hK₂
      nlinarith
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset terms').2 hev).exists
  have hF : ∀ t ∈ terms', ∃ F : X.an → EReal,
      X.IsHomFS (fun c => (Dt.deg c : ℚ) + 3 * R t / (n + 2 * D t)) F ∧
      ∀ w : X.normalization.an,
        X.normalization.logSecAbs w.1 Dt.deg t.1 ≤ F (hX.anHomeomorph w) ∧
          F (hX.anHomeomorph w) ≤ (((n : ℝ) / (n + 2 * D t) : ℝ) : EReal) *
            X.normalization.logSecAbs w.1 Dt.deg t.1 :=
    fun t ht => hS t ht n (hn t ht).1
  choose! F hFhom hFbd using hF
  -- the common class `b' = b + ε 𝟙`
  set ε : ℚ := terms'.sup' hne fun t => 3 * R t / (m * (n + 2 * D t)) with hεdef
  have hεt : ∀ t ∈ terms', (3 * R t / (m * (n + 2 * D t)) : ℚ) ≤ ε := fun t ht =>
    Finset.le_sup' (fun t => (3 * R t / (m * (n + 2 * D t)) : ℚ)) ht
  have hε0 : 0 ≤ ε := (by positivity : (0 : ℚ) ≤ 3 * R t₀ / (m * (n + 2 * D t₀))).trans
    (hεt t₀ ht₀')
  have hεη : (ε : ℝ) < η := by
    obtain ⟨t₁, ht₁, hεt₁⟩ := Finset.exists_mem_eq_sup' hne
      fun t => (3 * R t / (m * (n + 2 * D t)) : ℚ)
    rw [hεdef, hεt₁]
    push_cast
    have h3 := (hn t₁ ht₁).2.2.2
    have hpos : (0 : ℝ) < m * (n + 2 * D t₁) := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (hn t₁ ht₁).2.1
      positivity
    rw [div_lt_iff₀ hpos]
    have : (0 : ℝ) ≤ m * η * (2 * D t₁) := by positivity
    nlinarith
  set b' : Fin r → ℚ := fun c => b c + ε with hb'def
  -- the terms of `G`
  set μ : K × ℝ → ℝ := fun t => t.2 / m - C with hμdef
  set Gt : K × ℝ → X.an → EReal := fun t v =>
    ((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * F t v + ((μ t : ℝ) : EReal) with hGtdef
  have hcast : ((((m : ℚ)⁻¹ : ℚ)) : ℝ) = (m : ℝ)⁻¹ := by push_cast; rfl
  have hGt : ∀ t ∈ terms', X.IsFS b' (Gt t) := by
    intro t ht
    have hcl : (m : ℚ)⁻¹ • (fun c => (Dt.deg c : ℚ) + 3 * R t / (n + 2 * D t)) ≤ b' := by
      intro c
      have key : (m : ℚ)⁻¹ * ((Dt.deg c : ℚ) + 3 * R t / (n + 2 * D t)) =
          b c + 3 * R t / (m * (n + 2 * D t)) := by
        have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast (hn t ht).2.1
        have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
        rw [Dt.deg_eq c]
        field_simp
        rfl
      simp only [Pi.smul_apply, smul_eq_mul, hb'def]
      rw [key]
      linarith [hεt t ht]
    have h1 := ((hFhom t ht).isFS.smul (c := (m : ℚ)⁻¹)
      (inv_pos.2 (by exact_mod_cast hm0))).mono_class hcl
    have h2 := h1.add (X.isFS_const (X.nonneg_mem_semiampleCone le_rfl) (μ t))
    rw [add_zero] at h2
    exact h2
  set G : X.an → EReal := fun v => terms'.sup fun t => Gt t v with hGdef
  have hG : X.IsFS b' G := isFS_finset_sup hne hGt
  -- `φ - C` as a maximum over the nonzero terms
  have hstar : ∀ y : X.normalization.an, φ y + ((-C : ℝ) : EReal) = terms'.sup fun t =>
      (((m : ℝ)⁻¹ : ℝ) : EReal) * X.normalization.logSecAbs y.1 Dt.deg t.1 +
        ((μ t : ℝ) : EReal) := by
    intro y
    rw [hDt y, FSData.eval_def, ProjBerk.ereal_coe_mul_finset_sup (inv_pos.2 hmR),
      ereal_finset_sup_add_coe]
    have hterm : ∀ t ∈ Dt.terms, (((m : ℝ)⁻¹ : ℝ) : EReal) *
        X.normalization.termVal Dt.deg t y + ((-C : ℝ) : EReal) =
          (((m : ℝ)⁻¹ : ℝ) : EReal) * X.normalization.logSecAbs y.1 Dt.deg t.1 +
            ((μ t : ℝ) : EReal) := by
      intro t _
      rw [termVal_def, ProjBerk.ereal_coe_mul_add (inv_pos.2 hmR).le, ← EReal.coe_mul,
        add_assoc, ← EReal.coe_add]
      congr 2
      simp only [hμdef]
      ring
    rw [Finset.sup_congr rfl hterm]
    refine le_antisymm (Finset.sup_le fun t ht => ?_) (Finset.sup_mono (Finset.filter_subset _ _))
    by_cases h0 : t.1 = 0
    · rw [h0, logSecAbs_zero, EReal.coe_mul_bot_of_pos (inv_pos.2 hmR), EReal.bot_add]
      exact bot_le
    · exact Finset.le_sup (f := fun t => (((m : ℝ)⁻¹ : ℝ) : EReal) *
        X.normalization.logSecAbs y.1 Dt.deg t.1 + ((μ t : ℝ) : EReal))
        (Finset.mem_filter.2 ⟨ht, h0⟩)
  -- `μ_t ≤ 0` for the nonzero terms
  have hμ : ∀ t ∈ terms', μ t ≤ 0 := by
    intro t ht
    have h1 := hstar X.normalization.triv
    have h2 : (((m : ℝ)⁻¹ : ℝ) : EReal) *
        X.normalization.logSecAbs (X.normalization.triv : Berk k X.normalization.S) Dt.deg t.1 +
          ((μ t : ℝ) : EReal) ≤ φ X.normalization.triv + ((-C : ℝ) : EReal) := by
      rw [h1]
      exact Finset.le_sup (f := fun t => (((m : ℝ)⁻¹ : ℝ) : EReal) *
        X.normalization.logSecAbs (X.normalization.triv : Berk k X.normalization.S) Dt.deg t.1 +
          ((μ t : ℝ) : EReal)) ht
    rw [logSecAbs_triv (Dt.mem_sections t (hmem t ht).1) (hmem t ht).2, mul_zero, zero_add] at h2
    have h3 : φ X.normalization.triv + ((-C : ℝ) : EReal) ≤ 0 := by
      have := add_le_add hC (le_refl ((-C : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
    exact_mod_cast h2.trans h3
  refine ⟨b', G, ?_, hG, fun v => ⟨?_, ?_⟩⟩
  · refine (dist_pi_lt_iff hη).2 fun c => ?_
    simp only [hb'def, Rat.cast_add, Real.dist_eq, add_sub_cancel_left]
    rwa [abs_of_nonneg (by exact_mod_cast hε0)]
  · -- lower bound
    rw [hstar, hGdef]
    refine Finset.sup_mono_fun fun t ht => ?_
    simp only [hGtdef, hcast]
    have h := (hFbd t ht (hX.anHomeomorph.symm v)).1
    rw [Homeomorph.apply_symm_apply] at h
    exact add_le_add (ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 hmR.le) h) le_rfl
  · -- upper bound
    rw [hstar, hGdef, ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast sub_pos.2 hδ1)]
    refine Finset.sup_mono_fun fun t ht => ?_
    simp only [hGtdef, hcast]
    set L := X.normalization.logSecAbs (hX.anHomeomorph.symm v).1 Dt.deg t.1 with hL
    have hL0 : L ≤ 0 := logSecAbs_le_zero (hX.anHomeomorph.symm v).2.2 _ _
    have h := (hFbd t ht (hX.anHomeomorph.symm v)).2
    rw [Homeomorph.apply_symm_apply] at h
    have hδ' : (0 : ℝ) < ((1 - δ : ℚ) : ℝ) := by exact_mod_cast sub_pos.2 hδ1
    have hab : ((1 - δ : ℚ) : ℝ) ≤ (n : ℝ) / (n + 2 * D t) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hn t ht).2.1
      have h2 := (hn t ht).2.2.1
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith
    have hμt := hμ t ht
    calc (((m : ℝ)⁻¹ : ℝ) : EReal) * F t v + ((μ t : ℝ) : EReal)
        ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * ((((1 - δ : ℚ) : ℝ) : EReal) * L) +
            ((μ t : ℝ) : EReal) :=
          add_le_add (ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 hmR.le)
            (h.trans (ProjBerk.ereal_coe_mul_le_of_nonpos hδ' hab hL0))) le_rfl
      _ ≤ (((1 - δ : ℚ) : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * L) +
            (((1 - δ : ℚ) : ℝ) : EReal) * ((μ t : ℝ) : EReal) := by
          have e1 : (((m : ℝ)⁻¹ : ℝ) : EReal) * ((((1 - δ : ℚ) : ℝ) : EReal) * L) =
              (((1 - δ : ℚ) : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * L) := by
            rw [ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul,
              mul_comm ((m : ℝ)⁻¹)]
          rw [e1, ← EReal.coe_mul]
          refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
          push_cast
          nlinarith
      _ = (((1 - δ : ℚ) : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * L + ((μ t : ℝ) : EReal)) :=
          (ProjBerk.ereal_coe_mul_add hδ'.le _ _).symm

/-- **Psh functions descend through the normalization in characteristic `0`, every class**
(`thm:nn-normalization-reflection`; FHX Theorem 8.3, characteristic `0`): `ψ ∘ (ν^an)⁻¹ ∈
PSH(𝒳, θ)` for every `ψ ∈ PSH(𝒴, θ)` and **every** `θ ∈ ℝ^r`. With `ψ = lim ψ_α`,
`ψ_α ∈ 𝓗(𝒴, a_α)`, and `C = ψ_{α₀}(⋆)`, the net `u_α = (ψ_α - C) ∘ (ν^an)⁻¹ ≤ 0`
(`α ≥ α₀`) has sandwiched approximants `u_α ≤ G ≤ (1 - δ) u_α` with `G ∈ 𝓗(𝒳, b)`, `b` close to
`a_α` (`exists_isFS_sandwich`), so `ψ ∘ (ν^an)⁻¹ - C ∈ PSH(𝒳, θ)` by
`FSSystemC.isPSH_of_sandwich` (`cor:nn-sandwich-diagonal`). -/
theorem isPSH_comp_symm_of_charZero [IsAlgClosed k] [CharZero k] {θ : Fin r → ℝ}
    {ψ : X.normalization.an → EReal} (hψ : X.normalization.IsPSH θ ψ) :
    X.IsPSH θ (ψ ∘ hX.anHomeomorph.symm) := by
  obtain ⟨⟨x₀, hx₀⟩, -, ι, _, _, hne, a, f, hf, ha, hanti, hinf⟩ := hψ
  obtain ⟨i₀⟩ := hne
  have hfi : ∀ i, X.normalization.IsFS (a i) (f i) := hf
  set C : ℝ := (f i₀ X.normalization.triv).toReal with hCdef
  have hC : (C : EReal) = f i₀ X.normalization.triv :=
    EReal.coe_toReal ((hfi i₀).ne_top _) (hfi i₀).apply_triv_ne_bot
  have := isDirected_subtype_le i₀
  have : Nonempty {i // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  have hfC : ∀ i : {i // i₀ ≤ i}, f i X.normalization.triv ≤ C := fun i => by
    rw [hC]
    exact hanti _ i.2
  set u : {i // i₀ ≤ i} → X.an → EReal := fun i v =>
    f i (hX.anHomeomorph.symm v) + ((-C : ℝ) : EReal) with hudef
  set w' : X.an → EReal := fun v => ψ (hX.anHomeomorph.symm v) + ((-C : ℝ) : EReal) with hw'def
  have hw' : X.IsPSH θ w' := by
    refine X.fsSystem.isPSH_of_sandwich (ι := {i // i₀ ≤ i}) (u := u) ?_ ?_
      (θs := fun i c => (a i c : ℝ)) (ha.comp (tendsto_subtype_val_atTop i₀)) ?_ ?_ ?_
    · intro v i i' hii'
      exact add_le_add (hanti _ hii') le_rfl
    · intro i v
      have := add_le_add (((hfi i).le_apply_triv (hX.anHomeomorph.symm v)).trans (hfC i))
        (le_refl ((-C : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
    · intro v
      simp only [hw'def, hudef]
      rw [hinf, ← iInf_subtype_le_eq_iInf_of_antitone (hanti _) i₀, ereal_iInf_add_coe]
    · refine ⟨hX.anHomeomorph x₀, ?_⟩
      simp only [hw'def, Homeomorph.symm_apply_apply]
      exact ProjBerk.ereal_add_coe_ne_bot hx₀ _
    · intro i δ hδ0 hδ1 η hη
      obtain ⟨b', G, hdist, hG, hbd⟩ := hX.exists_isFS_sandwich (hfi i) (hfC i) hδ0 hδ1 hη
      exact ⟨b', G, hdist, hG, fun v => (hbd v).1, fun v => (hbd v).2⟩
  have h := hw'.add_const C
  convert h using 1
  funext v
  simp only [hw'def, Function.comp_apply, ProjBerk.ereal_add_neg_add_coe]

/-- **Psh functions descend through the normalization** (`thm:gl-normalization-reflection`,
`thm:nn-normalization-reflection`; FHX Theorem 8.3): for a unibranch model `𝒳` over an
algebraically closed field `k` of any characteristic, `ψ ∘ (ν^an)⁻¹ ∈ PSH(𝒳, θ)` for every
`ψ ∈ PSH(𝒳^ν, θ)` and every `θ ∈ ℝ^r`. This is the hypothesis `hrefl` of
`MultiModel.IsUnibranch.hasEnvelopeProperty_of_reflection`. -/
theorem isPSH_comp_symm [IsAlgClosed k] {θ : Fin r → ℝ} {ψ : X.normalization.an → EReal}
    (hψ : X.normalization.IsPSH θ ψ) : X.IsPSH θ (ψ ∘ hX.anHomeomorph.symm) := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    exact hX.isPSH_comp_symm_of_charP (ringChar k) hψ
  · have : CharZero k := (CharP.ringChar_zero_iff_CharZero k).1 hp
    exact hX.isPSH_comp_symm_of_charZero hψ

/-- **`PSH(𝒳^ν, θ) = PSH(𝒳, θ) ∘ ν^an`** for a unibranch model over an algebraically closed field,
every `θ ∈ ℝ^r` (`lem:gl-pullback` and `thm:gl-normalization-reflection`). -/
theorem isPSH_comp_iff [IsAlgClosed k] {θ : Fin r → ℝ} (u : X.an → EReal) :
    X.normalization.IsPSH θ (u ∘ hX.anHomeomorph) ↔ X.IsPSH θ u :=
  hX.isPSH_comp_iff_of_reflection (fun _ hψ => hX.isPSH_comp_symm hψ) u

/-- **The envelope property descends from the normalization** (the step `EP_{𝒳^ν}(θ) ⇒ EP_𝒳(θ)`
of `thm:gl-main` and `thm:nn-main`): for a unibranch model `𝒳` over an algebraically closed field
and every `θ ∈ ℝ^r`, `EP_{𝒳^ν}(θ)` implies `EP_𝒳(θ)`. -/
theorem hasEnvelopeProperty_of_normalization [IsAlgClosed k] {θ : Fin r → ℝ}
    (hEP : X.normalization.HasEnvelopeProperty θ) : X.HasEnvelopeProperty θ :=
  hX.hasEnvelopeProperty_of_reflection (fun _ hψ => hX.isPSH_comp_symm hψ) hEP

/-- **`EP_{𝒳^ν}(θ) ⇔ EP_𝒳(θ)`** for a unibranch model over an algebraically closed field and
every `θ ∈ ℝ^r`: `ν^an` identifies the psh classes (`isPSH_comp_iff`). -/
theorem hasEnvelopeProperty_normalization_iff [IsAlgClosed k] {θ : Fin r → ℝ} :
    X.normalization.HasEnvelopeProperty θ ↔ X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_iff_of_isPSH_comp_iff hX.anHomeomorph hX.isPSH_comp_iff

end IsUnibranch

end Unibranch

end MultiModel

end EnvelopeProperty
