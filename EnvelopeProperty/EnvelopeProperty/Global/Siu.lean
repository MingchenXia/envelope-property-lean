/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.HomPSH2
import EnvelopeProperty.Global.Division

/-!
# Homogeneous Siu division for every class

Let `𝒳 = (K, S, z)` be a normal integral multiprojective model of rank `r` over an algebraically
closed trivially valued field `k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file
implements the blueprint node `thm:nn-homogeneous-siu` of the chapter `nonnef.tex` (subsection
`subsec:nn-normal`; the all-classes form of `thm:gl-homogeneous-siu` of `global.tex`, decision
D-NN2) of the formalization of Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX, revision `832e086`, §7, Theorem 7.2, `thm:homogeneous-Siu`, and Remark 7.3,
`rem:BJ-6-21`).

## Main statement

`MultiModel.IsPSHHom.exists_isPSHHom_eq_add_of_le_logSecAbs` (**`thm:nn-homogeneous-siu`**): let
`θ ∈ ℝ^r` (any class), `e ∈ ℚ^r`, `0 ≠ s_E ∈ R_d` with `d = m e`, and `e_E = m⁻¹ log |s_E|`. If
`ψ ∈ PSH_hom(𝒳, θ + e)` and `ψ ≤ e_E`, then `ψ = e_E + φ` with `φ ∈ PSH_hom(𝒳, θ)`.

The envelope property of `𝒳` at positive classes (`thm:gl-normal-ample-ep`, FHX Theorem 6.1) enters
only through its conclusion, as the explicit hypothesis
`hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η`.

## Proof (as in the blueprint)

Choose `N ≥ 1` with `θ + N 𝟙` positive and let `s` be the nonzero monomials `z̃^β` of degree `N 𝟙`,
so that `max_{f ∈ s} log |f| = 0` (`exists_finset_sections_logSecAbs_eq_zero`).

* `IsPSHHom.exists_add_logSecAbs_eq_of_le_logSecAbs`: for `f ∈ s` and rational `0 < ε < 1`, the
  quotients `ψ + log |f| = t_n e_E + q_n` of the division with a fixed coefficient
  (`lem:gl-fixed-coefficient-division`, `MultiModel.IsPSHHom.exists_eq_add_of_le_logSecAbs`),
  `t_n = 1 - δ/(n+1) ↑ 1`, lie in the positive class `P = θ + (1 + ε) N 𝟙`, and their regularized
  supremum `χ_f = (sup_n q_n)^⋆` is `P`-psh by the envelope property at `P`, homogeneous,
  `≤ log |f|`, with `χ_f + e_E = ψ + log |f|` on `𝒳^div`.
* `IsPSHHom.exists_isPSHHom_eq_add_of_isDivisorial`: the division of `χ_f` by `f` with the
  coefficient `1 - ε` gives `q'_f ∈ PSH_hom(𝒳, θ + 2 ε N 𝟙)`, and `φ_ε = max_{f ∈ s} q'_f` satisfies
  `ψ = e_E + φ_ε` on `𝒳^div`.
* By the comparison theorem (`thm:gl-comparison`) the `φ_ε` do not depend on `ε`; PSH2 for
  homogeneous functions at the limit class (`thm:nn-psh2-hom`,
  `MultiModel.isPSHHom_of_tendsto_class`, classes `θ + 2 ε_n N 𝟙 → θ`) gives `φ ∈ PSH_hom(𝒳, θ)`,
  and `ψ = e_E + φ` by comparison. Nothing here depends on BJ22 Theorem 6.21 or Lemma 4.6.

## Deviations from the blueprint

* `N ≥ 1` is required (the blueprint takes `N ∈ ℕ` with `θ + N 𝟙` positive; for `N = 0` no
  `t₀ < 1` with `(1 - t₀) e ≤ ε N 𝟙` exists when `e` has a positive coordinate).
* The quotients are taken along the sequence `t_n = 1 - δ/(n+1)`, `δ = ε / (1 + ∑_c |e_c|)`, so that
  `(1 - t_n) e ≤ ε N 𝟙`, instead of all rational `t ∈ [t₀, 1)`.
* The open sets `Ω = {e_E > -∞}`, `V` are replaced by the divisorial points: the identity
  `χ_f = u + log |f|` (`u = ψ - e_E`) is proved at each `v ∈ 𝒳^div`, the upper bound by upper
  semicontinuity of `ψ + log |f| - e_E` at `v` and `g ≤ ψ + log |f| - e_E` on the neighbourhood
  `{e_E > -∞}` of `v` (`uscReg_le_of_eventually_le`, the pointwise form of `lem:gl-usc-local`(1)),
  the lower bound by `t_n → 1`. Comparisons are made with `thm:gl-comparison` directly.
* The base point free family is the family of nonzero monomials of degree `N 𝟙` (`lem:gl-cones`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Auxiliary facts on `EReal` and usc regularization -/

/-- If `g ≤ W` near `x` and `W` is usc at `x`, then `g^⋆(x) ≤ W(x)`. -/
theorem uscReg_le_of_eventually_le {T : Type*} [TopologicalSpace T] {g W : T → EReal} {x : T}
    (hW : UpperSemicontinuousAt W x) (h : ∀ᶠ y in 𝓝 x, g y ≤ W y) : uscReg g x ≤ W x :=
  (Filter.limsup_le_limsup h).trans hW.limsup_le

/-- Cancelling a real summand: `x + a = y + b` gives `x = y + (b - a)` in `EReal`. -/
theorem ereal_eq_add_coe_sub_of_add_coe_eq {x y : EReal} {a b : ℝ}
    (h : x + (a : EReal) = y + (b : EReal)) : x = y + ((b - a : ℝ) : EReal) := by
  calc x = x + (a : EReal) + ((-a : ℝ) : EReal) := (ProjBerk.ereal_add_coe_add_neg x a).symm
    _ = y + ((b - a : ℝ) : EReal) := by
        rw [h, add_assoc, ← EReal.coe_add, ← sub_eq_add_neg]

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- Finite maxima of homogeneous functions are homogeneous. -/
theorem IsScaleHomogeneous.finset_sup' {κ : Type*} {s : Finset κ} (hs : s.Nonempty)
    {w : κ → X.an → EReal} (hw : ∀ i ∈ s, X.IsScaleHomogeneous (w i)) :
    X.IsScaleHomogeneous fun v => s.sup' hs fun i => w i v := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup'_singleton] using hw a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs]
    exact (hw a (Finset.mem_cons_self a s)).max (ih fun i hi => hw i (Finset.mem_cons_of_mem hi))

/-- `m⁻¹ log |s| ∈ PSH_hom(𝒳, e)` for `0 ≠ s ∈ R_d`, `d = m e`. -/
theorem isPSHHom_inv_mul_logSecAbs {e : Fin r → ℚ} {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * e c) {s : K} (hs : s ∈ X.sections d) (hs0 : s ≠ 0) :
    X.IsPSHHom (fun c => (e c : ℝ)) fun v => (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d s := by
  have hm' : (0 : ℚ) < (m : ℚ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := (isPSH_logSecAbs hs hs0).smul_rat hm'
  refine ⟨?_, fun t ht v => ?_⟩
  · convert h using 1
    · funext c
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hd c]
      push_cast
      field_simp
    · funext v
      push_cast
      rfl
  · simp only [logSecAbs_rpow]
    exact mul_left_comm _ _ _

/-- The monomials `z̃^β`, `β ∈ Mon(N 𝟙)`, give a finite family of nonzero sections of degree
`N 𝟙` with `max_β log |z̃^β| = 0` on `𝒳^an` (`lem:gl-cones`(1),(2)). -/
theorem exists_finset_sections_logSecAbs_eq_zero (N : ℕ) :
    ∃ s : Finset K, (∀ f ∈ s, f ∈ X.sections (fun _ => (N : ℤ)) ∧ f ≠ 0) ∧
      ∀ v : X.an, ∃ f ∈ s, X.logSecAbs v.1 (fun _ => (N : ℤ)) f = 0 := by
  classical
  set dN : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N with hdN
  have hdN' : ∀ c, ((fun _ => (N : ℤ)) c : ℤ) = dN c := fun c => by simp [hdN]
  refine ⟨((X.monSet dN).image X.zCoeff).filter (· ≠ 0), fun f hf => ?_, fun v => ?_⟩
  · obtain ⟨hf, hf0⟩ := Finset.mem_filter.1 hf
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨mem_sections_of_mem_piece hdN' (zCoeff_mem_piece_of_mem_monSet hβ), hf0⟩
  · obtain ⟨β, hβ, h1⟩ := v.2.2.exists_val_zMon_eq_one dN
    have hsec : X.secAbs v.1 (fun _ => (N : ℤ)) (X.zCoeff β) = 1 := by
      rw [secAbs_of_mem_piece v.2.2 hdN' (zCoeff_mem_piece_of_mem_monSet hβ),
        ofPiece_zCoeff_of_mem_monSet hβ, h1]
    have hne : X.zCoeff β ≠ 0 := fun h0 => by
      rw [h0, secAbs_zero] at hsec
      exact zero_ne_one hsec
    refine ⟨X.zCoeff β, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hβ, hne⟩, ?_⟩
    rw [logSecAbs, hsec, ENNReal.coe_one, ENNReal.log_one]

variable [IsAlgClosed k]

/-- **The shifted limit** (first half of the proof of `thm:nn-homogeneous-siu`). Let `𝒳` be
normal with the envelope property at positive classes, `ψ ∈ PSH_hom(𝒳, θ + e)` with
`ψ ≤ e_E = m⁻¹ log |s_E|`, `0 ≠ f ∈ R_{d_A}` and `P` a positive class with
`θ + e + d_A - t e ≤ P` for rational `t ∈ [1 - δ, 1)`. Then there is `χ ∈ PSH_hom(𝒳, P)` with
`χ ≤ log |f|` and `χ + e_E = ψ + log |f|` on `𝒳^div`. It is `χ = (sup_n q_n)^⋆` for the quotients
`ψ + log |f| = t_n e_E + q_n` of `lem:gl-fixed-coefficient-division`, `t_n = 1 - δ/(n+1) ↑ 1`. -/
theorem IsPSHHom.exists_add_logSecAbs_eq_of_le_logSecAbs (hX : X.IsNormal)
    (hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η)
    {θ : Fin r → ℝ} {e : Fin r → ℚ} {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * e c) {sE : K} (hsE : sE ∈ X.sections d) (hsE0 : sE ≠ 0)
    {ψ : X.an → EReal} (hψ : X.IsPSHHom (fun c => θ c + (e c : ℝ)) ψ)
    (hle : ∀ v, ψ v ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE)
    {dA : Fin r → ℤ} {f : K} (hf : f ∈ X.sections dA) (hf0 : f ≠ 0)
    {P : Fin r → ℝ} (hP : ∀ c, 0 < P c) {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hPle : ∀ t : ℚ, 1 - δ ≤ t → t < 1 → ∀ c,
      θ c + (e c : ℝ) + (dA c : ℝ) - (t : ℝ) * (e c : ℝ) ≤ P c) :
    ∃ χ : X.an → EReal, X.IsPSHHom P χ ∧ (∀ v, χ v ≤ X.logSecAbs v.1 dA f) ∧
      ∀ v, X.IsDivisorial v → χ v + (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE =
        ψ v + X.logSecAbs v.1 dA f := by
  classical
  set eE : X.an → EReal := fun v => (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE with heE
  set ef : X.an → EReal := fun v => X.logSecAbs v.1 dA f with hef
  have hmR : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  -- properties of `e_E` and `e_f = log |f|`
  have heEcont : Continuous eE := (ProjBerk.continuous_ereal_coe_mul hmR.ne').comp
    ((X.continuous_logSecAbs d sE).comp continuous_subtype_val)
  have hefcont : Continuous ef := (X.continuous_logSecAbs dA f).comp continuous_subtype_val
  have heE0 : ∀ v, eE v ≤ 0 := fun v =>
    (ProjBerk.ereal_coe_mul_monotone hmR.le (logSecAbs_le_zero v.2.2 d sE)).trans_eq (mul_zero _)
  have hef0 : ∀ v, ef v ≤ 0 := fun v => logSecAbs_le_zero v.2.2 dA f
  have heEtop : ∀ v, eE v ≠ ⊤ := fun v =>
    ProjBerk.ereal_coe_mul_ne_top hmR.le (logSecAbs_ne_top _ _ _)
  have heEbot : ∀ v, X.IsDivisorial v → eE v ≠ ⊥ := fun v hv =>
    ProjBerk.ereal_coe_mul_ne_bot hmR.le (hv.logSecAbs_ne_bot hsE hsE0)
  have hefP : X.IsPSHHom (fun c => ((dA c : ℚ) : ℝ)) ef :=
    ⟨isPSH_logSecAbs hf hf0, fun t ht v => logSecAbs_rpow t ht v dA f⟩
  -- `ψ + e_f ∈ PSH_hom(𝒳, θ + e + d_A)`, `ψ + e_f ≤ e_E`
  have hψf := hψ.add hefP
  have hψfle : ∀ v, ψ v + ef v ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE := fun v =>
    (add_le_add (hle v) (hef0 v)).trans_eq (add_zero _)
  -- the coefficients `t_n = 1 - δ/(n+1)`
  set t : ℕ → ℚ := fun n => 1 - δ / (n + 1) with ht
  have hn1 : ∀ n : ℕ, (1 : ℚ) ≤ n + 1 := fun n => by
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  have hδt : ∀ n : ℕ, δ / ((n : ℚ) + 1) ≤ δ := fun n => div_le_self hδ0.le (hn1 n)
  have hδt0 : ∀ n : ℕ, 0 < δ / ((n : ℚ) + 1) := fun n => div_pos hδ0 (by linarith [hn1 n])
  have ht0 : ∀ n, 0 < t n := fun n => by simp only [ht]; linarith [hδt n]
  have ht1 : ∀ n, t n < 1 := fun n => by simp only [ht]; linarith [hδt0 n]
  have htδ : ∀ n, 1 - δ ≤ t n := fun n => by simp only [ht]; linarith [hδt n]
  -- the quotients `q_n` (`lem:gl-fixed-coefficient-division`)
  have hq := fun n => IsPSHHom.exists_eq_add_of_le_logSecAbs hX hm hd hsE hsE0 hψf hψfle
    (ht0 n) (ht1 n)
  choose q hqP hqeq using hq
  have hqeq' : ∀ n v, ψ v + ef v = (((t n : ℚ) : ℝ) : EReal) * eE v + q n v := hqeq
  have hqP' : ∀ n, X.IsPSHHom P (q n) := fun n => by
    refine ⟨(hqP n).1.mono_class fun c => ?_, (hqP n).2⟩
    have := hPle (t n) (htδ n) (ht1 n) c
    simp only [Pi.add_apply, Rat.cast_intCast]
    linarith
  -- at a point where `e_E` is finite, `q_n = ψ + e_f - t_n e_E`
  have hqval : ∀ n v (E : ℝ), eE v = E →
      q n v = ψ v + ef v + ((-(((t n : ℚ) : ℝ) * E) : ℝ) : EReal) := fun n v E hE => by
    have h := hqeq' n v
    rw [hE, ← EReal.coe_mul, add_comm _ (q n v)] at h
    have := ereal_eq_add_coe_sub_of_add_coe_eq (x := q n v) (y := ψ v + ef v)
      (a := ((t n : ℚ) : ℝ) * E) (b := 0) (by rw [EReal.coe_zero, add_zero]; exact h.symm)
    rw [this, zero_sub]
  -- `q_n ≤ e_f`
  have hqf : ∀ n v, q n v ≤ ef v := fun n => by
    refine (hqP' n).1.le_of_forall_isDivisorial_le hefcont.upperSemicontinuous
      (fun v => logSecAbs_ne_top _ _ _) fun v hv => ?_
    obtain ⟨E, hE⟩ : ∃ E : ℝ, eE v = E :=
      ⟨(eE v).toReal, (EReal.coe_toReal (heEtop v) (heEbot v hv)).symm⟩
    have hE0 : E ≤ 0 := by have := heE0 v; rw [hE] at this; exact_mod_cast this
    have hψE : ψ v ≤ E := by rw [← hE]; exact hle v
    have htn0 : (0 : ℝ) < ((t n : ℚ) : ℝ) := by exact_mod_cast ht0 n
    have htn1 : ((t n : ℚ) : ℝ) < 1 := by exact_mod_cast ht1 n
    rw [hqval n v E hE]
    calc ψ v + ef v + ((-(((t n : ℚ) : ℝ) * E) : ℝ) : EReal)
        ≤ (E : EReal) + ef v + ((-(((t n : ℚ) : ℝ) * E) : ℝ) : EReal) :=
          add_le_add (add_le_add hψE le_rfl) le_rfl
      _ = ef v + ((E + -(((t n : ℚ) : ℝ) * E) : ℝ) : EReal) := by
          rw [add_comm (E : EReal), add_assoc, ← EReal.coe_add]
      _ ≤ ef v + ((0 : ℝ) : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by nlinarith))
      _ = ef v := by rw [EReal.coe_zero, add_zero]
  -- `χ = (sup_n q_n)^⋆ ∈ PSH_hom(𝒳, P)`, by the envelope property at `P`
  set χ : X.an → EReal := uscReg fun v => ⨆ n, q n v with hχ
  have hχP : X.IsPSHHom P χ :=
    ⟨FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup (F := X.fsSystem) (hample P hP)
      (fun n => (hqP' n).1) ⟨0, fun n v => by exact_mod_cast (hqf n v).trans (hef0 v)⟩,
      IsScaleHomogeneous.uscReg_iSup fun n => (hqP' n).2⟩
  have hχf : ∀ v, χ v ≤ ef v :=
    uscReg_le_of_le hefcont.upperSemicontinuous fun v => iSup_le fun n => hqf n v
  refine ⟨χ, hχP, hχf, fun v hv => ?_⟩
  change χ v + eE v = ψ v + ef v
  obtain ⟨E, hE⟩ : ∃ E : ℝ, eE v = E :=
    ⟨(eE v).toReal, (EReal.coe_toReal (heEtop v) (heEbot v hv)).symm⟩
  have hE0 : E ≤ 0 := by have := heE0 v; rw [hE] at this; exact_mod_cast this
  rw [hE]
  refine le_antisymm ?_ ?_
  · -- upper bound: `χ ≤ ψ + e_f - e_E` near `v`, by usc of the right side at `v`
    set W : X.an → EReal := fun w => ψ w + ef w + -eE w with hW
    have hWusc : UpperSemicontinuousAt W v := by
      refine UpperSemicontinuousAt.add' (FSSystemC.IsPSH.upperSemicontinuous hψf.1 v)
        ((continuous_neg.comp heEcont).continuousAt.upperSemicontinuousAt) ?_
      refine EReal.continuousAt_add (Or.inr ?_) (Or.inr ?_)
      · simp only [hE, ← EReal.coe_neg]
        exact EReal.coe_ne_bot _
      · simp only [hE, ← EReal.coe_neg]
        exact EReal.coe_ne_top _
    have hΩ : ∀ᶠ w in 𝓝 v, eE w ≠ ⊥ :=
      (isOpen_compl_singleton.preimage heEcont).mem_nhds (heEbot v hv)
    have hloc : ∀ᶠ w in 𝓝 v, (⨆ n, q n w) ≤ W w := by
      filter_upwards [hΩ] with w hw
      obtain ⟨E', hE'⟩ : ∃ E' : ℝ, eE w = E' :=
        ⟨(eE w).toReal, (EReal.coe_toReal (heEtop w) hw).symm⟩
      have hE'0 : E' ≤ 0 := by have := heE0 w; rw [hE'] at this; exact_mod_cast this
      refine iSup_le fun n => ?_
      have htn1 : ((t n : ℚ) : ℝ) < 1 := by exact_mod_cast ht1 n
      have htn0 : (0 : ℝ) < ((t n : ℚ) : ℝ) := by exact_mod_cast ht0 n
      rw [hqval n w E' hE', hW]
      simp only [hE', ← EReal.coe_neg]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by nlinarith))
    have h1 : χ v ≤ W v := uscReg_le_of_eventually_le hWusc hloc
    rw [hW] at h1
    simp only [hE, ← EReal.coe_neg] at h1
    calc χ v + (E : EReal) ≤ ψ v + ef v + ((-E : ℝ) : EReal) + (E : EReal) :=
          add_le_add h1 le_rfl
      _ = ψ v + ef v := ProjBerk.ereal_add_neg_add_coe _ _
  · -- lower bound: `ψ + e_f = t_n e_E + q_n ≤ χ + e_E + (1 - t_n)(-e_E)`, `t_n → 1`
    refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ((δ : ℝ) * (-E) / ε)
    have hn' : (δ : ℝ) * (-E) / ((n : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn
      have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0.le
      nlinarith
    have htR : ((t n : ℚ) : ℝ) = 1 - (δ : ℝ) / ((n : ℝ) + 1) := by simp only [ht]; push_cast; ring
    have hqχ : q n v ≤ χ v :=
      (le_iSup (fun n => q n v) n).trans (le_uscReg (fun w => ⨆ n, q n w) v)
    rw [hqeq' n v, hE, ← EReal.coe_mul]
    calc ((((t n : ℚ) : ℝ) * E : ℝ) : EReal) + q n v
        ≤ ((((t n : ℚ) : ℝ) * E : ℝ) : EReal) + χ v := add_le_add le_rfl hqχ
      _ = χ v + (E : EReal) + (((((t n : ℚ) : ℝ) * E - E) : ℝ) : EReal) := by
          rw [add_comm _ (χ v), add_assoc, ← EReal.coe_add]
          congr 2
          ring
      _ ≤ χ v + (E : EReal) + (ε : EReal) := by
          refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
          rw [htR]
          have : ((1 - (δ : ℝ) / ((n : ℝ) + 1)) * E - E) = (δ : ℝ) * (-E) / ((n : ℝ) + 1) := by
            field_simp
            ring
          rw [this]
          exact hn'

/-- **Division at a shifted class** (second half of the proof of `thm:nn-homogeneous-siu`). In the
setting of `IsPSHHom.exists_add_logSecAbs_eq_of_le_logSecAbs`, let `N ≥ 1` with `θ + N 𝟙` positive,
and let `s` be a finite family of nonzero sections of degree `N 𝟙` with `max_{f ∈ s} log |f| = 0`
(e.g. the monomials, `exists_finset_sections_logSecAbs_eq_zero`). For every rational
`0 < ε < 1` there is `φ ∈ PSH_hom(𝒳, θ + 2 ε N 𝟙)` with `ψ = e_E + φ` on `𝒳^div`: divide the
shifted limits `χ_f ∈ PSH_hom(𝒳, θ + (1 + ε) N 𝟙)` by `f` with the coefficient `1 - ε`
(`lem:gl-fixed-coefficient-division`), `χ_f = (1 - ε) log |f| + q'_f`, and take
`φ = max_{f ∈ s} q'_f`; on `𝒳^div`, `q'_f = ψ - e_E + ε log |f|`. -/
theorem IsPSHHom.exists_isPSHHom_eq_add_of_isDivisorial (hX : X.IsNormal)
    (hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η)
    {θ : Fin r → ℝ} {e : Fin r → ℚ} {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * e c) {sE : K} (hsE : sE ∈ X.sections d) (hsE0 : sE ≠ 0)
    {ψ : X.an → EReal} (hψ : X.IsPSHHom (fun c => θ c + (e c : ℝ)) ψ)
    (hle : ∀ v, ψ v ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE)
    {N : ℕ} (hN1 : 1 ≤ N) (hN : ∀ c, 0 < θ c + N) {s : Finset K}
    (hs : ∀ f ∈ s, f ∈ X.sections (fun _ => (N : ℤ)) ∧ f ≠ 0)
    (hs1 : ∀ v : X.an, ∃ f ∈ s, X.logSecAbs v.1 (fun _ => (N : ℤ)) f = 0)
    {ε : ℚ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ φ : X.an → EReal, X.IsPSHHom (fun c => θ c + 2 * (ε : ℝ) * N) φ ∧
      ∀ v, X.IsDivisorial v → ψ v = (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE + φ v := by
  classical
  set eE : X.an → EReal := fun v => (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE with heE
  set dN : Fin r → ℤ := fun _ => (N : ℤ) with hdN
  set P : Fin r → ℝ := fun c => θ c + (1 + (ε : ℝ)) * N with hPdef
  have hmR : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hεR0 : (0 : ℝ) < ε := by exact_mod_cast hε0
  have hP : ∀ c, 0 < P c := fun c => by
    have := hN c
    simp only [hPdef]
    nlinarith
  -- the parameter `δ = ε / (1 + ∑ |e_c|)`, so that `(1 - t) e ≤ ε N 𝟙` for `t ∈ [1 - δ, 1)`
  set L : ℚ := ∑ c, |e c| with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun c _ => abs_nonneg _
  have heL : ∀ c, |e c| ≤ L := fun c =>
    Finset.single_le_sum (f := fun c => |e c|) (fun c _ => abs_nonneg _) (Finset.mem_univ c)
  set δ : ℚ := ε / (1 + L) with hδ
  have hδ0 : 0 < δ := div_pos hε0 (by linarith)
  have hδε : δ ≤ ε := div_le_self hε0.le (by linarith)
  have hδ1 : δ < 1 := hδε.trans_lt hε1
  have hPle : ∀ t : ℚ, 1 - δ ≤ t → t < 1 → ∀ c,
      θ c + (e c : ℝ) + (dN c : ℝ) - (t : ℝ) * (e c : ℝ) ≤ P c := by
    intro t ht0 ht1 c
    have hq : (1 - t) * e c ≤ ε * N := by
      have h1 : (1 - t) * e c ≤ (1 - t) * |e c| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      have h2 : (1 - t) * |e c| ≤ δ * |e c| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      have h3 : δ * |e c| ≤ δ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith [heL c]) hδ0.le
      have h4 : δ * (1 + L) = ε := by
        rw [hδ]
        field_simp
      have h5 : ε ≤ ε * N := le_mul_of_one_le_right hε0.le (by exact_mod_cast hN1)
      linarith
    have hqR : (1 - (t : ℝ)) * (e c : ℝ) ≤ (ε : ℝ) * N := by exact_mod_cast hq
    simp only [hPdef, hdN, Int.cast_natCast]
    nlinarith
  -- the shifted limits `χ_f`
  have hχ := fun f (hf : f ∈ s) => IsPSHHom.exists_add_logSecAbs_eq_of_le_logSecAbs hX hample hm
    hd hsE hsE0 hψ hle (hs f hf).1 (hs f hf).2 hP hδ0 hδ1 hPle
  choose! χ hχP hχle hχeq using hχ
  -- division of `χ_f` by `f` with the coefficient `1 - ε`
  have hA : ∀ c, ((dN c : ℤ) : ℚ) = ((1 : ℕ) : ℚ) * (N : ℚ) := fun c => by simp [hdN]
  have hε1' : (0 : ℚ) < 1 - ε := by linarith
  have hε2' : 1 - ε < 1 := by linarith
  have hq' := fun f (hf : f ∈ s) => IsPSHHom.exists_eq_add_of_le_logSecAbs
    (e := fun _ => (N : ℚ)) hX one_pos hA (hs f hf).1 (hs f hf).2 (hχP f hf)
    (fun v => by rw [Nat.cast_one, inv_one, EReal.coe_one, one_mul]; exact hχle f hf v) hε1' hε2'
  choose! q' hq'P hq'eq using hq'
  obtain ⟨f₁, hf₁, -⟩ := hs1 X.triv
  have hsne : s.Nonempty := ⟨f₁, hf₁⟩
  refine ⟨fun v => s.sup' hsne fun f => q' f v, ⟨?_, ?_⟩, fun v hv => ?_⟩
  · have := FSSystemC.isPSH_finset_sup' (F := X.fsSystem) hsne fun f hf => (hq'P f hf).1
    convert this using 1
    funext c
    simp only [hPdef]
    push_cast
    ring
  · exact IsScaleHomogeneous.finset_sup' hsne fun f hf => (hq'P f hf).2
  -- the identity on `𝒳^div`
  obtain ⟨E, hE⟩ : ∃ E : ℝ, eE v = E :=
    ⟨(eE v).toReal, (EReal.coe_toReal (ProjBerk.ereal_coe_mul_ne_top hmR.le
      (logSecAbs_ne_top _ _ _)) (ProjBerk.ereal_coe_mul_ne_bot hmR.le
        (hv.logSecAbs_ne_bot hsE hsE0))).symm⟩
  have key : ∀ f ∈ s, ∀ F : ℝ, X.logSecAbs v.1 dN f = F →
      (E : EReal) + q' f v = ψ v + ((ε * F : ℝ) : EReal) := by
    intro f hf F hF
    have h1 := hχeq f hf v hv
    have h2 := hq'eq f hf v
    change χ f v + eE v = ψ v + X.logSecAbs v.1 dN f at h1
    rw [Nat.cast_one, inv_one, EReal.coe_one, one_mul, hF, ← EReal.coe_mul] at h2
    rw [hE, hF, h2, add_comm _ (q' f v), add_assoc, ← EReal.coe_add] at h1
    have h3 := ereal_eq_add_coe_sub_of_add_coe_eq h1
    rw [h3, add_comm, add_assoc, ← EReal.coe_add]
    congr 2
    push_cast
    ring
  have hfin : ∀ f ∈ s, ∃ F : ℝ, X.logSecAbs v.1 dN f = F ∧ F ≤ 0 := fun f hf =>
    ⟨(X.logSecAbs v.1 dN f).toReal, (EReal.coe_toReal (logSecAbs_ne_top _ _ _)
      (hv.logSecAbs_ne_bot (hs f hf).1 (hs f hf).2)).symm,
      EReal.toReal_nonpos (logSecAbs_le_zero v.2.2 dN f)⟩
  change ψ v = eE v + s.sup' hsne fun f => q' f v
  rw [hE]
  refine le_antisymm ?_ ?_
  · obtain ⟨f₀, hf₀, h0⟩ := hs1 v
    have := key f₀ hf₀ 0 (by rw [h0, EReal.coe_zero])
    rw [mul_zero, EReal.coe_zero, add_zero] at this
    rw [← this]
    exact add_le_add le_rfl (Finset.le_sup' (fun f => q' f v) hf₀)
  · have hle' : (s.sup' hsne fun f => q' f v) ≤ ψ v + ((-E : ℝ) : EReal) := by
      refine Finset.sup'_le hsne _ fun f hf => ?_
      obtain ⟨F, hF, hF0⟩ := hfin f hf
      have h1 := key f hf F hF
      have h2 : (E : EReal) + q' f v ≤ ψ v := by
        rw [h1]
        calc ψ v + ((ε * F : ℝ) : EReal) ≤ ψ v + ((0 : ℝ) : EReal) :=
              add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by nlinarith))
          _ = ψ v := by rw [EReal.coe_zero, add_zero]
      calc q' f v = (E : EReal) + q' f v + ((-E : ℝ) : EReal) := by
            rw [add_comm (E : EReal), ProjBerk.ereal_add_coe_add_neg]
        _ ≤ ψ v + ((-E : ℝ) : EReal) := add_le_add h2 le_rfl
    calc (E : EReal) + (s.sup' hsne fun f => q' f v)
        ≤ (E : EReal) + (ψ v + ((-E : ℝ) : EReal)) := add_le_add le_rfl hle'
      _ = ψ v := by rw [add_comm, ProjBerk.ereal_add_neg_add_coe]

/-- **Homogeneous Siu division for every class** (**`thm:nn-homogeneous-siu`**; FHX Theorem 7.2,
`thm:homogeneous-Siu`, for all classes). Let `𝒳` be a normal model over an algebraically closed
field, with the envelope property at every positive class (`hample`; this is
`thm:gl-normal-ample-ep`). Let `θ ∈ ℝ^r`, `e ∈ ℚ^r`, `0 ≠ s_E ∈ R_d` with `d = m e`, and
`e_E = m⁻¹ log |s_E|`. If `ψ ∈ PSH_hom(𝒳, θ + e)` and `ψ ≤ e_E`, then `ψ = e_E + φ` with
`φ ∈ PSH_hom(𝒳, θ)`. -/
theorem IsPSHHom.exists_isPSHHom_eq_add_of_le_logSecAbs (hX : X.IsNormal)
    (hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η)
    {θ : Fin r → ℝ} {e : Fin r → ℚ} {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * e c) {sE : K} (hsE : sE ∈ X.sections d) (hsE0 : sE ≠ 0)
    {ψ : X.an → EReal} (hψ : X.IsPSHHom (fun c => θ c + (e c : ℝ)) ψ)
    (hle : ∀ v, ψ v ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE) :
    ∃ φ : X.an → EReal, X.IsPSHHom θ φ ∧
      ∀ v, ψ v = (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE + φ v := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  -- `N ≥ 1` with `θ + N 𝟙` positive, and the monomials of degree `N 𝟙`
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (∑ c, |θ c|)
  have hN1 : 1 ≤ N₀ + 1 := Nat.le_add_left 1 N₀
  have hN : ∀ c, 0 < θ c + ((N₀ + 1 : ℕ) : ℝ) := fun c => by
    have h1 : |θ c| ≤ ∑ c, |θ c| :=
      Finset.single_le_sum (f := fun c => |θ c|) (fun c _ => abs_nonneg _) (Finset.mem_univ c)
    have h2 := neg_abs_le (θ c)
    push_cast
    linarith
  obtain ⟨s, hs, hs1⟩ := X.exists_finset_sections_logSecAbs_eq_zero (N₀ + 1)
  have hφ := fun (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) =>
    IsPSHHom.exists_isPSHHom_eq_add_of_isDivisorial hX hample hm hd hsE hsE0 hψ hle hN1 hN hs hs1
      h0 h1
  obtain ⟨φ, hφP, hφeq⟩ := hφ (1 / 2) (by norm_num) (by norm_num)
  -- by comparison, `φ ∈ PSH_hom(𝒳, θ + 2 ε N 𝟙)` for every `ε = 1/(2(n+1))`
  set εs : ℕ → ℚ := fun n => 1 / 2 * (1 / ((n : ℚ) + 1)) with hεs
  have hall : ∀ n : ℕ,
      X.IsPSHHom (fun c => θ c + 2 * ((εs n : ℚ) : ℝ) * ((N₀ + 1 : ℕ) : ℝ)) φ := by
    intro n
    have hn : (1 : ℚ) ≤ n + 1 := by
      have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      linarith
    have h0 : 0 < εs n := by simp only [hεs]; positivity
    have h1 : εs n < 1 := by
      simp only [hεs]
      have : 1 / ((n : ℚ) + 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact hn
      linarith
    obtain ⟨φ', hφ'P, hφ'eq⟩ := hφ _ h0 h1
    have heq : φ' = φ := hφ'P.1.eq_of_forall_isDivisorial_eq hφP.1 fun v hv => by
      obtain ⟨E, hE⟩ : ∃ E : ℝ, (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE = E :=
        ⟨_, (EReal.coe_toReal (ProjBerk.ereal_coe_mul_ne_top hmR.le (logSecAbs_ne_top _ _ _))
          (ProjBerk.ereal_coe_mul_ne_bot hmR.le (hv.logSecAbs_ne_bot hsE hsE0))).symm⟩
      have h := (hφ'eq v hv).symm.trans (hφeq v hv)
      rw [hE] at h
      exact le_antisymm (ereal_le_of_coe_add_le_coe_add h.le)
        (ereal_le_of_coe_add_le_coe_add h.ge)
    rw [← heq]
    exact hφ'P
  have hlim : Tendsto (fun n : ℕ => fun c => θ c + 2 * ((εs n : ℚ) : ℝ) * ((N₀ + 1 : ℕ) : ℝ))
      atTop (𝓝 θ) := by
    refine tendsto_pi_nhds.2 fun c => ?_
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (h0.const_mul ((N₀ + 1 : ℕ) : ℝ)).const_add (θ c)
    rw [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    simp only [hεs]
    push_cast
    ring
  have hφθ : X.IsPSHHom θ φ := isPSHHom_of_tendsto_class hlim hall
  refine ⟨φ, hφθ, fun v => ?_⟩
  -- `e_E + φ` and `ψ` are psh and agree on `𝒳^div`
  have hsum := (isPSHHom_inv_mul_logSecAbs hm hd hsE hsE0).1.add hφθ.1
  have := hψ.1.eq_of_forall_isDivisorial_eq hsum fun v hv => hφeq v hv
  exact congrFun this v

end MultiModel

end EnvelopeProperty
