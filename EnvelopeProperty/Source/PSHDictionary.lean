/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Source.PSH

/-! # Psh functions through a Fubini–Study dictionary

Let `p : X ⟶ Spec k` be projective with `X` integral, `F` a Fubini–Study system
(`FSSystemC`, `def:gl-fs-system`) on a space `B`, `e : X^an ≃ₜ B` a homeomorphism and
`L_1, …, L_s` invertible sheaves with coefficient map `π(a) = ∑_c a_c [L_c]`
(`NativeRealNumericalClasses.lineFamilyMap`) and a coordinate vector `w` with `π(w)` ample.
This file proves that BJ22's psh functions on `X^an` (`Variety.IsPSH`, BJ22 Definition 4.1,
`bj22-trivval:defi:psh`) of class `π(θm)` are, through `e`, the `θm`-psh functions of `F`, as
soon as the Fubini–Study functions of `F` and the native ones correspond in the following
sense (`lem:var-psh-comparison-dictionary`):

(A) every `F`-Fubini–Study function `ψ` of class `a ∈ ℚ^s` is `ψ ∘ e = φ_D` for a nonzero native
  Fubini–Study datum `D` (`NativeNumericalFubiniStudy.FSData`) of class `π(a)`;
(B) if `D` is a nonzero native datum and `π(a) - [D]` is ample, then `φ_D ∘ e⁻¹` is an
  `F`-Fubini–Study function of class `a`.

For the model of a presentation, (A) is the FS dictionary and (B) is finite class promotion
(FHX Lemma 2.6); see
`EnvelopeProperty.Source.PSHComparison`.

## Main results

* `Variety.isPSH_iff_of_fsDictionary`: `φ ∈ PSH(X, π(θm)) ↔ φ ∘ e⁻¹ ∈ PSH_F(θm)`;
* `Variety.hasEnvelopeProperty_iff_of_fsDictionary`: `EP_X(π(θm)) ↔ EP_F(θm)`.

## Proof

* (⇐) An `F`-net `(a_i, f_i)` gives native data `D_i` of classes `π(a_i)` by (A); since
  `a_i → θm`, `π(a_i) → π(θm)` in the order of the ample cone
  (`Variety.ampleTendsto_lineFamilyMap`).
* (⇒) (BJ22 Lemma 4.4, `bj22-trivval:lem:PSH`, a diagonal re-indexing.) Let `D_j` be a
  decreasing net of native data with classes `c_j → θ = π(θm)`. Put `ε_N = 1/(N+1)` and
  `η_N = ε_N π(w)`. Choose `j_N` with `θ + η_N - c_j` ample for `j ≥ j_N`
  (`Variety.AmpleTendsto.eventually_sub_mem`), a radius `ρ_N` of `η_N` along `π`
  (`NativeRealNumericalClasses.exists_ampleCone_lineFamily_radius`), and `b_N ∈ ℚ^s` within
  `min(ρ_N, ε_N)` of `θm + 2 ε_N w`. Then
  `π(b_N) - c_j = (η_N + π(b_N - θm - 2ε_N w)) + (θ + η_N - c_j)` is ample for `j ≥ j_N`, and
  `b_N → θm`. On the directed set `J' = {(j, N) | j_N ≤ j} ⊆ J × ℕ` the functions
  `φ_{D_j} ∘ e⁻¹` are `F`-Fubini–Study functions of class `b_N` by (B), decrease, and have the
  same infimum as the original net (the projection `J' → J` is cofinal); and `b_N → θm` along
  `J'`.
-/

open AlgebraicGeometry CategoryTheory Filter Topology
open Scheme.Modules
open scoped NNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses NativeNumericalFubiniStudy

/-! ### Auxiliary facts -/

/-- Every real number has rational approximations. -/
private theorem exists_rat_abs_sub_lt (x δ : ℝ) (hδ : 0 < δ) : ∃ t : ℚ, |(t : ℝ) - x| < δ := by
  obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn (show x - δ < x + δ by linarith)
  exact ⟨t, abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The index set `{(j, N) | j_N ≤ j} ⊆ J × ℕ` of the re-indexed net in the proof of
`isPSH_iff_of_fsDictionary`, with the product order. -/
private abbrev CofinalIndex {J : Type u} [Preorder J] (jN : ℕ → J) : Type u :=
  {x : J × ℕ // jN x.2 ≤ x.1}

private instance cofinalIndex_nonempty {J : Type u} [Preorder J] (jN : ℕ → J) :
    Nonempty (CofinalIndex jN) :=
  ⟨⟨(jN 0, 0), le_rfl⟩⟩

private instance cofinalIndex_isDirected {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (jN : ℕ → J) : IsDirected (CofinalIndex jN) (· ≤ ·) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨j₁, hx₁, hy₁⟩ := exists_ge_ge x.1.1 y.1.1
  obtain ⟨j₂, h₁₂, hN₂⟩ := exists_ge_ge j₁ (jN (max x.1.2 y.1.2))
  exact ⟨⟨(j₂, max x.1.2 y.1.2), hN₂⟩,
    Subtype.coe_le_coe.mp (Prod.le_def.mpr ⟨hx₁.trans h₁₂, le_max_left _ _⟩),
    Subtype.coe_le_coe.mp (Prod.le_def.mpr ⟨hy₁.trans h₁₂, le_max_right _ _⟩)⟩

private theorem cofinalIndex_le_fst {J : Type u} [Preorder J] {jN : ℕ → J}
    {x y : CofinalIndex jN} (h : x ≤ y) : x.1.1 ≤ y.1.1 :=
  (Prod.le_def.mp (Subtype.coe_le_coe.mpr h)).1

private theorem cofinalIndex_le_snd {J : Type u} [Preorder J] {jN : ℕ → J}
    {x y : CofinalIndex jN} (h : x ≤ y) : x.1.2 ≤ y.1.2 :=
  (Prod.le_def.mp (Subtype.coe_le_coe.mpr h)).2

/-- The second projection `J' → ℕ` tends to infinity. -/
private theorem tendsto_cofinalIndex_snd {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (jN : ℕ → J) : Tendsto (fun x : CofinalIndex jN => x.1.2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun N =>
    ⟨⟨(jN N, N), le_rfl⟩, fun _ hx => cofinalIndex_le_snd hx⟩

private local instance pshComparisonProper {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### The abstract comparison -/

section Dictionary

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k))
  [IsProjective p]

/-- **Psh functions through a Fubini–Study dictionary** (`lem:var-psh-comparison-dictionary`).
Let `F` be a Fubini–Study system on a space `B`, `e : X^an ≃ₜ B`, `L` a finite family of lines
with coefficient map `π = lineFamilyMap p L hL` and a coordinate vector `w` with `π(w)` ample.
Assume (A) every `F`-Fubini–Study function `ψ` of class `a` is, through `e`, the function of a
nonzero native Fubini–Study datum of class `π(a)`, and (B) the function of a nonzero native datum
`D` with `π(a) - [D]` ample is, through `e`, an `F`-Fubini–Study function of class `a`. Then
`φ ∈ PSH(X, π(θm))` iff `φ ∘ e⁻¹` is `θm`-psh for `F`. -/
theorem isPSH_iff_of_fsDictionary {B : Type u} [TopologicalSpace B] {s : ℕ}
    (F : FSSystemC B s) (e : An p ≃ₜ B) (L : Fin s → X.Modules) (hL : ∀ c, IsInvertible (L c))
    (w : Fin s → ℝ) (hw : lineFamilyMap p L hL w ∈ ampleCone p)
    (hA : ∀ (a : Fin s → ℚ) (ψ : B → EReal), F.IsFS a ψ →
      ∃ D : NativeNumericalFubiniStudy.FSData X, D.Nonzero ∧
        D.numericalClass p = lineFamilyMap p L hL (fun c => (a c : ℝ)) ∧
          ∀ y, ψ (e y) = D.eval p y)
    (hB : ∀ (a : Fin s → ℚ) (D : NativeNumericalFubiniStudy.FSData X), D.Nonzero →
      lineFamilyMap p L hL (fun c => (a c : ℝ)) - D.numericalClass p ∈ ampleCone p →
        F.IsFS a fun v => D.eval p (e.symm v))
    (θm : Fin s → ℝ) (φ : An p → EReal) :
    IsPSH p (lineFamilyMap p L hL θm) φ ↔ F.IsPSH θm (φ ∘ e.symm) := by
  constructor
  · rintro ⟨⟨y₀, hy₀⟩, -, J, _, _, _, D, hD, hconv, hanti, he⟩
    -- the ample directions `η_N = ε_N π(w)`
    obtain ⟨ε, hεpos, hεlim⟩ : ∃ ε : ℕ → ℝ, (∀ N, 0 < ε N) ∧ Tendsto ε atTop (𝓝 0) :=
      ⟨fun N => 1 / ((N : ℝ) + 1), fun N => show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity,
        tendsto_one_div_add_atTop_nhds_zero_nat⟩
    have hη (N : ℕ) : ε N • lineFamilyMap p L hL w ∈ ampleCone p :=
      (ampleCone p).smul_mem (hεpos N) hw
    -- `θ + η_N - c_j` is ample for `j ≥ j_N`
    choose jN hjN using fun N => eventually_atTop.mp (hconv.eventually_sub_mem (hη N))
    -- perturbation radii of `η_N` along `π`
    choose ρ hρ hball using fun N => exists_ampleCone_lineFamily_radius p L hL _ (hη N)
    -- rational classes `b_N` close to `θm + 2 ε_N w`
    choose b hb using fun N c =>
      exists_rat_abs_sub_lt ((θm + (2 * ε N) • w) c) (min (ρ N) (ε N)) (lt_min (hρ N) (hεpos N))
    have hdom (N : ℕ) (j : J) (hj : jN N ≤ j) :
        lineFamilyMap p L hL (fun c => (b N c : ℝ)) - (D j).numericalClass p ∈ ampleCone p := by
      have h₁ := hball N ((fun c => (b N c : ℝ)) - (θm + (2 * ε N) • w))
        fun c => (hb N c).trans_le (min_le_left _ _)
      have h₂ : lineFamilyMap p L hL θm + ε N • lineFamilyMap p L hL w -
          (D j).numericalClass p ∈ ampleCone p := hjN N j hj
      have key : lineFamilyMap p L hL (fun c => (b N c : ℝ)) - (D j).numericalClass p =
          (ε N • lineFamilyMap p L hL w +
              lineFamilyMap p L hL ((fun c => (b N c : ℝ)) - (θm + (2 * ε N) • w))) +
            (lineFamilyMap p L hL θm + ε N • lineFamilyMap p L hL w -
              (D j).numericalClass p) := by
        rw [map_sub, map_add, _root_.map_smul]
        module
      rw [key]
      exact (ampleCone p).add_mem h₁ h₂
    have hbconv : Tendsto (fun N c => (b N c : ℝ)) atTop (𝓝 θm) := by
      rw [tendsto_pi_nhds]
      intro c
      have hbound (N : ℕ) : dist (b N c : ℝ) (θm c) ≤ (1 + 2 * |w c|) * ε N := by
        have h : |(b N c : ℝ) - (θm c + 2 * ε N * w c)| < ε N :=
          (hb N c).trans_le (min_le_right _ _)
        have h2 : |2 * ε N * w c| = 2 * ε N * |w c| := by
          rw [abs_mul, abs_of_pos (mul_pos two_pos (hεpos N))]
        rw [Real.dist_eq]
        calc |(b N c : ℝ) - θm c|
            = |((b N c : ℝ) - (θm c + 2 * ε N * w c)) + 2 * ε N * w c| := by
              congr 1
              ring
          _ ≤ |(b N c : ℝ) - (θm c + 2 * ε N * w c)| + |2 * ε N * w c| := abs_add_le _ _
          _ ≤ ε N + 2 * ε N * |w c| := by
              rw [h2]
              linarith
          _ = (1 + 2 * |w c|) * ε N := by ring
      have hlim : Tendsto (fun N => (1 + 2 * |w c|) * ε N) atTop (𝓝 0) := by
        simpa only [mul_zero] using hεlim.const_mul (1 + 2 * |w c|)
      exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun N => dist_nonneg) hbound hlim)
    -- the re-indexed net on `J' = {(j, N) | j_N ≤ j}`
    refine FSSystemC.isPSH_of_iInf (F := F) (ι := CofinalIndex jN)
      ⟨e y₀, by rw [Function.comp_apply, Homeomorph.symm_apply_apply]; exact hy₀⟩
      (fun x => b x.1.2) (fun x v => (D x.1.1).eval p (e.symm v))
      (fun x => hB (b x.1.2) (D x.1.1) (hD _) (hdom x.1.2 x.1.1 x.2))
      (hbconv.comp (tendsto_cofinalIndex_snd jN)) ?_ ?_
    · intro v x x' hxx'
      exact hanti (e.symm v) (cofinalIndex_le_fst hxx')
    · intro v
      change φ (e.symm v) = ⨅ x : CofinalIndex jN, (D x.1.1).eval p (e.symm v)
      rw [he (e.symm v)]
      refine le_antisymm (le_iInf fun x => iInf_le _ x.1.1) (le_iInf fun j => ?_)
      obtain ⟨j', hj, hj'⟩ := exists_ge_ge j (jN 0)
      exact iInf_le_of_le (⟨(j', 0), hj'⟩ : CofinalIndex jN) (hanti (e.symm v) hj)
  · rintro ⟨⟨v₀, hv₀⟩, husc, ι, _, _, _, a, f, hf, ha, hanti, hu⟩
    choose D hD hcl heval using fun i => hA (a i) (f i) (hf i)
    refine ⟨⟨e.symm v₀, hv₀⟩, ?_, ι, inferInstance, inferInstance, inferInstance, D, hD, ?_,
      ?_, ?_⟩
    · have hφ : φ = (φ ∘ e.symm) ∘ e := funext fun y => by
        simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
      rw [hφ]
      exact husc.comp e.continuous
    · exact (ampleTendsto_lineFamilyMap p L hL ha).congr'
        (Eventually.of_forall fun i => (hcl i).symm)
    · intro y i j hij
      have h₁ : f j (e y) ≤ f i (e y) := hanti (e y) hij
      rw [heval i y, heval j y] at h₁
      exact h₁
    · intro y
      have h₁ : φ y = ⨅ i, f i (e y) := by
        have := hu (e y)
        rwa [Function.comp_apply, Homeomorph.symm_apply_apply] at this
      rw [h₁]
      exact iInf_congr fun i => heval i y

/-- **The envelope property through a Fubini–Study dictionary**: under the hypotheses of
`isPSH_iff_of_fsDictionary`, `EP_X(π(θm)) ↔ EP_F(θm)`. -/
theorem hasEnvelopeProperty_iff_of_fsDictionary {B : Type u} [TopologicalSpace B] {s : ℕ}
    (F : FSSystemC B s) (e : An p ≃ₜ B) (L : Fin s → X.Modules) (hL : ∀ c, IsInvertible (L c))
    (w : Fin s → ℝ) (hw : lineFamilyMap p L hL w ∈ ampleCone p)
    (hA : ∀ (a : Fin s → ℚ) (ψ : B → EReal), F.IsFS a ψ →
      ∃ D : NativeNumericalFubiniStudy.FSData X, D.Nonzero ∧
        D.numericalClass p = lineFamilyMap p L hL (fun c => (a c : ℝ)) ∧
          ∀ y, ψ (e y) = D.eval p y)
    (hB : ∀ (a : Fin s → ℚ) (D : NativeNumericalFubiniStudy.FSData X), D.Nonzero →
      lineFamilyMap p L hL (fun c => (a c : ℝ)) - D.numericalClass p ∈ ampleCone p →
        F.IsFS a fun v => D.eval p (e.symm v))
    (θm : Fin s → ℝ) :
    HasEnvelopeProperty p (lineFamilyMap p L hL θm) ↔ F.HasEnvelopeProperty θm :=
  (hasEnvelopeProperty_iff_fsSystem p F θm e.symm fun u =>
    (isPSH_iff_of_fsDictionary p F e L hL w hw hA hB θm u).symm).symm

end Dictionary

end EnvelopeProperty.Variety
