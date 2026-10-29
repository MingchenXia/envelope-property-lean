/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NormalAmple
import EnvelopeProperty.Global.NormalEP
import EnvelopeProperty.Global.NormalizationDescent
import EnvelopeProperty.Local.NonflatNorm

/-!
# The main theorem of Fang–Han–Xia for every class (FHX Theorem A)

This file proves Theorem A (`thm:intro-main`) of Fang–Han–Xia, *The envelope property for
unibranch projective varieties* (FHX) on multiprojective models: *let `X` be an integral unibranch
projective variety over an algebraically closed trivially valued field `k` and `θ ∈ N¹(X)_ℝ`; then
every nonempty bounded-above family `(φ_i) ⊆ PSH(X, θ)` satisfies `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`*.
The variety is an integral multiprojective model `𝒳 = (K, S, z)` of rank `r`
(`EnvelopeProperty.MultiModel`, `def:gl-model`), the classes are all `θ ∈ ℝ^r`
(`rmk:gl-model-comparison`), and unibranchness is `MultiModel.IsUnibranch` (`def:gl-unibranch`:
the normalization is injective on the maximal spectra of all charts; equivalently all local rings
of the charts are geometrically unibranch, `MultiModel.isUnibranch_tfae`). Blueprint: `thm:nn-main`
(`nonnef.tex`), the all-classes form of `thm:gl-main` (`global.tex`).

The theorems `…_of_forall_countable` of this file assume three inputs, `LocalPositivity`,
`BlowupFibreConstancy` and `SmoothEnvelopeCharZero`, at the countable algebraically closed fields
`k₀` with an algebra map `k₀ → k` (see *Hypotheses* below). All three hold over every
algebraically closed field; `EnvelopeProperty/MainTheorem.lean` supplies them and states the
theorems without hypotheses.

## Main results

* `ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield`
  (`prop:gl-ample-countable`, FHX Theorem 6.1, Step 1, over the countable algebraically closed
  subfields of `k`): under the three inputs at a countable algebraically closed field `k₀` with
  `k₀ → k`, every projectively normal `X₀ ⊆ ℙᴹ_{k₀}` has `EP_{X₀}(1)`.
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos_of_forall_subfield`
  (`thm:gl-normal-ample-ep`, FHX Theorem 6.1, Steps 2 and 3): if `EP_{X₀}(1)` holds for every
  projectively normal `X₀` over every countable algebraically closed subfield `k₀` of `k`, every
  normal model has `EP_𝒳(θ)` at every positive `θ`.
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_subfield` (`cor:nn-normal-ep` composed with
  the previous item; FHX Corollary 7.6, `cor:normal-EP`) and
  `MultiModel.IsUnibranch.hasEnvelopeProperty_of_forall_subfield` (the proof of `thm:nn-main` from
  the conclusion of Step 1): `EP_𝒳(θ)` for **every** `θ ∈ ℝ^r`, on normal, resp. unibranch, models.
* **`thm:nn-main`**: `MultiModel.hasEnvelopeProperty_of_isUnibranch_of_forall_countable` (`EP_𝒳(θ)` for every
  `θ ∈ ℝ^r` on a unibranch model) and `MultiModel.isPSH_uscReg_iSup_of_isUnibranch_of_forall_countable` (the statement
  of FHX for indexed families: `(sup_i φ_i)^⋆ ∈ PSH(𝒳, θ)`).
* `MultiModel.hasEnvelopeProperty_of_isUnibranch_of_charP`: in characteristic `p > 0` the
  characteristic-`0` input is not needed.
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_countable`: the normal case (FHX
  Corollary 7.6 at every class) under the same hypotheses.

## Hypotheses

The theorems `…_of_forall_countable` carry exactly the following hypotheses, each quantified over
the countable algebraically closed fields `k₀ : Type u` with an algebra map `k₀ → k` (the
subfields `↥k₀ ⊆ k` instantiate them), all explicit `Prop`-valued hypotheses, **not** axioms:

* `hLP : LocalPositivity k₀` (FHX Lemma 5.5, `lem:local-PL-positivity`, `lem:wu-local-positivity`;
  it gives `WuRegularization` = FHX Lemma 5.11(5),(6) and FHX Proposition 5.22 for
  chart-regularizable functions, `ChartNonflatNorms`, by the instances
  `LocalPositivity.toConvexPLApproximation`, `ConvexPLApproximation.toWuRegularization`,
  `ChartNonflatNorms.of_wuRegularization`);
* `hFC : BlowupFibreConstancy k₀` (FHX Theorem 6.1, Step 1, Gubler–Rabinoff fibre constancy,
  `thm:gl-fibre-constancy`);
* `h₀ : SmoothEnvelopeCharZero k₀` for `k₀` of characteristic `0` (FHX Theorem 3.1 =
  BJ22 Theorem 5.20 in characteristic `0`, `thm:import-sg-ep-char0`); it holds vacuously in
  characteristic `p` (`hasEnvelopeProperty_of_isUnibranch_of_charP`).

De Jong's alterations enter through the scheme-theoretic alteration theorem and its model-form
bridge.

Nothing else is assumed: Theorem 3.1 in characteristic `p`, Corollary 5.26, finite descent, Siu
division, homogeneous PSH2 at every class (`nonnef.tex`), Frobenius descent (Stacks 0CNF) and
additive powers (FHX Lemma 8.2) are theorems. BJ22 Theorems 5.6 and 6.21, Lemma 4.6,
Corollaries 4.17 and 12.18, test configurations and the energy theory are not used.

## Deviations from the blueprint

* The hypotheses are quantified over the countable algebraically closed fields `k₀` **with an
  algebra map `k₀ → k`** (subfields of `k`), not over all countable algebraically closed fields of
  the universe as in `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos_of_forall_countable`.
  This is a weaker hypothesis (the form over all countable fields instantiates it), and it makes
  the characteristic-`0` input vacuous in characteristic `p`. To this end the rank-one step and
  Step 3 of `thm:gl-normal-ample-ep` are re-proved here with the subfield form
  (`ProjSubvariety.hasEnvelopeProperty_one_of_countable` already takes it); the proofs are those of
  `MultiModel.hasEnvelopeProperty_one_of_isNormal_of_forall_countable` and
  `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos`.
* `thm:nn-main` lists the hypotheses of `thm:gl-frobenius-descent` and `thm:gl-additive-powers`;
  both are theorems, so they do not appear.
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Step 1 over the countable subfields (`prop:gl-ample-countable`) -/

namespace ProjSubvariety

variable {k : Type u} [Field k]

/-- **Ample envelopes over countable subfields** (`prop:gl-ample-countable`; FHX Theorem 6.1,
`thm:normal-ample-EP`, Step 1): let `k₀` be a countable algebraically closed field with an algebra
map `k₀ → k`. Under the inputs `LocalPositivity k₀` (FHX Lemma 5.5),
`BlowupFibreConstancy k₀` and, in characteristic `0`, `SmoothEnvelopeCharZero k₀`, every
projectively normal `X₀ = V(I) ⊆ ℙᴹ_{k₀}` has `EP_{X₀}(1)`. FHX Proposition 5.22 for
chart-regularizable functions (`ChartNonflatNorms k₀`) is found by instance search from
`LocalPositivity k₀` (`ChartNonflatNorms.of_wuRegularization`). -/
theorem hasEnvelopeProperty_one_of_isProjNormal_of_subfield
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
    (X₀ : ProjSubvariety k₀ M) (hX₀ : X₀.IsProjNormal) : X₀.HasEnvelopeProperty 1 := by
  have := hLP k₀
  have := hFC k₀
  exact X₀.hasEnvelopeProperty_one_of_isProjNormal_of_countable (h₀ k₀) hX₀

end ProjSubvariety

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

section NormalAmple

variable [IsAlgClosed k]

/-! ### Steps 2 and 3 with the subfield form of the hypothesis (`thm:gl-normal-ample-ep`) -/

/-- **The envelope property of `O(1)` on normal models of rank one**, from Step 1 over the
countable algebraically closed subfields of `k` (`hEP1`). The proof of
`MultiModel.hasEnvelopeProperty_one_of_isNormal_of_forall_countable`, with the subfield form of
`prop:gl-ample-rational` (`ProjSubvariety.hasEnvelopeProperty_one_of_countable`). -/
theorem hasEnvelopeProperty_one_of_isNormal_of_forall_subfield
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {Y : MultiModel k K 1} (hY : Y.IsNormal) : Y.HasEnvelopeProperty fun _ => 1 := by
  obtain ⟨e, he, N, ⟨P⟩⟩ := Y.exists_degOnePres_veronese
  have he' : (0 : ℝ) < e := by
    have := he 0
    rw [Finsupp.single_eq_same] at this
    exact_mod_cast this
  have hV : P.toProjSubvariety.IsProjNormal :=
    P.isProjNormal_toProjSubvariety_iff.2 (Y.isNormal_veronese (ha := he) hY)
  have hEP : P.toProjSubvariety.HasEnvelopeProperty 1 :=
    P.toProjSubvariety.hasEnvelopeProperty_one_of_countable hV
      fun k₀ _ _ _ _ X₀ hX₀ => hEP1 k₀ X₀ hX₀
  have h1 := (P.hasEnvelopeProperty_toProjSubvariety_iff hV zero_le_one).1 hEP
  have h2 := (Y.hasEnvelopeProperty_veronese_iff he).1 h1
  refine (hasEnvelopeProperty_smul_iff (Y.mem_nefCone_of_nonneg fun _ => zero_le_one) he').1 ?_
  convert h2 using 2 with c
  obtain rfl := Fin.fin_one_eq_zero c
  simp

/-- **Ample classes on normal models** (`thm:gl-normal-ample-ep`; FHX Theorem 6.1, Steps 2 and 3,
for the positive classes `θ ∈ ℝ^r`), from Step 1 over the countable algebraically closed subfields
of `k` (`hEP1`). The proof of `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos`: reduce to
positive `a ∈ ℕ^r` by `lem:gl-ep-basic`(1),(2) and pass to the normal Segre–Veronese model
`𝒳_(a)` of rank `1` (`lem:gl-veronese`). -/
theorem hasEnvelopeProperty_of_isNormal_of_pos_of_forall_subfield
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {X : MultiModel k K r} (hX : X.IsNormal) {θ : Fin r → ℝ} (hθ : ∀ c, 0 < θ c) :
    X.HasEnvelopeProperty θ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact X.hasEnvelopeProperty_of_rank_zero θ
  have : NeZero r := ⟨hr.ne'⟩
  refine hasEnvelopeProperty_of_forall_rat_gt (X.mem_nefCone_of_nonneg fun c => (hθ c).le)
    fun q hq => ?_
  have hqpos : ∀ c, (0 : ℚ) < q c := fun c => by
    have h : (0 : ℝ) < q c := (hθ c).trans (hq c)
    exact_mod_cast h
  have hq0 : 0 ≤ q := fun c => (hqpos c).le
  obtain ⟨m, hm, d, hd⟩ := exists_nat_mul_rat_vec_eq_nat_of_nonneg hq0
  set a : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  have had : ∀ c, a c = d c := fun c => rfl
  have ha : ∀ c, 0 < a c := fun c => by
    have h2 : (0 : ℚ) < d c := by rw [hd c]; exact mul_pos (by exact_mod_cast hm) (hqpos c)
    rw [had c]
    exact_mod_cast h2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hqa : (fun c => (q c : ℝ)) = (m : ℝ)⁻¹ • fun c => (a c : ℝ) := by
    funext c
    have := hd c
    rw [Pi.smul_apply, smul_eq_mul, had c]
    have h' : ((d c : ℚ) : ℝ) = (m : ℝ) * (q c : ℝ) := by exact_mod_cast this
    rw [show ((d c : ℕ) : ℝ) = ((d c : ℚ) : ℝ) by norm_cast, h', ← mul_assoc,
      inv_mul_cancel₀ hm'.ne', one_mul]
  rw [hqa, hasEnvelopeProperty_smul_iff (X.mem_nefCone_of_nonneg fun c => by positivity)
    (inv_pos.2 hm')]
  have h1 := hasEnvelopeProperty_one_of_isNormal_of_forall_subfield hEP1
    (X.isNormal_veronese (ha := ha) hX)
  have h2 := (X.hasEnvelopeProperty_veronese_iff ha).1 h1
  simpa using h2

/-! ### Every class (`cor:nn-normal-ep`, `thm:nn-main`) from the conclusion of Step 1 -/

/-- **The envelope property at every class on normal models** (`cor:nn-normal-ep` composed with
`thm:gl-normal-ample-ep`; FHX Corollary 7.6 with Theorem 6.1), from Step 1 over the countable
algebraically closed subfields of `k` (`hEP1`): `EP_𝒳(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isNormal_of_forall_subfield
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {X : MultiModel k K r} (hX : X.IsNormal) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_forall_pos hX
    (fun _ hη => hasEnvelopeProperty_of_isNormal_of_pos_of_forall_subfield hEP1 hX hη) θ

/-- **The main theorem from the conclusion of Step 1** (the proof of `thm:nn-main`): let `𝒳` be a
unibranch model over an algebraically closed field `k`. If `EP_{X₀}(1)` holds for every
projectively normal `X₀ ⊆ ℙᴹ_{k₀}` over every countable algebraically closed subfield `k₀` of `k`
(`hEP1`, the conclusion of `prop:gl-ample-countable`), then `EP_𝒳(θ)` for every `θ ∈ ℝ^r`: the
normalization `𝒳^ν` is normal, so `EP_{𝒳^ν}(θ)`
(`hasEnvelopeProperty_of_isNormal_of_forall_subfield`), and `EP` descends along the
homeomorphism `ν^an` (`IsUnibranch.hasEnvelopeProperty_of_normalization`, FHX Theorem 8.3). -/
theorem IsUnibranch.hasEnvelopeProperty_of_forall_subfield
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hX.hasEnvelopeProperty_of_normalization
    (hasEnvelopeProperty_of_isNormal_of_forall_subfield hEP1 X.isNormal_normalization θ)

/-! ### The main theorem under the three inputs (`thm:nn-main`) -/

/-- **FHX Corollary 7.6 at every class** (`cor:normal-EP`), under the three inputs at the
countable subfields: a normal model over an algebraically closed field `k` has `EP_𝒳(θ)` for every `θ ∈ ℝ^r`, under `LocalPositivity`,
`BlowupFibreConstancy` and (characteristic `0`) `SmoothEnvelopeCharZero` at the countable
algebraically closed subfields of `k`. -/
theorem hasEnvelopeProperty_of_isNormal_of_forall_countable
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsNormal) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_forall_subfield
    (ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield hLP hFC h₀) hX θ

/-- **The main theorem** (**`thm:nn-main`**, the all-classes form of `thm:gl-main`; FHX
Theorem A, `thm:intro-main`), envelope-property form: let `k` be an algebraically closed field
and `𝒳` a unibranch model of rank `r` over `k` (`def:gl-unibranch`). Assume, at every countable
algebraically closed subfield `k₀` of `k`, FHX Lemma 5.5 (`LocalPositivity k₀`),
fibre constancy (`BlowupFibreConstancy k₀`) and, in
characteristic `0`, FHX Theorem 3.1 (`SmoothEnvelopeCharZero k₀`). Then `EP_𝒳(θ)` holds for
**every** `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isUnibranch_of_forall_countable
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hX.hasEnvelopeProperty_of_forall_subfield
    (ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield hLP hFC h₀) θ

/-- **The main theorem** (**`thm:nn-main`**; FHX Theorem A, `thm:intro-main`), in the form of
the source: under the hypotheses of `hasEnvelopeProperty_of_isUnibranch_of_forall_countable`, for a unibranch model
`𝒳`, every `θ ∈ ℝ^r` and every nonempty family `(φ_i)_{i ∈ ι}` (any index type) in `PSH(𝒳, θ)`
that is uniformly bounded above, the usc regularization `(sup_i φ_i)^⋆` lies in `PSH(𝒳, θ)`. -/
theorem isPSH_uscReg_iSup_of_isUnibranch_of_forall_countable
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) {θ : Fin r → ℝ} {ι : Sort*} [Nonempty ι]
    {φ : ι → X.an → EReal} (hφ : ∀ i, X.IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    X.IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup
    (hasEnvelopeProperty_of_isUnibranch_of_forall_countable hLP hFC h₀ hX θ) hφ hbdd

omit [IsAlgClosed k] in
/-- In characteristic `p > 0` the characteristic-`0` hypothesis `SmoothEnvelopeCharZero k₀` at the
countable algebraically closed subfields `k₀` of `k` holds vacuously: such a `k₀` has
characteristic `p` as well. -/
theorem smoothEnvelopeCharZero_of_charP (p : ℕ) [Fact p.Prime] [CharP k p]
    (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] [CharZero k₀] :
    SmoothEnvelopeCharZero k₀ := by
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap k₀ k).injective
  exact absurd (CharP.cast_eq_zero k p) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

/-- **The main theorem in characteristic `p`** (**`thm:nn-main`**; FHX Theorem A for
`char k = p > 0`): for a unibranch model `𝒳` over an algebraically closed field of characteristic
`p`, under `LocalPositivity` and `BlowupFibreConstancy` at the countable
algebraically closed subfields of `k` (no characteristic-`0` input), `EP_𝒳(θ)` for every
`θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isUnibranch_of_charP (p : ℕ) [Fact p.Prime] [CharP k p]
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch_of_forall_countable hLP hFC (smoothEnvelopeCharZero_of_charP p) hX θ

end NormalAmple

end MultiModel

end EnvelopeProperty
