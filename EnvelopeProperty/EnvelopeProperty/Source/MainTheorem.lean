/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Source.PSHComparison
import EnvelopeProperty.Source.UnibranchPresentation
import EnvelopeProperty.Global.MainTheorem
import EnvelopeProperty.Global.BlowupFibreConstancyProved

/-! # FHX Theorem 1.1 for projective varieties

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX,
`fhx-envelope-20261028`), Theorem 1.1 (`thm:intro-main`): *let `X` be an integral unibranch
projective variety over an algebraically closed trivially valued field `k`, and let
`θ ∈ N¹(X)_ℝ`. Then every nonempty bounded-above family `(φ_i) ⊆ PSH(X, θ)` satisfies
`(sup_i φ_i)^⋆ ∈ PSH(X, θ)`.* Blueprint: `thm:var-main`.

The statements of this file are about the scheme itself:

* `X : Scheme`, integral, with a projective structure morphism `p : X ⟶ Spec k`
  (`AlgebraicGeometry.IsProjective`);
* `θ ∈ N¹(X)_ℝ = NativeRealNumericalClasses.Space p` (real line bundle classes modulo numerical
  equivalence against all closed integral curves);
* `X^an = Variety.An p`, the Berkovich analytification over the trivially valued `k`;
* `PSH(X, θ) = Variety.IsPSH p θ` (BJ22 Definition 4.1, `bj22-trivval:defi:psh`, with
  convergence of classes in the order of the ample cone, `Variety.AmpleTendsto`) and
  `EP_X(θ) = Variety.HasEnvelopeProperty p θ`;
* unibranch: `Variety.IsUnibranch X` (FHX §1.1: every local ring `𝒪_{X,x}` has one branch; here in
  the equivalent form "the normalization of `X` is bijective",
  `Variety.isUnibranch_iff_isUnibranchLocalRing_stalk`).

## Main results

* `Variety.hasEnvelopeProperty_of_isUnibranch`: `EP_X(θ)` for every `θ ∈ N¹(X)_ℝ`;
* `Variety.isPSH_uscReg_iSup_of_isUnibranch`: the family form of FHX Theorem 1.1;
* `Variety.hasEnvelopeProperty_of_isUnibranch_of_charP`,
  `Variety.isPSH_uscReg_iSup_of_isUnibranch_of_charP`: in characteristic `ℓ > 0`, without the
  characteristic-`0` hypothesis.

## Proof

Choose a presentation `θ = ∑_c θm_c [q_c^* 𝒪(1)]` (`Variety.exists_presentation`,
`lem:pm-exists-presentation`). Its multiprojective model `𝒫` is unibranch since `X` is
(`Variety.isUnibranch_iff_presentation`, `thm:var-unibranch-presentation`), so `EP_𝒫(θm)` by the
model main theorem (`MultiModel.hasEnvelopeProperty_of_isUnibranch`, `thm:nn-main`), and
`EP_X(θ)` follows by the comparison of psh functions
(`Variety.hasEnvelopeProperty_iff_presentation`, `cor:var-ep-comparison`).

## Hypotheses

The theorems carry exactly the hypotheses of the model main theorem
(`EnvelopeProperty.MainTheorem`), quantified over the countable algebraically closed fields
`k₀ → k`: `hLP : LocalPositivity k₀` (FHX Lemma 5.5) and, for the characteristic-free forms,
`h₀ : SmoothEnvelopeCharZero k₀` in characteristic `0` (FHX Theorem 3.1). Fibre constancy and
de Jong's alterations are proved and supplied internally. The only other remaining boundary is
the topology of `N¹(X)_ℝ` (BJ22 uses the Euclidean topology of the finite dimensional space
`Num(X)`): `Variety.AmpleTendsto` is that convergence when `N¹(X)_ℝ` is finite dimensional
(`Variety.ampleTendsto_iff_tendsto`); finite dimensionality is not formalized.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **FHX Theorem 1.1** (`thm:var-main`; FHX `thm:intro-main`), envelope-property form: let `X`
be an integral unibranch projective variety over an algebraically closed (trivially valued)
field `k`. Assume, at every countable algebraically closed subfield `k₀` of `k`, FHX Lemma 5.5
(`hLP`) and, in characteristic `0`, FHX Theorem 3.1 (`h₀`). Then `EP_X(θ)` holds for every
`θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_isUnibranch
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) (θ : Space p) : HasEnvelopeProperty p θ := by
  obtain ⟨r, d, q, hp, _, θm, rfl⟩ := exists_presentation p θ
  let := p.stalkAlgebra (genericPoint X)
  exact (hasEnvelopeProperty_iff_presentation d q p hp θm).mpr
    (MultiModel.hasEnvelopeProperty_of_isUnibranch hLP
      (fun k₀ _ _ _ _ => blowupFibreConstancy_proved k₀) h₀
      ((isUnibranch_iff_presentation q p hp).mp hX) θm)

/-- **FHX Theorem 1.1** (`thm:var-main`; FHX `thm:intro-main`), in the form of the source:
under the hypotheses of `hasEnvelopeProperty_of_isUnibranch`, for every `θ ∈ N¹(X)_ℝ` and every
nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)` that is uniformly bounded above,
`(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_of_isUnibranch
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) {θ : Space p} {ι : Sort*} [Nonempty ι] {φ : ι → An p → EReal}
    (hφ : ∀ i, IsPSH p θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  HasEnvelopeProperty.isPSH_uscReg_iSup (p := p)
    (hasEnvelopeProperty_of_isUnibranch hLP h₀ p hX θ) hφ hbdd

/-- **FHX Theorem 1.1 in characteristic `ℓ > 0`** (`thm:var-main`): over an algebraically closed
field of characteristic `ℓ`, under FHX Lemma 5.5 (`hLP`) at the countable algebraically closed
subfields of `k` (no characteristic-`0` input), every integral unibranch projective variety has
`EP_X(θ)` for every `θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_isUnibranch_of_charP (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) (θ : Space p) : HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_of_isUnibranch hLP (MultiModel.smoothEnvelopeCharZero_of_charP ℓ) p hX θ

/-- **FHX Theorem 1.1 in characteristic `ℓ > 0`**, family form. -/
theorem isPSH_uscReg_iSup_of_isUnibranch_of_charP (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) {θ : Space p} {ι : Sort*} [Nonempty ι] {φ : ι → An p → EReal}
    (hφ : ∀ i, IsPSH p θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  HasEnvelopeProperty.isPSH_uscReg_iSup (p := p)
    (hasEnvelopeProperty_of_isUnibranch_of_charP ℓ hLP p hX θ) hφ hbdd

end EnvelopeProperty.Variety
