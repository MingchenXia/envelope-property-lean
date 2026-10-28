/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Characterization
import EnvelopeProperty.Global.BlowupFibreConstancyProved

/-!
# The envelope property for unibranch projective varieties: the main results

This file states the main results of Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX, `references/fhx-envelope-20261028`, revision of 2026-10-28; the statements of
Theorem 1.1 and Corollary 1.2 are verbatim those of the preceding revision `832e086`,
`references/fhx-envelope-832e086`), in the form proved in this project, for an integral
multiprojective variety `X = V(I) ⊆ ℙ^{M_1} × ⋯ × ℙ^{M_r}` over an algebraically closed trivially
valued field `k`, and records the complete trust boundary. Blueprint:
`thm:nn-main`, `cor:nn-characterization` (`nonnef.tex`), the all-classes forms of `thm:gl-main`,
`cor:gl-characterization` (`global.tex`), and `rmk:gl-trust-boundary`.

* **FHX Theorem 1.1** (`thm:intro-main`): *let `X` be an integral unibranch projective variety over
  an algebraically closed trivially valued field `k`, and let `θ ∈ N¹(X)_ℝ`; then every nonempty
  bounded-above family `(φ_i) ⊆ PSH(X, θ)` satisfies `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`.*
  Here: `MultiModel.isPSH_uscReg_iSup_quotModel_of_isUnibranch` (families) and
  `MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch` (`EP_X(θ)`); in characteristic `p`,
  `MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch_of_charP`.
* **FHX Corollary 1.2** (`cor:intro-characterization`): *for an integral projective variety `X`
  over `k` the following are equivalent: (1) `X` is unibranch; (2) `EP_X(θ)` holds for every
  `θ ∈ N¹(X)_ℝ`; (3) `EP_X(ω)` holds for some ample class `ω`.* Here:
  `MultiModel.quotModel_isUnibranch_tfae`, with (3) ⇒ (1) import-free as
  `MultiModel.isUnibranch_quotModel_of_hasEnvelopeProperty`.

For general models (`EnvelopeProperty.MultiModel`, `def:gl-model`: also normalizations, finite
covers and Segre–Veronese models) the same statements are
`MultiModel.hasEnvelopeProperty_of_isUnibranch`, `MultiModel.isPSH_uscReg_iSup_of_isUnibranch`,
`MultiModel.hasEnvelopeProperty_of_isUnibranch_of_charP` (`Global/MainTheorem.lean`) and
`MultiModel.isUnibranch_tfae_hasEnvelopeProperty`,
`MultiModel.isUnibranch_of_exists_hasEnvelopeProperty`,
`MultiModel.isUnibranch_of_forall_hasEnvelopeProperty` (`Global/Characterization.lean`,
`Global/ConductorDescent.lean`).

## The objects

* `R = k[x^{(c)}_j]` (`MvPolynomial (MultiModel.QuotVar M) k`), multigraded by
  `deg x^{(c)}_j = e_c`; `I ⊆ R` a prime ideal, relevant at `j₀` (`x^{(c)}_{j₀ c} ∉ I` for every
  `c`, `MultiModel.IsRelevantAt`). Its quotient model `𝒳_I = MultiModel.quotModel I j₀ hj₀`
  (`rmk:gl-model-examples`(1)) has function field the degree-zero fractions of `R / I` and
  coordinate ring `S = k[z] ≅ R / I` when `I` is multihomogeneous
  (`MultiModel.quotModelEquiv`); then `𝒳_I` is the model of `X = V(I)` with the line bundles
  `L_c = O(e_c)|_X`. The theorems below do not need multihomogeneity of `I`.
* Classes: `θ ∈ ℝ^r`, read as `∑_c θ_c c₁(L_c)`. Psh functions: `MultiModel.IsPSH` (`def:gl-psh`,
  BJ22 Definition 4.1 in the model: usc limits `≢ -∞` of decreasing nets of Fubini–Study functions
  of classes tending to `θ`); `EP_X(θ)` is `MultiModel.HasEnvelopeProperty` (`def:gl-psh`).
* Unibranch: `MultiModel.IsUnibranch` (`def:gl-unibranch`): on every affine chart the
  normalization is injective on maximal ideals (FHX §1.1 defines unibranch by "every local ring
  `𝒪_{X,x}` has one branch" and states its equivalence with bijectivity of the normalization;
  surjectivity is lying over). Equivalently every local ring of every chart is unibranch, or
  geometrically unibranch (`MultiModel.isUnibranch_tfae`); both forms are part of
  `MultiModel.quotModel_isUnibranch_tfae`.

## Trust boundary

The theorems carry exactly the following hypotheses, quantified over the countable algebraically
closed fields `k₀ : Type u` with an algebra map `k₀ → k` (the countable algebraically closed
subfields of `k`, decision D-H5). They are explicit `Prop`-valued hypotheses (classes), **not**
axioms:

* `hLP : LocalPositivity k₀` — FHX Lemma 5.5 (`lem:local-PL-positivity`, blueprint
  `lem:wu-local-positivity`), stated verbatim in the graded model (`Local/PositivityImport.lean`);
  it holds for every algebraically closed field (`LocalPositivity.instOfIsAlgClosed`, see above).
  It implies `WuRegularization k₀` (FHX Lemma 5.11(5),(6)) and FHX Proposition 5.22 for
  chart-regularizable functions (`ChartNonflatNorms k₀`) by the instances
  `LocalPositivity.toConvexPLApproximation`, `ConvexPLApproximation.toWuRegularization` and
  `ChartNonflatNorms.of_wuRegularization` (lanes NF1–NF7); `NonflatNorms` (FHX Proposition 5.22
  for weakly psh functions) is **not** assumed.
* `h₀ : SmoothEnvelopeCharZero k₀` for `k₀` of characteristic `0` — FHX Theorem 3.1 = BJ22
  Theorem 5.20 in characteristic `0` (`thm:import-sg-ep-char0`,
  `Projective/SmoothEPCharZeroImport.lean`). It holds for every algebraically closed field of
  characteristic `0` by the instance `SmoothEnvelopeCharZero.instOfIsAlgClosed`
  (`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`, from relative ample Nadel
  vanishing); `MainTheoremFullyUnconditional.lean` restates the theorems of this file with
  neither `hLP` nor `h₀`. In characteristic `p` it is vacuous and
  the `…_of_charP` theorems do not
  carry it (`MultiModel.smoothEnvelopeCharZero_of_charP`).

The implications (2) ⇒ (1) and (3) ⇒ (1) of Corollary 1.2 carry **no** hypothesis.

Fibre constancy, FHX Theorem 6.1 Step 1, is proved by
`blowupFibreConstancy_proved` over every algebraically closed field. The theorems of this file
derive it internally; the older global compatibility interfaces still accept it explicitly.
De Jong's alterations are derived internally from the proved scheme-theoretic theorem and its
model-form bridge. The remaining project-owned inputs are `LocalPositivity` and
`SmoothEnvelopeCharZero`.

Proved in this project, hence not assumed: Theorem 3.1 in characteristic `p` (test ideals, lanes
SG), Corollary 5.26 and Theorem 5.25 (from Lemma 5.5), finite descent (Theorem 4.2), Theorem 6.1
Steps 2 and 3, Siu division and homogeneous slices (Theorem 7.2, Proposition 7.5, Corollary 7.6;
Proposition 7.4 and Corollary 7.5 in revision `832e086`), PSH2 at non-nef classes in the three
places revision `832e086` of FHX uses it (`nonnef.tex`: homogeneous PSH2 and the diagonal lemmas;
the revision of 2026-10-28 replaces these uses by its Lemmas 2.3 and 7.4), Lemma 8.1, Frobenius
descent (Stacks 0CNC/0CNF), additive powers (FHX Lemma 8.2, Roberts–Singh), Theorem 8.3, and BJ22
Theorem 5.12 (via the conductor, `prop:gl-conductor-descent`).

**Not used** anywhere in the dependency cone: BJ22 Theorem 5.6 (non-negligibility of divisorial
points), BJ22 Theorem 6.21, BJ22 Lemma 4.6 (false, `Global/Lemma46Counterexample.lean`),
BJ22 Corollary 4.17 (finiteness on `X^div`), BJ22 Corollary 12.18 (countable regularization),
test configurations, and the energy theory of BJ22. The appendix of FHX (singular
Yau–Tian–Donaldson) is out of scope.

`#print axioms` of every theorem of this file reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Differences from the statements of FHX

* *Varieties and classes.* In this file `X` is given by a multiprojective embedding
  `V(I) ⊆ ∏_c ℙ^{M_c}` and the classes are `θ ∈ ℝ^r`, i.e. the real span of the `c₁(L_c)`. The
  statements of FHX for an integral projective `X` over `k` and every `θ ∈ N¹(X)_ℝ`, with
  Boucksom–Jonsson's psh functions on `X^an` (`Variety.IsPSH`, `Variety.HasEnvelopeProperty`), are
  `Variety.hasEnvelopeProperty_of_isUnibranch`, `Variety.isPSH_uscReg_iSup_of_isUnibranch`,
  `Variety.hasEnvelopeProperty_of_isUnibranch_of_charP` (`Source/MainTheorem.lean`) and
  `Variety.isUnibranch_tfae_hasEnvelopeProperty`, `Variety.isUnibranch_of_hasEnvelopeProperty`
  (`Source/Characterization.lean`; blueprint `thm:var-main`, `cor:var-characterization`). They are
  deduced from the theorems of this file through presentations (`Variety.exists_presentation`,
  `Variety.isPSH_iff_presentation`, `Variety.hasEnvelopeProperty_iff_presentation`), not through
  the spanning-family comparison of `rmk:gl-model-comparison`; their single difference from FHX is
  recorded in `rmk:var-main-fidelity`.
* *Ample classes.* In the model form of Corollary 1.2 (3) below, "ample" is replaced by "positive"
  (all `ω_c > 0`, a sufficient condition for ampleness). The variety form
  `Variety.isUnibranch_of_hasEnvelopeProperty` takes any class of the ample cone.
* *Remaining inputs.* FHX uses Lemma 5.5 (cited from Wu), de Jong's theorem, Gubler–Rabinoff
  and, in characteristic `0`, BJ22 Theorem 5.20. De Jong's theorem and fibre constancy are derived
  internally. The hypotheses below retain Lemma 5.5 and the characteristic-`0` smooth-envelope
  input only over the countable algebraically closed subfields of `k` (FHX Theorem 6.1, Step 2).
  Lemma 5.5 is proved over every algebraically closed field by the instance
  `LocalPositivity.instOfIsAlgClosed` (`Local/LocalPositivityInstance.lean`, blueprint
  `thm:lpn-local-positivity-instance`); `MainTheoremUnconditional.lean` restates the theorems of
  this file without `hLP` (`…_unconditional`, blueprint `thm:lpn-main-unconditional`).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ} {M : Fin r → ℕ}
  (I : Ideal (MvPolynomial (QuotVar M) k)) [I.IsPrime] (j₀ : (c : Fin r) → Fin (M c + 1))

/-- **FHX Theorem 1.1** (`thm:intro-main`; `thm:nn-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`, the
envelope property: let `k` be algebraically closed and `I ⊆ k[x^{(c)}_j]` a prime ideal, relevant at
`j₀`, whose quotient model `𝒳_I` is unibranch. Assume, at every countable algebraically closed
subfield `k₀` of `k`, FHX Lemma 5.5 (`hLP`) and, in characteristic `0`, FHX Theorem 3.1 (`h₀`).
De Jong's alterations and fibre constancy are derived internally. Then `EP_X(θ)` for every
`θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch hLP
    (fun k₀ _ _ _ _ => blowupFibreConstancy_proved k₀) h₀ hX θ

/-- **FHX Theorem 1.1** (`thm:intro-main`; `thm:nn-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`, in the form
of the source: under the hypotheses of `hasEnvelopeProperty_quotModel_of_isUnibranch`, for every
`θ ∈ ℝ^r` and every nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)` uniformly bounded above,
`(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_quotModel_of_isUnibranch
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) {θ : Fin r → ℝ}
    {ι : Sort*} [Nonempty ι] {φ : ι → (quotModel I j₀ hj₀).an → EReal}
    (hφ : ∀ i, (quotModel I j₀ hj₀).IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    (quotModel I j₀ hj₀).IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_of_isUnibranch hLP
    (fun k₀ _ _ _ _ => blowupFibreConstancy_proved k₀) h₀ hX hφ hbdd

/-- **FHX Theorem 1.1 in characteristic `p`** for `X = V(I) ⊆ ∏_c ℙ^{M_c}`: over an algebraically
closed field of characteristic `p > 0`, under FHX Lemma 5.5 (`hLP`) at the countable
algebraically closed subfields of `k`, a unibranch `X` has `EP_X(θ)` for every `θ ∈ ℝ^r`.
De Jong's alterations and fibre constancy are proved internally. -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch_of_charP (p : ℕ) [Fact p.Prime] [CharP k p]
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch_of_charP p hLP
    (fun k₀ _ _ _ _ => blowupFibreConstancy_proved k₀) hX θ

/-- **FHX Corollary 1.2** (`cor:intro-characterization`; `cor:nn-characterization`) for
`X = V(I) ⊆ ∏_c ℙ^{M_c}`: under the hypotheses of `hasEnvelopeProperty_quotModel_of_isUnibranch`,
the following are equivalent: (1) `X` is unibranch (`def:gl-unibranch`); (1′) every local ring of
every affine chart of `X` is unibranch; (1″) every such local ring is geometrically unibranch;
(2) `EP_X(θ)` for every `θ ∈ ℝ^r`; (3) `EP_X(ω)` for some positive `ω ∈ ℝ^r`. The hypotheses
enter only through (1) ⇒ (2) (see `isUnibranch_quotModel_of_hasEnvelopeProperty`). -/
theorem quotModel_isUnibranch_tfae
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hj₀ : IsRelevantAt I j₀) :
    List.TFAE [(quotModel I j₀ hj₀).IsUnibranch,
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, (quotModel I j₀ hj₀).HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ (quotModel I j₀ hj₀).HasEnvelopeProperty ω] :=
  isUnibranch_tfae_hasEnvelopeProperty hLP
    (fun k₀ _ _ _ _ => blowupFibreConstancy_proved k₀) h₀ (quotModel I j₀ hj₀)

/-- **FHX Corollary 1.2, (3) ⇒ (1)** (BJ22 Theorem 5.12, `thm:unibranch`) for
`X = V(I) ⊆ ∏_c ℙ^{M_c}`, with **no** hypothesis: if `EP_X(ω)` holds for some positive
`ω ∈ ℝ^r`, then `X` is unibranch. -/
theorem isUnibranch_quotModel_of_hasEnvelopeProperty (hj₀ : IsRelevantAt I j₀)
    (h : ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ (quotModel I j₀ hj₀).HasEnvelopeProperty ω) :
    (quotModel I j₀ hj₀).IsUnibranch :=
  isUnibranch_of_exists_hasEnvelopeProperty h

end MultiModel

end EnvelopeProperty
