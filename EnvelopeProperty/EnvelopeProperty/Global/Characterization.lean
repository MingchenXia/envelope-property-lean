/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MainTheorem
import EnvelopeProperty.Global.ConductorDescent

/-!
# Unibranchness is characterized by the envelope property (FHX Corollary 1.2)

This file implements the blueprint node `cor:nn-characterization` of the chapter `nonnef.tex` (the
all-classes form of `cor:gl-characterization` of `global.tex`, decisions D-NN1, D-NN2, D-C1) for
the formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX, revision `832e086`, Corollary 1.2, `cor:intro-characterization`): *for an integral projective
variety `X` over `k` the following are equivalent: (1) `X` is unibranch; (2) `EP_X(θ)` holds for
every `θ ∈ N¹(X)_ℝ`; (3) `EP_X(ω)` holds for some ample class `ω`*. The variety is an integral
multiprojective model `𝒳` of rank `r` over an algebraically closed field `k`
(`EnvelopeProperty.MultiModel`), the classes are `θ ∈ ℝ^r` and "ample" is read as "positive" (all
coordinates `> 0`, `rmk:gl-model-comparison`).

## Main results

* `MultiModel.isUnibranch_of_forall_hasEnvelopeProperty` ((2) ⇒ (1)) and
  `MultiModel.isUnibranch_of_exists_hasEnvelopeProperty` ((3) ⇒ (1), lane G14a,
  `Global/ConductorDescent.lean`): **no imported statement is used** (BJ22 Theorem 5.12,
  `thm:unibranch`, re-proved through the conductor, `prop:gl-conductor-descent`).
* `MultiModel.isUnibranch_tfae_of_imp`: (1) ⇔ (2) ⇔ (3) for a model on which (1) ⇒ (2) is known;
  only the implication (1) ⇒ (2) is an input.
* **`cor:nn-characterization`**: `MultiModel.isUnibranch_tfae_hasEnvelopeProperty`, the
  equivalence of (1), (2), (3) under the hypotheses of the main theorem
  (`MultiModel.hasEnvelopeProperty_of_isUnibranch`, `thm:nn-main`: `LocalPositivity`,
  `BlowupFibreConstancy` and, in characteristic `0`, `SmoothEnvelopeCharZero`
  at the countable algebraically closed subfields of `k`), together with the local forms of (1):
  (1′) every local ring of every chart algebra is unibranch, (1″) every such local ring is
  geometrically unibranch (Stacks / EGA IV 0 (23.2.1), `MultiModel.isUnibranch_tfae`, lane G12b).
  `MultiModel.isUnibranch_iff_forall_hasEnvelopeProperty` and
  `MultiModel.isUnibranch_iff_exists_hasEnvelopeProperty` extract (1) ⇔ (2) and (1) ⇔ (3).
* `MultiModel.isUnibranch_tfae_hasEnvelopeProperty_of_charP`: the same in characteristic `p > 0`
  without the characteristic-`0` import.

## Deviations from the source

* (3) asks for a **positive** class `ω ∈ ℝ^r` (all `ω_c > 0`), a sufficient condition for
  ampleness of `∑_c ω_c c₁(L_c)`; ample classes with non-positive model coordinates are not covered
  by the formal (3) ⇒ (1). With (2) ⇒ (3) through `ω = 𝟙` the three statements are equivalent as in
  FHX.
* (2) quantifies over `θ ∈ ℝ^r`, read as `∑_c θ_c c₁(L_c) ∈ N¹(X)_ℝ`; every class of `N¹(X)_ℝ` is of
  this form when the `L_c` span `N¹(X)_ℚ` (`rmk:gl-model-comparison`, not formalized).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

section Characterization

variable [IsAlgClosed k]

/-- **FHX Corollary 1.2, (2) ⇒ (1)** (`cor:nn-characterization`), with no imported statement: a
model with the envelope property at every class is unibranch (take `ω = 𝟙` in
`isUnibranch_of_exists_hasEnvelopeProperty`). -/
theorem isUnibranch_of_forall_hasEnvelopeProperty (h : ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ) :
    X.IsUnibranch :=
  isUnibranch_of_exists_hasEnvelopeProperty ⟨1, fun _ => one_pos, h 1⟩

/-- **The characterization from the main theorem** (`cor:nn-characterization`): if unibranchness
of `𝒳` implies `EP_𝒳(θ)` for every `θ ∈ ℝ^r` (`hmain`, the conclusion of `thm:nn-main`), then
(1) `𝒳` is unibranch, (2) `EP_𝒳(θ)` for every `θ ∈ ℝ^r`, and (3) `EP_𝒳(ω)` for some positive
`ω ∈ ℝ^r` are equivalent. (2) ⇒ (3) takes `ω = 𝟙`; (3) ⇒ (1) is
`isUnibranch_of_exists_hasEnvelopeProperty` and uses no imported statement. -/
theorem isUnibranch_tfae_of_imp
    (hmain : X.IsUnibranch → ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ) :
    List.TFAE [X.IsUnibranch, ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] := by
  tfae_have 1 → 2 := hmain
  tfae_have 2 → 3 := fun h => ⟨1, fun _ => one_pos, h 1⟩
  tfae_have 3 → 1 := isUnibranch_of_exists_hasEnvelopeProperty
  tfae_finish

/-- **The characterization with the local forms of unibranchness**, from the main theorem: if
unibranchness of `𝒳` implies `EP_𝒳(θ)` for every `θ` (`hmain`), the following are equivalent:
(1) `𝒳` is unibranch (`def:gl-unibranch`); (1′) every local ring `(A_j)_𝔭` of every chart algebra is
unibranch (`IsUnibranchLocalRing`); (1″) every such local ring is geometrically unibranch
(`IsGeometricallyUnibranchLocalRing`); (2) `EP_𝒳(θ)` for every `θ ∈ ℝ^r`; (3) `EP_𝒳(ω)` for some
positive `ω`. -/
theorem isUnibranch_tfae_localRing_of_imp
    (hmain : X.IsUnibranch → ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ) :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] := by
  have hloc := X.isUnibranch_tfae
  have hep := isUnibranch_tfae_of_imp hmain
  tfae_have 1 ↔ 2 := hloc.out 0 1
  tfae_have 1 ↔ 3 := hloc.out 0 2
  tfae_have 1 ↔ 4 := hep.out 0 1
  tfae_have 1 ↔ 5 := hep.out 0 2
  tfae_finish

/-- **FHX Corollary 1.2** (**`cor:nn-characterization`**, the all-classes form of
`cor:gl-characterization`; FHX `cor:intro-characterization`): let `k` be algebraically closed and
`𝒳` a model of rank `r` over `k`. Assume, at every countable algebraically closed subfield `k₀` of
`k`, `LocalPositivity k₀` (FHX Lemma 5.5), `BlowupFibreConstancy k₀` and,
in characteristic `0`, `SmoothEnvelopeCharZero k₀` (the hypotheses of `thm:nn-main`). Then the
following are equivalent: (1) `𝒳` is unibranch; (1′) all local rings of all chart algebras are
unibranch; (1″) they are all geometrically unibranch; (2) `EP_𝒳(θ)` for every `θ ∈ ℝ^r`;
(3) `EP_𝒳(ω)` for some positive `ω ∈ ℝ^r`. The hypotheses enter only through (1) ⇒ (2): the
implications (2) ⇒ (1) and (3) ⇒ (1) are `isUnibranch_of_forall_hasEnvelopeProperty` and
`isUnibranch_of_exists_hasEnvelopeProperty`, which assume nothing. De Jong's alterations are
supplied internally. -/
theorem isUnibranch_tfae_hasEnvelopeProperty
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (X : MultiModel k K r) :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] :=
  isUnibranch_tfae_localRing_of_imp fun hX => hasEnvelopeProperty_of_isUnibranch hLP hFC h₀ hX

/-- **FHX Corollary 1.2 in characteristic `p`** (`cor:nn-characterization` for `char k = p > 0`):
the equivalences of `isUnibranch_tfae_hasEnvelopeProperty` under `LocalPositivity`
and `BlowupFibreConstancy` at the countable algebraically closed subfields of
`k`, without the characteristic-`0` import. -/
theorem isUnibranch_tfae_hasEnvelopeProperty_of_charP (p : ℕ) [Fact p.Prime] [CharP k p]
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (X : MultiModel k K r) :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] :=
  isUnibranch_tfae_hasEnvelopeProperty hLP hFC (smoothEnvelopeCharZero_of_charP p) X

/-- **FHX Corollary 1.2, (1) ⇔ (2)**, under the hypotheses of the main theorem: `𝒳` is unibranch
iff `EP_𝒳(θ)` holds for every `θ ∈ ℝ^r`. -/
theorem isUnibranch_iff_forall_hasEnvelopeProperty
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (X : MultiModel k K r) :
    X.IsUnibranch ↔ ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ :=
  (isUnibranch_tfae_hasEnvelopeProperty hLP hFC h₀ X).out 0 3

/-- **FHX Corollary 1.2, (1) ⇔ (3)**, under the hypotheses of the main theorem: `𝒳` is unibranch
iff `EP_𝒳(ω)` holds for some positive `ω ∈ ℝ^r`. -/
theorem isUnibranch_iff_exists_hasEnvelopeProperty
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (X : MultiModel k K r) :
    X.IsUnibranch ↔ ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω :=
  (isUnibranch_tfae_hasEnvelopeProperty hLP hFC h₀ X).out 0 4

end Characterization

end MultiModel

end EnvelopeProperty
