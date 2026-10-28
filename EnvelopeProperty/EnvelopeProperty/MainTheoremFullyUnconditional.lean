/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.MainTheoremUnconditional
import EnvelopeProperty.Source.Characterization
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroUnconditional
import EnvelopeProperty.Global.EPDecreasingLimits

/-!
# The main theorems without the hypotheses `LocalPositivity` and `SmoothEnvelopeCharZero`

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX,
`references/fhx-envelope-20261028`, revision of 2026-10-28; Theorem 1.1 and Corollary 1.2 are
verbatim those of revision `832e086`), Theorem 1.1 (`thm:intro-main`), Corollary 1.2
(`cor:intro-characterization`) and Corollary 8.4 (`cor:unibranch-decreasing-stability`, new in the
revision of 2026-10-28). The main theorems
of `EnvelopeProperty/MainTheorem.lean`, `EnvelopeProperty/Global/MainTheorem.lean`,
`EnvelopeProperty/Global/Characterization.lean`, `EnvelopeProperty/Source/MainTheorem.lean` and
`EnvelopeProperty/Source/Characterization.lean` take, at every countable algebraically closed
field `k₀` with an algebra map `k₀ → k`, two hypotheses:

* `hLP : LocalPositivity k₀` (FHX Lemma 5.5), now the instance `LocalPositivity.instOfIsAlgClosed`
  (`Local/LocalPositivityInstance.lean`);
* `h₀ : SmoothEnvelopeCharZero k₀` in characteristic `0` (FHX Theorem 3.1 = BJ22 Theorem 5.20), now
  the instance `SmoothEnvelopeCharZero.instOfIsAlgClosed`
  (`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`, from relative ample Nadel
  vanishing `Char0.relativeAmpleNadelVanishingInput`).

This file restates those theorems without `hLP` and `h₀`. FHX (revision of 2026-10-28) defines
"unibranch" stalk-wise (every local ring `𝒪_{X,x}` has one branch); `Variety.IsUnibranch` is the
equivalent bijectivity of the normalization (`Variety.isUnibranch_iff_isUnibranchLocalRing_stalk`),
and `Variety.hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk_fully_unconditional`,
`Variety.isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk_fully_unconditional` state Theorem
1.1 with the stalk-wise hypothesis.
`MultiModel.isPSH_of_antitone_of_isUnibranch_fully_unconditional` is FHX Corollary 8.4 (PSH2 at
every class on unibranch varieties) on models.

The forms for general models (`MultiModel`, `ProjSubvariety` over a countable subfield) of
`Global/MainTheorem.lean` and `MainTheoremUnconditional.lean` also take the fibre-constancy
hypothesis `hFC : BlowupFibreConstancy k₀` (FHX Theorem 6.1, Step 1); it holds for every
algebraically closed field by the instance `blowupFibreConstancy_proved`
(`Global/BlowupFibreConstancyProved.lean`) and is discharged here as well. Every theorem of this
file therefore has **no** hypothesis besides the mathematical ones of FHX (algebraically closed
`k`, `X` integral or normal or unibranch, relevance of the chart index).

The characteristic-`p` forms (`…_of_charP`) are special cases of the characteristic-free forms;
for `quotModel` they are already hypothesis-free in `MainTheoremUnconditional.lean`.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace EnvelopeProperty

universe u

/-- FHX Lemma 5.5 at every algebraically closed subfield, from the instance. -/
private theorem forall_subfield_localPositivity (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀ :=
  fun _ _ _ _ _ => inferInstance

/-- FHX Theorem 3.1 in characteristic `0` at every algebraically closed subfield, from the
instance. -/
private theorem forall_subfield_smoothEnvelopeCharZero (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] [CharZero k₀],
      SmoothEnvelopeCharZero k₀ :=
  fun _ _ _ _ _ _ => inferInstance

/-- Fibre constancy (FHX Theorem 6.1, Step 1) at every algebraically closed subfield, from the
instance `blowupFibreConstancy_proved`. -/
private theorem forall_subfield_blowupFibreConstancy (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀ :=
  fun _ _ _ _ _ => inferInstance

namespace ProjSubvariety

variable {k : Type u} [Field k]

/-- `ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield` without `hLP`, `hFC`
and `h₀`: ample envelopes over countable algebraically closed subfields (FHX Theorem 6.1,
Step 1). -/
theorem hasEnvelopeProperty_one_of_isProjNormal_of_subfield_fully_unconditional
    (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
    (X₀ : ProjSubvariety k₀ M) (hX₀ : X₀.IsProjNormal) : X₀.HasEnvelopeProperty 1 :=
  hasEnvelopeProperty_one_of_isProjNormal_of_subfield_unconditional
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) k₀ X₀ hX₀

end ProjSubvariety

namespace MultiModel

section Global

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ} [IsAlgClosed k]

/-- `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_countable` without `hLP`, `hFC` and
`h₀` (FHX Corollary 7.6, `cor:normal-EP`, at every class; Corollary 7.5 in revision `832e086`):
a normal model has `EP_𝒳(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isNormal_of_forall_countable_fully_unconditional
    {X : MultiModel k K r} (hX : X.IsNormal) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_forall_countable_unconditional
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX θ

/-- `MultiModel.hasEnvelopeProperty_of_isUnibranch` without `hLP`, `hFC` and `h₀`
(**`thm:nn-main`**; FHX Theorem 1.1): a unibranch model has `EP_𝒳(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isUnibranch_fully_unconditional
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch_unconditional (forall_subfield_blowupFibreConstancy k)
    (forall_subfield_smoothEnvelopeCharZero k) hX θ

/-- `MultiModel.isPSH_uscReg_iSup_of_isUnibranch` without `hLP`, `hFC` and `h₀` (FHX
Theorem 1.1 in the form of the source). -/
theorem isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional
    {X : MultiModel k K r} (hX : X.IsUnibranch) {θ : Fin r → ℝ} {ι : Sort*} [Nonempty ι]
    {φ : ι → X.an → EReal} (hφ : ∀ i, X.IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    X.IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_of_isUnibranch_unconditional (forall_subfield_blowupFibreConstancy k)
    (forall_subfield_smoothEnvelopeCharZero k) hX hφ hbdd

/-- **FHX Corollary 8.4** (`cor:nn-psh2-unibranch`, `cor:ep-unibranch-decreasing-limits`; FHX
`cor:unibranch-decreasing-stability`, revision of 2026-10-28) on models, with no hypothesis: on a
unibranch model `𝒳`, let `(ψᵢ)` be a decreasing net with `ψᵢ ∈ PSH(𝒳, θᵢ)` and `θᵢ → θ ∈ ℝ^r`
(any class). If its limit `w` is not identically `-∞`, then `w ∈ PSH(𝒳, θ)`. This is
`MultiModel.isPSH_of_antitone_of_isUnibranch` without `hLP`, `hFC` and `h₀`. -/
theorem isPSH_of_antitone_of_isUnibranch_fully_unconditional
    {X : MultiModel k K r} (hX : X.IsUnibranch) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} {ψ : ι → X.an → EReal}
    (hθ : Filter.Tendsto θs Filter.atTop (nhds θ)) (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) : X.IsPSH θ w :=
  isPSH_of_antitone_of_isUnibranch (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX hθ hψ
    hanti hw hne

/-- `MultiModel.isUnibranch_tfae_hasEnvelopeProperty` without `hLP`, `hFC` and `h₀`
(**`cor:nn-characterization`**; FHX Corollary 1.2): for a model `𝒳`, (1) `𝒳` is unibranch,
(1′) all local rings of all chart algebras are unibranch, (1″) they are all geometrically
unibranch, (2) `EP_𝒳(θ)` for every `θ ∈ ℝ^r`, (3) `EP_𝒳(ω)` for some positive `ω ∈ ℝ^r` are
equivalent. -/
theorem isUnibranch_tfae_hasEnvelopeProperty_fully_unconditional
    (X : MultiModel k K r) :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] :=
  isUnibranch_tfae_hasEnvelopeProperty (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) X

end Global

section Quot

variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ} {M : Fin r → ℕ}
  (I : Ideal (MvPolynomial (QuotVar M) k)) [I.IsPrime] (j₀ : (c : Fin r) → Fin (M c + 1))

/-- **FHX Theorem 1.1** (`thm:intro-main`; `thm:nn-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`, with no
hypothesis: let `k` be algebraically closed and `I ⊆ k[x^{(c)}_j]` a prime ideal, relevant at
`j₀`, whose quotient model `𝒳_I` is unibranch. Then `EP_X(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch_fully_unconditional
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_quotModel_of_isUnibranch_unconditional I j₀
    (forall_subfield_smoothEnvelopeCharZero k) hj₀ hX θ

/-- **FHX Theorem 1.1** (`thm:intro-main`; `thm:nn-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`, in the
form of the source and with no hypothesis: for a unibranch `𝒳_I`, every `θ ∈ ℝ^r` and every
nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)` uniformly bounded above,
`(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_quotModel_of_isUnibranch_fully_unconditional
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) {θ : Fin r → ℝ}
    {ι : Sort*} [Nonempty ι] {φ : ι → (quotModel I j₀ hj₀).an → EReal}
    (hφ : ∀ i, (quotModel I j₀ hj₀).IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    (quotModel I j₀ hj₀).IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_quotModel_of_isUnibranch_unconditional I j₀
    (forall_subfield_smoothEnvelopeCharZero k) hj₀ hX hφ hbdd

/-- **FHX Corollary 1.2** (`cor:intro-characterization`; `cor:nn-characterization`) for
`X = V(I) ⊆ ∏_c ℙ^{M_c}`, with no hypothesis: (1) `X` is unibranch; (1′) every local ring of
every affine chart of `X` is unibranch; (1″) every such local ring is geometrically unibranch;
(2) `EP_X(θ)` for every `θ ∈ ℝ^r`; (3) `EP_X(ω)` for some positive `ω ∈ ℝ^r` are equivalent. -/
theorem quotModel_isUnibranch_tfae_fully_unconditional (hj₀ : IsRelevantAt I j₀) :
    List.TFAE [(quotModel I j₀ hj₀).IsUnibranch,
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, (quotModel I j₀ hj₀).HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ (quotModel I j₀ hj₀).HasEnvelopeProperty ω] :=
  quotModel_isUnibranch_tfae_unconditional I j₀ (forall_subfield_smoothEnvelopeCharZero k) hj₀

end Quot

end MultiModel

namespace Variety

open NativeRealNumericalClasses

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **FHX Theorem 1.1** (`thm:var-main`; FHX `thm:intro-main`), envelope-property form, with no
hypothesis: let `X` be an integral unibranch projective variety over an algebraically closed
(trivially valued) field `k`. Then `EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_isUnibranch_fully_unconditional
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) (θ : Space p) : HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_of_isUnibranch (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) p hX θ

/-- **FHX Theorem 1.1** (`thm:var-main`; FHX `thm:intro-main`), in the form of the source and
with no hypothesis: let `X` be an integral unibranch projective variety over an algebraically
closed (trivially valued) field `k` and `θ ∈ N¹(X)_ℝ`. Then every nonempty family
`(φ_i)_{i ∈ ι}` in `PSH(X, θ)` that is uniformly bounded above satisfies
`(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) {θ : Space p} {ι : Sort*} [Nonempty ι] {φ : ι → An p → EReal}
    (hφ : ∀ i, IsPSH p θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  isPSH_uscReg_iSup_of_isUnibranch (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) p hX hφ hbdd

/-- **FHX Theorem 1.1** (`thm:fu-variety-main-stalks`; FHX `thm:intro-main`) with FHX's stalk-wise
definition of unibranch (FHX §1.1, revision of 2026-10-28: every local ring `𝒪_{X,x}` has one
branch), envelope-property form, with no hypothesis: let `X` be an integral projective variety over
an algebraically closed (trivially valued) field `k` all of whose local rings are unibranch. Then
`EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk_fully_unconditional
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x)) (θ : Space p) :
    HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_of_isUnibranch_fully_unconditional p
    (isUnibranch_iff_isUnibranchLocalRing_stalk.mpr hX) θ

/-- **FHX Theorem 1.1** (`thm:fu-variety-main-stalks`; FHX `thm:intro-main`) word for word: with
FHX's stalk-wise definition of unibranch and with no hypothesis, let `X` be an integral projective
variety over an algebraically closed (trivially valued) field `k` all of whose local rings
`𝒪_{X,x}` are unibranch, and `θ ∈ N¹(X)_ℝ`. Then every nonempty family `(φ_i)_{i ∈ ι}` in
`PSH(X, θ)` that is uniformly bounded above satisfies `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk_fully_unconditional
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x)) {θ : Space p} {ι : Sort*}
    [Nonempty ι] {φ : ι → An p → EReal} (hφ : ∀ i, IsPSH p θ (φ i))
    (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional p
    (isUnibranch_iff_isUnibranchLocalRing_stalk.mpr hX) hφ hbdd

/-- **FHX Corollary 1.2** (`cor:var-characterization`; FHX `cor:intro-characterization`), with no
hypothesis: let `X` be an integral projective variety over an algebraically closed field `k`.
The following are equivalent:
1. `X` is unibranch, in the form "its normalization is bijective";
1′. every local ring `𝒪_{X,x}` is unibranch (FHX §1.1's definition of unibranch);
1″. every local ring `𝒪_{X,x}` is geometrically unibranch;
2. `EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`;
3. `EP_X(ω)` holds for some ample class `ω ∈ Amp(X)`. -/
theorem isUnibranch_tfae_hasEnvelopeProperty_fully_unconditional
    (X : Scheme.{u}) [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p] :
    List.TFAE [IsUnibranch X,
      ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x),
      IsGeometricallyUnibranchScheme X,
      ∀ θ : Space p, HasEnvelopeProperty p θ,
      ∃ ω ∈ ampleCone p, HasEnvelopeProperty p ω] :=
  isUnibranch_tfae_hasEnvelopeProperty (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) X p

end Variety

end EnvelopeProperty
