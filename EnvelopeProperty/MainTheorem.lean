/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.QuotModelMainTheorem
import EnvelopeProperty.Global.MainTheorem
import EnvelopeProperty.Local.LocalPositivityInstance
import EnvelopeProperty.Source.Characterization
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroUnconditional
import EnvelopeProperty.Global.EPDecreasingLimits

/-!
# The envelope property for unibranch projective varieties: the main theorems

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX, `paper/`),
Theorem A (`thm:intro-main`), Corollary 1.1 (`cor:intro-characterization`), Corollary 7.6
(`cor:normal-EP`) and Corollary 8.4 (`cor:unibranch-decreasing-stability`). Every theorem of this
file has no hypothesis besides the mathematical ones of FHX (algebraically closed `k`; `X`
integral, normal or unibranch; relevance of the chart index).

## Main results

For an integral projective scheme `X` over an algebraically closed (trivially valued) field `k`:

* `Variety.hasEnvelopeProperty_of_isUnibranch`, `Variety.isPSH_uscReg_iSup_of_isUnibranch`
  (Theorem A): if `X` is unibranch, `EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`, i.e. the usc
  regularization of the supremum of a nonempty family in `PSH(X, θ)` bounded above is θ-psh.
  Here unibranch is `Variety.IsUnibranch X` (the normalization is bijective).
* `Variety.hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk`,
  `Variety.isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk`: Theorem A with FHX's
  definition of unibranch (every local ring `𝒪_{X,x}` has one branch, FHX §1).
* `Variety.isUnibranch_tfae_hasEnvelopeProperty` (Corollary 1.1): `X` is unibranch iff `EP_X(θ)`
  for every `θ` iff `EP_X(ω)` for some ample `ω`, together with the stalk-wise forms of
  unibranchness.

The same statements for the multiprojective models of the proof (`EnvelopeProperty.MultiModel`)
and for `X = V(I) ⊆ ∏_c ℙ^{M_c}` given by a prime ideal `I` (`MultiModel.quotModel`):
`MultiModel.hasEnvelopeProperty_of_isUnibranch`, `MultiModel.isPSH_uscReg_iSup_of_isUnibranch`,
`MultiModel.isUnibranch_tfae_hasEnvelopeProperty`, `MultiModel.hasEnvelopeProperty_of_isNormal`
(Corollary 7.6), `MultiModel.isPSH_of_antitone_of_isUnibranch` (Corollary 8.4),
`MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch`,
`MultiModel.isPSH_uscReg_iSup_quotModel_of_isUnibranch`, `MultiModel.quotModel_isUnibranch_tfae`.

## Proof

The theorems `…_of_forall_countable` of `Global/MainTheorem.lean`, `Global/Characterization.lean`,
`Global/QuotModelMainTheorem.lean`, `Global/EPDecreasingLimits.lean`, `Source/MainTheorem.lean`
and `Source/Characterization.lean` prove these statements from three inputs at the countable
algebraically closed fields `k₀` with an algebra map `k₀ → k`:

* `LocalPositivity k₀` (FHX Lemma 5.5), the instance `LocalPositivity.instOfIsAlgClosed`
  (`Local/LocalPositivityInstance.lean`);
* `SmoothEnvelopeCharZero k₀` (FHX Theorem 3.1 in characteristic `0`, BJ22 Theorem 5.20), the
  instance `SmoothEnvelopeCharZero.instOfIsAlgClosed`
  (`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`);
* `BlowupFibreConstancy k₀` (FHX Theorem 6.1, Step 1), the instance `blowupFibreConstancy_proved`
  (`Global/BlowupFibreConstancyProved.lean`).

This file supplies the three instances.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace EnvelopeProperty

universe u

/-- FHX Lemma 5.5 at every countable algebraically closed field over `k`. -/
private theorem forall_subfield_localPositivity (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀ :=
  fun _ _ _ _ _ => inferInstance

/-- FHX Theorem 3.1 in characteristic `0` at every countable algebraically closed field over
`k`. -/
private theorem forall_subfield_smoothEnvelopeCharZero (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] [CharZero k₀],
      SmoothEnvelopeCharZero k₀ :=
  fun _ _ _ _ _ _ => inferInstance

/-- Fibre constancy (FHX Theorem 6.1, Step 1) at every countable algebraically closed field over
`k`. -/
private theorem forall_subfield_blowupFibreConstancy (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀ :=
  fun _ _ _ _ _ => inferInstance

namespace MultiModel

section Global

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ} [IsAlgClosed k]

/-- **FHX Corollary 7.6** (`cor:normal-EP`) on models: a normal model has `EP_𝒳(θ)` for every
`θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isNormal
    {X : MultiModel k K r} (hX : X.IsNormal) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX θ

/-- **FHX Theorem A** (`thm:intro-main`) on models: a unibranch model has `EP_𝒳(θ)` for every
`θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isUnibranch
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX θ

/-- **FHX Theorem A** (`thm:intro-main`) on models, in the form of the paper: on a unibranch model,
for every `θ ∈ ℝ^r` and every nonempty family `(φ_i)` in `PSH(𝒳, θ)` uniformly bounded above,
`(sup_i φ_i)^⋆ ∈ PSH(𝒳, θ)`. -/
theorem isPSH_uscReg_iSup_of_isUnibranch
    {X : MultiModel k K r} (hX : X.IsUnibranch) {θ : Fin r → ℝ} {ι : Sort*} [Nonempty ι]
    {φ : ι → X.an → EReal} (hφ : ∀ i, X.IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    X.IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_of_isUnibranch_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX hφ
    hbdd

/-- **FHX Corollary 8.4** (`cor:unibranch-decreasing-stability`) on models: on a unibranch model
`𝒳`, let `(ψᵢ)` be a decreasing net with `ψᵢ ∈ PSH(𝒳, θᵢ)` and `θᵢ → θ ∈ ℝ^r`. If its limit `w`
is not identically `-∞`, then `w ∈ PSH(𝒳, θ)`. -/
theorem isPSH_of_antitone_of_isUnibranch
    {X : MultiModel k K r} (hX : X.IsUnibranch) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} {ψ : ι → X.an → EReal}
    (hθ : Filter.Tendsto θs Filter.atTop (nhds θ)) (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) : X.IsPSH θ w :=
  isPSH_of_antitone_of_isUnibranch_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) hX hθ hψ
    hanti hw hne

/-- **FHX Corollary 1.1** (`cor:intro-characterization`) on models: for a model `𝒳`, (1) `𝒳` is
unibranch, (1′) all local rings of all chart algebras are unibranch, (1″) they are all
geometrically unibranch, (2) `EP_𝒳(θ)` for every `θ ∈ ℝ^r`, (3) `EP_𝒳(ω)` for some positive
`ω ∈ ℝ^r` are equivalent. -/
theorem isUnibranch_tfae_hasEnvelopeProperty
    (X : MultiModel k K r) :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, X.HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω] :=
  isUnibranch_tfae_hasEnvelopeProperty_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_blowupFibreConstancy k) (forall_subfield_smoothEnvelopeCharZero k) X

end Global

section Quot

variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ} {M : Fin r → ℕ}
  (I : Ideal (MvPolynomial (QuotVar M) k)) [I.IsPrime] (j₀ : (c : Fin r) → Fin (M c + 1))

/-- **FHX Theorem A** (`thm:intro-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`: let `k` be algebraically
closed and `I ⊆ k[x^{(c)}_j]` a prime ideal, relevant at `j₀`, whose quotient model `𝒳_I` is
unibranch. Then `EP_X(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_quotModel_of_isUnibranch_of_forall_countable I j₀
    (forall_subfield_localPositivity k) (forall_subfield_smoothEnvelopeCharZero k) hj₀ hX θ

/-- **FHX Theorem A** (`thm:intro-main`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`, in the form of the paper:
for a unibranch `𝒳_I`, every `θ ∈ ℝ^r` and every nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)`
uniformly bounded above, `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_quotModel_of_isUnibranch
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) {θ : Fin r → ℝ}
    {ι : Sort*} [Nonempty ι] {φ : ι → (quotModel I j₀ hj₀).an → EReal}
    (hφ : ∀ i, (quotModel I j₀ hj₀).IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    (quotModel I j₀ hj₀).IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_quotModel_of_isUnibranch_of_forall_countable I j₀
    (forall_subfield_localPositivity k) (forall_subfield_smoothEnvelopeCharZero k) hj₀ hX hφ hbdd

/-- **FHX Corollary 1.1** (`cor:intro-characterization`) for `X = V(I) ⊆ ∏_c ℙ^{M_c}`: (1) `X` is
unibranch; (1′) every local ring of every affine chart of `X` is unibranch; (1″) every such local
ring is geometrically unibranch; (2) `EP_X(θ)` for every `θ ∈ ℝ^r`; (3) `EP_X(ω)` for some
positive `ω ∈ ℝ^r` are equivalent. -/
theorem quotModel_isUnibranch_tfae (hj₀ : IsRelevantAt I j₀) :
    List.TFAE [(quotModel I j₀ hj₀).IsUnibranch,
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : (quotModel I j₀ hj₀).ChartIndex, (∀ c, (quotModel I j₀ hj₀).coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum ((quotModel I j₀ hj₀).chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ θ : Fin r → ℝ, (quotModel I j₀ hj₀).HasEnvelopeProperty θ,
      ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ (quotModel I j₀ hj₀).HasEnvelopeProperty ω] :=
  quotModel_isUnibranch_tfae_of_forall_countable I j₀ (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) hj₀

end Quot

end MultiModel

namespace Variety

open NativeRealNumericalClasses

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **FHX Theorem A** (`thm:intro-main`), envelope-property form: let `X` be an integral unibranch
projective variety over an algebraically closed (trivially valued) field `k`. Then `EP_X(θ)` holds
for every `θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_isUnibranch
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) (θ : Space p) : HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_of_isUnibranch_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) p hX θ

/-- **FHX Theorem A** (`thm:intro-main`), in the form of the paper: let `X` be an integral
unibranch projective variety over an algebraically closed (trivially valued) field `k` and
`θ ∈ N¹(X)_ℝ`. Then every nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)` that is uniformly
bounded above satisfies `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_of_isUnibranch
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : IsUnibranch X) {θ : Space p} {ι : Sort*} [Nonempty ι] {φ : ι → An p → EReal}
    (hφ : ∀ i, IsPSH p θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  isPSH_uscReg_iSup_of_isUnibranch_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) p hX hφ hbdd

/-- **FHX Theorem A** (`thm:intro-main`) with FHX's definition of unibranch (every local ring
`𝒪_{X,x}` has one branch), envelope-property form: let `X` be an integral projective variety over
an algebraically closed (trivially valued) field `k` all of whose local rings are unibranch. Then
`EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x)) (θ : Space p) :
    HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_of_isUnibranch p (isUnibranch_iff_isUnibranchLocalRing_stalk.mpr hX) θ

/-- **FHX Theorem A** (`thm:intro-main`) word for word: let `X` be an integral projective variety
over an algebraically closed (trivially valued) field `k` all of whose local rings `𝒪_{X,x}` are
unibranch, and `θ ∈ N¹(X)_ℝ`. Then every nonempty family `(φ_i)_{i ∈ ι}` in `PSH(X, θ)` that is
uniformly bounded above satisfies `(sup_i φ_i)^⋆ ∈ PSH(X, θ)`. -/
theorem isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hX : ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x)) {θ : Space p} {ι : Sort*}
    [Nonempty ι] {φ : ι → An p → EReal} (hφ : ∀ i, IsPSH p θ (φ i))
    (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) :
    IsPSH p θ (uscReg fun y => ⨆ i, φ i y) :=
  isPSH_uscReg_iSup_of_isUnibranch p (isUnibranch_iff_isUnibranchLocalRing_stalk.mpr hX) hφ hbdd

/-- **FHX Corollary 1.1** (`cor:intro-characterization`): let `X` be an integral projective variety
over an algebraically closed field `k`. The following are equivalent:
1. `X` is unibranch, in the form "its normalization is bijective";
1′. every local ring `𝒪_{X,x}` is unibranch (FHX's definition of unibranch);
1″. every local ring `𝒪_{X,x}` is geometrically unibranch;
2. `EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`;
3. `EP_X(ω)` holds for some ample class `ω ∈ Amp(X)`. -/
theorem isUnibranch_tfae_hasEnvelopeProperty
    (X : Scheme.{u}) [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p] :
    List.TFAE [IsUnibranch X,
      ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x),
      IsGeometricallyUnibranchScheme X,
      ∀ θ : Space p, HasEnvelopeProperty p θ,
      ∃ ω ∈ ampleCone p, HasEnvelopeProperty p ω] :=
  isUnibranch_tfae_hasEnvelopeProperty_of_forall_countable (forall_subfield_localPositivity k)
    (forall_subfield_smoothEnvelopeCharZero k) X p

end Variety

end EnvelopeProperty
