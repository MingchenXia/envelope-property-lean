/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.MainTheorem
import EnvelopeProperty.Global.MainTheorem
import EnvelopeProperty.Local.LocalPositivityInstance

/-!
# The main theorems without the hypothesis `LocalPositivity`

The main theorems of `EnvelopeProperty/MainTheorem.lean` and
`EnvelopeProperty/Global/MainTheorem.lean` (Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Theorem 1.1 `thm:intro-main` and Corollary 1.2
`cor:intro-characterization`) take FHX Lemma 5.5 at the
countable algebraically closed subfields of `k` as the hypothesis `hLP`. That lemma is now the
instance `LocalPositivity.instOfIsAlgClosed` (`Local/LocalPositivityInstance.lean`), so the
hypothesis is discharged. This file restates each of those theorems without `hLP`; the remaining
hypotheses (`SmoothEnvelopeCharZero` in characteristic `0`, and in `Global/MainTheorem.lean`
fibre constancy `BlowupFibreConstancy`) are kept here. Both are proved as well (instances
`SmoothEnvelopeCharZero.instOfIsAlgClosed` and `blowupFibreConstancy_proved`), and
`MainTheoremFullyUnconditional.lean` states the theorems with no hypothesis beyond FHX's.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u

/-- FHX Lemma 5.5 at every algebraically closed subfield, from the instance. -/
private theorem localPositivity_forall_subfield (k : Type u) [Field k] :
    ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀ :=
  fun _ _ _ _ _ => inferInstance

namespace ProjSubvariety

variable {k : Type u} [Field k]

/-- `ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield` without `hLP`: ample
envelopes over countable algebraically closed subfields (FHX Theorem 6.1, Step 1). -/
theorem hasEnvelopeProperty_one_of_isProjNormal_of_subfield_unconditional
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
    (X₀ : ProjSubvariety k₀ M) (hX₀ : X₀.IsProjNormal) : X₀.HasEnvelopeProperty 1 :=
  hasEnvelopeProperty_one_of_isProjNormal_of_subfield (localPositivity_forall_subfield k) hFC h₀
    k₀ X₀ hX₀

end ProjSubvariety

namespace MultiModel

section Global

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ} [IsAlgClosed k]

/-- `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_countable` without `hLP` (FHX
Corollary 7.6, `cor:normal-EP`, at every class; Corollary 7.5 in revision `832e086`). -/
theorem hasEnvelopeProperty_of_isNormal_of_forall_countable_unconditional
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsNormal) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_forall_countable (localPositivity_forall_subfield k) hFC h₀
    hX θ

/-- `MultiModel.hasEnvelopeProperty_of_isUnibranch` without `hLP` (**`thm:nn-main`**; FHX
Theorem 1.1): a unibranch model has `EP_𝒳(θ)` for every `θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isUnibranch_unconditional
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch (localPositivity_forall_subfield k) hFC h₀ hX θ

/-- `MultiModel.isPSH_uscReg_iSup_of_isUnibranch` without `hLP` (FHX Theorem 1.1 in the form of
the source). -/
theorem isPSH_uscReg_iSup_of_isUnibranch_unconditional
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) {θ : Fin r → ℝ} {ι : Sort*} [Nonempty ι]
    {φ : ι → X.an → EReal} (hφ : ∀ i, X.IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    X.IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_of_isUnibranch (localPositivity_forall_subfield k) hFC h₀ hX hφ hbdd

/-- `MultiModel.hasEnvelopeProperty_of_isUnibranch_of_charP` without `hLP` (FHX Theorem 1.1 in
characteristic `p > 0`). -/
theorem hasEnvelopeProperty_of_isUnibranch_of_charP_unconditional (p : ℕ) [Fact p.Prime]
    [CharP k p]
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    {X : MultiModel k K r} (hX : X.IsUnibranch) (θ : Fin r → ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isUnibranch_of_charP p (localPositivity_forall_subfield k) hFC hX θ

end Global

section Quot

variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ} {M : Fin r → ℕ}
  (I : Ideal (MvPolynomial (QuotVar M) k)) [I.IsPrime] (j₀ : (c : Fin r) → Fin (M c + 1))

/-- `MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch` without `hLP` (**FHX Theorem 1.1**,
`thm:intro-main`, for `X = V(I) ⊆ ∏_c ℙ^{M_c}`). -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch_unconditional
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_quotModel_of_isUnibranch I j₀ (localPositivity_forall_subfield k) h₀ hj₀ hX
    θ

/-- `MultiModel.isPSH_uscReg_iSup_quotModel_of_isUnibranch` without `hLP` (FHX Theorem 1.1 in the
form of the source, for `X = V(I) ⊆ ∏_c ℙ^{M_c}`). -/
theorem isPSH_uscReg_iSup_quotModel_of_isUnibranch_unconditional
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) {θ : Fin r → ℝ}
    {ι : Sort*} [Nonempty ι] {φ : ι → (quotModel I j₀ hj₀).an → EReal}
    (hφ : ∀ i, (quotModel I j₀ hj₀).IsPSH θ (φ i)) (hbdd : ∃ C : ℝ, ∀ i v, φ i v ≤ C) :
    (quotModel I j₀ hj₀).IsPSH θ (uscReg fun v => ⨆ i, φ i v) :=
  isPSH_uscReg_iSup_quotModel_of_isUnibranch I j₀ (localPositivity_forall_subfield k) h₀ hj₀ hX
    hφ hbdd

/-- `MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch_of_charP` without `hLP` (FHX
Theorem 1.1 in characteristic `p > 0`, for `X = V(I) ⊆ ∏_c ℙ^{M_c}`). -/
theorem hasEnvelopeProperty_quotModel_of_isUnibranch_of_charP_unconditional (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (hj₀ : IsRelevantAt I j₀) (hX : (quotModel I j₀ hj₀).IsUnibranch) (θ : Fin r → ℝ) :
    (quotModel I j₀ hj₀).HasEnvelopeProperty θ :=
  hasEnvelopeProperty_quotModel_of_isUnibranch_of_charP I j₀ p (localPositivity_forall_subfield k)
    hj₀ hX θ

/-- `MultiModel.quotModel_isUnibranch_tfae` without `hLP` (**FHX Corollary 1.2**,
`cor:intro-characterization`, for `X = V(I) ⊆ ∏_c ℙ^{M_c}`). -/
theorem quotModel_isUnibranch_tfae_unconditional
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
  quotModel_isUnibranch_tfae I j₀ (localPositivity_forall_subfield k) h₀ hj₀

end Quot

end MultiModel

end EnvelopeProperty
