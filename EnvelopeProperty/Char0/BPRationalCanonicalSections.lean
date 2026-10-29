import EnvelopeProperty.Char0.BPCanonicalDifferentialNonzero
import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatioImage
import EnvelopeProperty.AlgGeom.GenericOpenFunctionField

/-! # ALL original BP canonical sections have their SAME actual rational coefficients -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace EnvelopeProperty.Char0.BPRationalCanonicalSections
universe u
set_option backward.isDefEq.respectTransparency false
variable {k R : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]

private abbrev originalBPRatioLine
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :=
  RoundedCanonicalModule.relative f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n

private def originalBPRatioSection
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) : Γ(originalBPRatioLine f n I hI, ⊤) :=
  (RoundedCanonicalModule.differentialSection f
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op ⊤)
      (show Γ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, ⊤) from 1)

private theorem originalBPRatioSectionNeZero
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    (RoundedCanonicalModule.differentialSection f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op ⊤)
        (show Γ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, ⊤) from 1) ≠ 0 :=
  @affinePrincipalization_differentialGlobalSection_ne_zero k R _ _ _ _ f n _ I hI

private instance originalBPRatioIntegral
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) : IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

private instance originalBPRatioSmooth
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    SmoothOfRelativeDimension n ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private theorem originalBPRatioLineInvertible
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) : Scheme.Modules.IsInvertible (originalBPRatioLine f n I hI) :=
  @RoundedCanonicalModule.relative_isInvertible (Spec (.of R))
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last k _ f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
    inferInstance (originalBPRatioSmooth f n I hI)

variable (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥)

/-- ALL actual sections of the SAME original BP relative canonical line
have genuine semilinear rational coefficients in its SAME actual generic field.
Target integrality, line invertibility and nonzero differential are DERIVED. -/
def normalizedCoefficient (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U] :
    Γ(originalBPRatioLine f n I hI, U) →ₛₗ[
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.germToFunctionField U).hom]
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.functionField :=
  CanonicalGeometry.sectionRatio (originalBPRatioLine f n I hI)
    (originalBPRatioLineInvertible f n I hI) (originalBPRatioSection f n I hI)
    (originalBPRatioSectionNeZero f n I hI) U

/-- The genuine rational coefficient is faithful on EVERY original nonempty open. -/
theorem normalizedCoefficient_injective
    (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U] :
    Function.Injective (normalizedCoefficient f n I hI U) :=
  CanonicalGeometry.sectionRatio_injective (originalBPRatioLine f n I hI)
    (originalBPRatioLineInvertible f n I hI) (originalBPRatioSection f n I hI)
    (originalBPRatioSectionNeZero f n I hI) U

variable {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The SAME actual BP function field identifies with the SAME
specified affine fraction field, from the genuine original off-centre isomorphism. -/
def fractionFieldEquiv : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.functionField ≃+* F := by
  let U : (Spec (.of R)).Opens := (specIdealSheaf I).support.compl
  let : Nonempty U := Set.nonempty_coe_sort.mpr (nonempty_compl_support_specIdealSheaf I hI)
  let : IsIso ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ∣_ U) :=
    affinePrincipalization_isIso_restrict f n I hI
  exact GenericOpenFunctionField.specFractionFieldEquiv
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite U

/-- EVERY section of the SAME original BP relative canonical line has its
actual rational coefficient in the original affine fraction field. -/
def fractionCoefficient (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U]
    (s : Γ(originalBPRatioLine f n I hI, U)) : F :=
  fractionFieldEquiv (F := F) f n I hI (normalizedCoefficient f n I hI U s)

/-- The original fraction-field coefficient retains ALL actual original sections faithfully. -/
theorem fractionCoefficient_injective
    (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U] :
    Function.Injective (fractionCoefficient (F := F) f n I hI U) :=
  (fractionFieldEquiv (F := F) f n I hI).injective.comp
    (normalizedCoefficient_injective f n I hI U)

/-- Multiplying the SAME original differential by ANY original affine
coefficient gives exactly that SAME coefficient in the prescribed original field. -/
theorem fractionCoefficient_originalRing (a : R) :
    letI : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens)) :=
      ⟨⟨genericPoint (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, by trivial⟩⟩
    fractionCoefficient (F := F) f n I hI ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens))
      ((RoundedCanonicalModule.differentialSection f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app
        (.op ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens)))
          ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite.app ⊤ ((Scheme.ΓSpecIso (.of R)).inv a))) = algebraMap R F a := by
  let : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens)) :=
    ⟨⟨genericPoint (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, by trivial⟩⟩
  have hn := CanonicalGeometry.sectionRatio_unitSection_apply (originalBPRatioLine f n I hI)
    (originalBPRatioLineInvertible f n I hI)
    (RoundedCanonicalModule.differentialSection f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n)
    (originalBPRatioSectionNeZero f n I hI)
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens))
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite.app ⊤ ((Scheme.ΓSpecIso (.of R)).inv a))
  let U : (Spec (.of R)).Opens := (specIdealSheaf I).support.compl
  let : Nonempty U := Set.nonempty_coe_sort.mpr (nonempty_compl_support_specIdealSheaf I hI)
  let : IsIso ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  exact (congrArg (fractionFieldEquiv (F := F) f n I hI) hn).trans
    (GenericOpenFunctionField.specFractionFieldEquiv_coefficients
      (F := F) (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite U a)

end EnvelopeProperty.Char0.BPRationalCanonicalSections
