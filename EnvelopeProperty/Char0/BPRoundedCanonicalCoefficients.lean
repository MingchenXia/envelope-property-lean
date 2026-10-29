import EnvelopeProperty.Char0.BPRationalCanonicalSections
import EnvelopeProperty.Char0.RoundedCanonicalExactness

/-! # Faithful rational coefficients of the ENTIRE original rounded BP canonical module -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace EnvelopeProperty.Char0.BPRoundedCanonicalCoefficients
universe u
set_option backward.isDefEq.respectTransparency false
variable {k R : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]

private theorem originalRoundedMonoAppInjective {X : Scheme.{u}} {M N : X.Modules}
    (α : M ⟶ N) [Mono α] (U : X.Opens) : Function.Injective (α.val.app (.op U)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (.op U)
  have : Mono (E.map α) := inferInstance
  exact (ModuleCat.mono_iff_injective (E.map α)).mp inferInstance

variable (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥)

private abbrev originalRoundedBPIdeal :=
  (specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite

private theorem originalRoundedBPSnc : (originalRoundedBPIdeal f n I hI).IsIdealOfSncDivisor :=
  affinePrincipalization_isIdealOfSncDivisor f n I hI

private abbrev originalRoundedBPModule (q : ℚ) :=
  RoundedCanonicalModule.relativeRounded f
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
    (originalRoundedBPIdeal f n I hI) (originalRoundedBPSnc f n I hI) q

private def originalRoundedBPInclusion (q : ℚ) :=
  RoundedCanonicalModule.relativeRoundedInclusion f
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
    (originalRoundedBPIdeal f n I hI) (originalRoundedBPSnc f n I hI) q

private theorem originalRoundedBPInclusionMono (q : ℚ) :
    Mono (originalRoundedBPInclusion f n I hI q) := by
  let : SmoothOfRelativeDimension n
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
    affinePrincipalization_smoothOfRelativeDimension f n I hI
  exact RoundedCanonicalModule.mono_relativeRoundedInclusion f
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
    (originalRoundedBPIdeal f n I hI) (originalRoundedBPSnc f n I hI) q

variable {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F]

/-- EVERY original rounded BP canonical section has its SAME genuine rational coefficient
through the ENTIRE actual rounded inclusion and SAME original prescribed fraction field. -/
def coefficient (q : ℚ)
    (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U]
    (s : Γ(originalRoundedBPModule f n I hI q, U)) : F :=
  BPRationalCanonicalSections.fractionCoefficient (F := F) f n I hI U
    ((originalRoundedBPInclusion f n I hI q).val.app (.op U) s)

/-- ALL original sections of the WHOLE rounded module are retained faithfully,
with no image/regularity/rational-coefficient comparison premise. -/
theorem coefficient_injective (q : ℚ)
    (U : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens) [Nonempty U] :
    Function.Injective (coefficient (F := F) f n I hI q U) := by
  let : Mono (originalRoundedBPInclusion f n I hI q) := originalRoundedBPInclusionMono f n I hI q
  exact (BPRationalCanonicalSections.fractionCoefficient_injective (F := F) f n I hI U).comp
    (originalRoundedMonoAppInjective _ U)

/-- The SAME original rounded rational coefficient equals a prescribed original ring element
exactly when its actual whole inclusion is the SAME original differential times that element. -/
theorem coefficient_eq_originalRing_iff (q : ℚ) (a : R) :
    letI : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
        (⊤ : (Spec (.of R)).Opens)) :=
      ⟨⟨genericPoint (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, by trivial⟩⟩
    ∀ s : Γ(originalRoundedBPModule f n I hI q,
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
          (⊤ : (Spec (.of R)).Opens)),
      coefficient (F := F) f n I hI q _ s = algebraMap R F a ↔
        (originalRoundedBPInclusion f n I hI q).val.app (.op _) s =
          (RoundedCanonicalModule.differentialSection f
            (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op _)
              ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite.app ⊤
                ((Scheme.ΓSpecIso (.of R)).inv a)) := by
  let : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
      (⊤ : (Spec (.of R)).Opens)) :=
    ⟨⟨genericPoint (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, by trivial⟩⟩
  intro s
  have hc := BPRationalCanonicalSections.fractionCoefficient_originalRing (F := F) f n I hI a
  constructor
  · intro h
    apply BPRationalCanonicalSections.fractionCoefficient_injective (F := F) f n I hI _
    exact h.trans hc.symm
  · intro h
    exact (congrArg (BPRationalCanonicalSections.fractionCoefficient (F := F) f n I hI _) h).trans hc

end EnvelopeProperty.Char0.BPRoundedCanonicalCoefficients
