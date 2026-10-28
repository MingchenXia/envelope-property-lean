import EnvelopeProperty.Char0.AffinePrincipalization
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence

/-! # The actual global principalization of the original Nadel ideal

The source scheme, its structure, pure dimension and original ideal are
retained. No resolution, model or multiplier comparison is an input.
The whole multiplier pushforward formula and local vanishing are separate.
-/

open AlgebraicGeometry CategoryTheory Scheme.BlowUpSequence

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalization

/-- Original generic nonvanishing implies actual nonvanishing at every stalk. -/
theorem nonzeroEverywhere_of_generic {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) :
    I.IsNonzeroEverywhere := by
  intro x hx
  exact hI (I.stalkIdeal_eq_bot_of_specializes (genericPoint_specializes x) hx)

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- Construct the original global triple internally, with its actual empty boundary. -/
def originalTriple : Triple k := by
  let : IsProper f := hp.isProper
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact
    { X := .ofHom f inferInstance inferInstance
      smoothOfRelativeDimension := ⟨n, by change SmoothOfRelativeDimension n f; infer_instance⟩
      I := I
      isNonzeroEverywhere := nonzeroEverywhere_of_generic I hI
      E := Scheme.DivisorFamily.empty X
      isSnc := isSnc_empty_of_smooth f }

variable [CharZero k]

/-- The actual finite algebraic BP sequence on the original whole scheme. -/
def sequence : X.BlowUpSequence := Hironaka.Sequence.BP (originalTriple f hp n I hI)

/-- Every actual centre is smooth over the original field. -/
theorem sequence_isSmooth : (sequence f hp n I hI).IsSmooth f := by
  intro i
  exact (Hironaka.Sequence.BP_center_smooth_hasSncWith (originalTriple f hp n I hI) i).1

/-- The same original dimension is preserved, including all intermediate stages. -/
theorem stage_smoothOfRelativeDimension (i : Fin ((sequence f hp n I hI).length + 1)) :
    SmoothOfRelativeDimension n ((sequence f hp n I hI).stageMap i ≫ f) :=
  IsSmooth.smoothOfRelativeDimension_stageMap (f := f) (n := n)
    (sequence_isSmooth f hp n I hI) i

/-- The actual original ideal's full total transform has SNC support. -/
theorem totalTransform_isIdealOfSncDivisor :
    (I.comap (sequence f hp n I hI).composite).IsIdealOfSncDivisor :=
  Hironaka.Sequence.BP_isIdealOfSncDivisor (originalTriple f hp n I hI)

/-- The last whole scheme has a constructed finite polynomial projective embedding. -/
theorem last_isProjectiveFactorization :
    IsProjectiveFactorization ((sequence f hp n I hI).composite ≫ f) :=
  ProjectiveBlowupSequence.composite_isProjectiveFactorization (sequence f hp n I hI) f hp

/-- The actual map is an isomorphism over the original ideal's unit locus. -/
theorem isIso_restrict_compl :
    IsIso ((sequence f hp n I hI).composite ∣_ I.support.compl) := by
  have h := Hironaka.Sequence.BP_isIso_restrict (originalTriple f hp n I hI)
  have hempty : (Scheme.DivisorFamily.empty X).singularLocus = ⊥ := by
    simp [Scheme.DivisorFamily.singularLocus, Scheme.DivisorFamily.empty]
  change IsIso ((sequence f hp n I hI).composite ∣_
    (I.support ⊔ (Scheme.DivisorFamily.empty X).singularLocus).compl) at h
  rw [hempty, sup_bot_eq] at h
  exact h

end EnvelopeProperty.Vanishing.NadelPrincipalization
