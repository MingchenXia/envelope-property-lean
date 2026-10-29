import EnvelopeProperty.Vanishing.NadelPrincipalizationGeometry
import Hironaka.Scheme.FiniteType

/-! # Original Nadel principalization over a finite-type affine base

The algebraic Hironaka triple requires separated finite type over the field.
Both properties follow from the original projective map to the original
finite-type affine base. The field structure map need not be proper.
The same original ideal and empty boundary produce the actual BP sequence;
its final scheme remains projective over the original affine base.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme.BlowUpSequence
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalization

section Algebraic
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- The original global algebraic triple; properness over the field is unnecessary. -/
def originalTriple : Triple k := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact
    { X := .ofHom f inferInstance inferInstance
      smoothOfRelativeDimension := ⟨n, by change SmoothOfRelativeDimension n f; infer_instance⟩
      I := I
      isNonzeroEverywhere := NadelPrincipalization.nonzeroEverywhere_of_generic I hI
      E := Scheme.DivisorFamily.empty X
      isSnc := isSnc_empty_of_smooth f }

variable [CharZero k]

/-- The actual BP principalization of the SAME original global ideal. -/
def sequence : X.BlowUpSequence := Hironaka.Sequence.BP (originalTriple f n I hI)

/-- Every actual original BP centre is smooth over the original field. -/
theorem sequence_isSmooth : (sequence f n I hI).IsSmooth f := by
  intro i
  exact (Hironaka.Sequence.BP_center_smooth_hasSncWith (originalTriple f n I hI) i).1

/-- The original absolute dimension persists through every actual stage. -/
theorem stage_smoothOfRelativeDimension (i : Fin ((sequence f n I hI).length + 1)) :
    SmoothOfRelativeDimension n ((sequence f n I hI).stageMap i ≫ f) :=
  IsSmooth.smoothOfRelativeDimension_stageMap (f := f) (n := n)
    (sequence_isSmooth f n I hI) i

/-- The full total transform of the original ideal is an SNC divisor ideal. -/
theorem totalTransform_isIdealOfSncDivisor :
    (I.comap (sequence f n I hI).composite).IsIdealOfSncDivisor :=
  Hironaka.Sequence.BP_isIdealOfSncDivisor (originalTriple f n I hI)

/-- The original BP is an isomorphism over the original ideal's unit locus. -/
theorem isIso_restrict_compl :
    IsIso ((sequence f n I hI).composite ∣_ I.support.compl) := by
  have h := Hironaka.Sequence.BP_isIso_restrict (originalTriple f n I hI)
  have hempty : (Scheme.DivisorFamily.empty X).singularLocus = ⊥ := by
    simp [Scheme.DivisorFamily.singularLocus, Scheme.DivisorFamily.empty]
  change IsIso ((sequence f n I hI).composite ∣_
    (I.support ⊔ (Scheme.DivisorFamily.empty X).singularLocus).compl) at h
  rw [hempty, sup_bot_eq] at h
  exact h

/-- Nonemptiness comes from the original generic point, not from resolution data. -/
theorem last_nonempty : Nonempty (sequence f n I hI).last := by
  let U := I.support.compl
  let : IsIso ((sequence f n I hI).composite ∣_ U) := isIso_restrict_compl f n I hI
  let : Nonempty U := ⟨⟨genericPoint X, NadelPrincipalization.genericPoint_mem_unitLocus I hI⟩⟩
  let : Nonempty ((sequence f n I hI).composite ⁻¹ᵁ U) :=
    Nonempty.map (inv ((sequence f n I hI).composite ∣_ U)) inferInstance
  exact Nonempty.map ((sequence f n I hI).composite ⁻¹ᵁ U).ι inferInstance

/-- The actual final scheme is integral, produced from the original generic nonvanishing. -/
theorem last_isIntegral : IsIntegral (sequence f n I hI).last := by
  let : Nonempty (sequence f n I hI).last := last_nonempty f n I hI
  exact ProjectiveStrongResolution.isIntegral_last (sequence f n I hI)

/-- The blowup composite is proper over X even when X is not proper over k. -/
theorem composite_isProper : IsProper (sequence f n I hI).composite := by
  let : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  exact (sequence f n I hI).isProper_composite

/-- The actual original dense open and its entire isomorphism restriction. -/
theorem exists_dense_isIso :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso ((sequence f n I hI).composite ∣_ U) :=
  ⟨I.support.compl, NadelPrincipalization.unitLocus_dense I hI,
    isIso_restrict_compl f n I hI⟩

end Algebraic

section Relative
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [hRft : Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (hp : IsProjectiveFactorization π)

include hRft hπ hp in
/-- Actual projectivity over a finite-type affine base produces finite type over k. -/
theorem structure_finiteType : FiniteType f := by
  let : IsProper π := hp.isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType k R))
  have h : FiniteType (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := inferInstance
  exact hπ ▸ h

include hπ hp in
omit hRft in
/-- The SAME original relative projectivity produces separatedness over k. -/
theorem structure_isSeparated : IsSeparated f := by
  let : IsProper π := hp.isProper
  have h : IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := inferInstance
  exact hπ ▸ h

variable [IsIntegral X] (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- The full relative hypotheses internally construct the SAME original algebraic triple. -/
def relativeTriple : Triple k := by
  let : FiniteType f := structure_finiteType f π hπ hp
  let : IsSeparated f := structure_isSeparated f π hπ hp
  exact originalTriple f n I hI

variable [CharZero k]

/-- The actual original relative BP; no global properness or supplied resolution. -/
def relativeSequence : X.BlowUpSequence := Hironaka.Sequence.BP (relativeTriple f π hπ hp n I hI)

/-- The actual final principalization retains projectivity over the SAME original R. -/
theorem relative_last_isProjectiveFactorization :
    IsProjectiveFactorization ((relativeSequence f π hπ hp n I hI).composite ≫ π) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact ProjectiveBlowupSequence.composite_isProjectiveFactorization
    (relativeSequence f π hπ hp n I hI) π hp

end Relative
end EnvelopeProperty.Vanishing.NadelRelativePrincipalization
