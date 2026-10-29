/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRMultiplierContribution
import EnvelopeProperty.Char0.DVRCoordinatePresentations

/-!
# Actual intrinsic valuative multiplier ideals

The intersection ranges over every actual essentially finite-type DVR
subalgebra of the actual original function field containing the original
source. Coordinates are produced internally and removed from the result.
No finite valuation family or multiplier-ideal property is assumed.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private structure FiniteDVRCoordinateData (V : Subalgebra k K)
    [IsDiscreteValuationRing V] where
  residueDimension : ℕ
  uniformizer : V
  residueCoordinates : ULift.{u} (Fin residueDimension) → V
  uniformizer_irreducible : Irreducible uniformizer
  residue_isTranscendenceBasis :
    IsTranscendenceBasis k (residue V ∘ residueCoordinates)

private def finiteDVRCoordinateData (V : Subalgebra k K)
    [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] : FiniteDVRCoordinateData V :=
  Classical.choice <| by
    obtain ⟨m, π, v, hπ, hv⟩ := exists_finite_dvr_coordinates (k := k) V
    exact ⟨⟨m, π, fun i => v i.down, hπ, hv.comp_equiv Equiv.ulift⟩⟩

variable [CharZero k] (C V : Subalgebra k K)
  [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
  (hCV : C ≤ V)

/-- The genuine all-original-source Jacobian ideal using internally produced actual
finite DVR coordinates; the following theorem removes every coordinate choice. -/
def intrinsicDVRSourceJacobianIdeal : Ideal V :=
  let d := finiteDVRCoordinateData V
  dvrOriginalSourceJacobianIdeal C V hCV d.uniformizer_irreducible
    d.residue_isTranscendenceBasis (Fintype.equivFin (Option (ULift.{u} (Fin d.residueDimension)))).symm

/-- The intrinsic ideal is exactly the original ideal for any actual finite coordinate
presentation, including arbitrary finite residue dimension and enumeration. -/
theorem intrinsicDVRSourceJacobianIdeal_eq {m n : ℕ} {π : V}
    {v : ULift.{u} (Fin m) → V} (hπ : Irreducible π)
    (hv : IsTranscendenceBasis k (residue V ∘ v))
    (e : Fin n ≃ Option (ULift.{u} (Fin m))) :
    intrinsicDVRSourceJacobianIdeal C V hCV =
      dvrOriginalSourceJacobianIdeal C V hCV hπ hv e := by
  exact dvrOriginalSourceJacobianIdeal_presentation_independent C V hCV
    (finiteDVRCoordinateData V).uniformizer_irreducible
    (finiteDVRCoordinateData V).residue_isTranscendenceBasis hπ hv
    (Fintype.equivFin (Option (ULift.{u} (Fin (finiteDVRCoordinateData V).residueDimension)))).symm e

/-- An actual intrinsic divisorial contribution with all coordinate choices internal. -/
def intrinsicDVRMultiplierContribution (I : Ideal C) (_hI : I ≠ ⊥) (q : ℚ) : Ideal C :=
  (IsLocalRing.maximalIdeal V ^
    (⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ -
      (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat)).comap
    (Subalgebra.inclusion hCV).toRingHom

/-- The intrinsic contribution recovers the actual cutoff for every genuine coordinate
presentation, rather than accepting choice independence as a premise. -/
theorem intrinsicDVRMultiplierContribution_eq {m n : ℕ} {π : V}
    {v : ULift.{u} (Fin m) → V} (hπ : Irreducible π)
    (hv : IsTranscendenceBasis k (residue V ∘ v))
    (e : Fin n ≃ Option (ULift.{u} (Fin m))) (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    intrinsicDVRMultiplierContribution C V hCV I hI q =
      dvrMultiplierContribution C V hCV hπ hv e I hI q := by
  unfold intrinsicDVRMultiplierContribution dvrMultiplierContribution
  rw [intrinsicDVRSourceJacobianIdeal_eq C V hCV hπ hv e]

/-- Exact strict-discrepancy membership in the internally constructed actual contribution. -/
theorem mem_intrinsicDVRMultiplierContribution_iff (I : Ideal C) (hI : I ≠ ⊥)
    (q : ℚ) (f : C) :
    f ∈ intrinsicDVRMultiplierContribution C V hCV I hI q ↔ f = 0 ∨
      q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) <
        ((addVal V (Subalgebra.inclusion hCV f)).toNat : ℚ) + 1 +
          (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat := by
  let d := finiteDVRCoordinateData V
  let e := (Fintype.equivFin (Option (ULift.{u} (Fin d.residueDimension)))).symm
  rw [intrinsicDVRMultiplierContribution_eq C V hCV d.uniformizer_irreducible
    d.residue_isTranscendenceBasis e I hI q,
    mem_dvrMultiplierContribution_iff_strict,
    intrinsicDVRSourceJacobianIdeal_eq C V hCV d.uniformizer_irreducible d.residue_isTranscendenceBasis e]

omit [CharZero k] [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] in
/-- All actual essentially finite-type divisorial DVRs of the original function field
containing the original source. This is the full geometric indexing set. -/
def divisorialDVRs : Set (Subalgebra k K) :=
  {W | C ≤ W ∧ IsDiscreteValuationRing W ∧ IsFractionRing W K ∧ Algebra.EssFiniteType k W}

/-- The actual valuative multiplier ideal: the intersection over every actual
essentially finite-type divisorial DVR of the original function field. -/
def valuativeMultiplierIdeal [IsFractionRing C K] (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) : Ideal C :=
  ⨅ D : divisorialDVRs C,
    letI := D.property.2.1
    letI := D.property.2.2.1
    letI := D.property.2.2.2
    intrinsicDVRMultiplierContribution C D.val D.property.1 I hI q

/-- The actual intrinsic original-source Jacobian order is finite, using the genuine
original function field rather than a supplied discrepancy bound. -/
theorem intrinsicDVRSourceJacobianIdeal_order_ne_top [IsFractionRing C K] :
    dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV) ≠ ⊤ := by
  let d := finiteDVRCoordinateData V
  let e := (Fintype.equivFin (Option (ULift.{u} (Fin d.residueDimension)))).symm
  rw [intrinsicDVRSourceJacobianIdeal_eq C V hCV d.uniformizer_irreducible
    d.residue_isTranscendenceBasis e]
  exact dvrOriginalSourceJacobianIdeal_order_ne_top V C hCV d.uniformizer_irreducible
    d.residue_isTranscendenceBasis e

omit [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V] in
/-- Membership in the actual ideal is exactly the strict discrepancy condition at
every actual essentially finite-type DVR of the original function field. -/
theorem mem_valuativeMultiplierIdeal_iff [IsFractionRing C K]
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C) :
    f ∈ valuativeMultiplierIdeal C I hI q ↔ ∀ D : divisorialDVRs C,
      letI := D.property.2.1
      letI := D.property.2.2.1
      letI := D.property.2.2.2
      f = 0 ∨ q * ((dvrIdealOrder (I.map (Subalgebra.inclusion D.property.1).toRingHom)).toNat : ℚ) <
        ((addVal D.val (Subalgebra.inclusion D.property.1 f)).toNat : ℚ) + 1 +
          (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C D.val D.property.1)).toNat := by
  simp only [valuativeMultiplierIdeal, Submodule.mem_iInf]
  apply forall_congr'
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  exact mem_intrinsicDVRMultiplierContribution_iff C D.val D.property.1 I hI q f

/-- The full actual valuative multiplier ideal is contained in the contribution at
each actual divisorial DVR, with no selected finite family supplied. -/
theorem valuativeMultiplierIdeal_le_contribution [IsFractionRing C K]
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal C I hI q ≤ intrinsicDVRMultiplierContribution C V hCV I hI q := by
  let D : divisorialDVRs C := ⟨V, hCV, inferInstance, inferInstance, inferInstance⟩
  exact iInf_le _ D

omit [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V] in
/-- Every original nonzero ideal is contained in its actual valuative multiplier ideal
at exponent one; the conclusion concerns the complete divisorial intersection. -/
theorem le_valuativeMultiplierIdeal_one [IsFractionRing C K]
    (I : Ideal C) (hI : I ≠ ⊥) : I ≤ valuativeMultiplierIdeal C I hI 1 := by
  apply le_iInf
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  let d := finiteDVRCoordinateData D.val
  let e := (Fintype.equivFin (Option (ULift.{u} (Fin d.residueDimension)))).symm
  rw [intrinsicDVRMultiplierContribution_eq C D.val D.property.1
    d.uniformizer_irreducible d.residue_isTranscendenceBasis e I hI 1]
  exact le_dvrMultiplierContribution_one C D.val D.property.1
    d.uniformizer_irreducible d.residue_isTranscendenceBasis e I hI

end EnvelopeProperty.Char0
