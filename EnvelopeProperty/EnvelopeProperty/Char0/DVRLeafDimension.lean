/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeDifferentialJacobian
import EnvelopeProperty.Char0.DVRJacobian
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Actual leaf fraction fields, divisorial coordinate ranks and valuation subrings

The common field and coordinate-index compatibility needed for the actual
DVR Jacobian adapter are produced internally from literal geometry.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open IsLocalRing Module
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Every literal intermediate algebra has the same actual fraction field as its root. -/
theorem isFractionRing_intermediate_subalgebra (C E : Subalgebra k K) (hCE : C ≤ E)
    [IsFractionRing C K] : IsFractionRing E K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective C z
  exact ⟨Subalgebra.inclusion hCE x, Subalgebra.inclusion hCE y, hxy.symm⟩

variable [CharZero k]

/-- The actual field differential bases produce the leaf/DVR coordinate index equivalence;
no dimension equality or separate matching-index premise is assumed. -/
def dvrLeafCoordinateIndexEquiv (E V : Subalgebra k K) [IsFractionRing E K]
    [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {ι : Type u} [Fintype ι] {π : V} (hπ : Irreducible π) {u : ι → V}
    (hu : IsTranscendenceBasis k (residue V ∘ u)) : Fin n ≃ Option ι := by
  have : Algebra.FormallyEtale E K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors E)
  exact (differentialBasisBaseChange (A := K) (etaleDifferentialBasis v hv)).indexEquiv
    (kaehlerBasisOfIsTranscendenceBasis (isTranscendenceBasis_dvrCoordinates hπ hu))

/-- The actual literal DVR underlying subring is an actual valuation subring of its
actual fraction field, without a separately supplied valuation or covering premise. -/
def actualDVRValuationSubring (V : Subalgebra k K)
    [IsDiscreteValuationRing V] [IsFractionRing V K] : ValuationSubring K :=
  ValuationSubring.ofSubring V.toSubring (by
    intro x
    obtain hx | hx := ValuationRing.isInteger_or_isInteger V x
    · obtain ⟨y, hy⟩ := hx
      exact Or.inl (hy ▸ y.2)
    · obtain ⟨y, hy⟩ := hx
      exact Or.inr (hy ▸ y.2))

end EnvelopeProperty.Char0
