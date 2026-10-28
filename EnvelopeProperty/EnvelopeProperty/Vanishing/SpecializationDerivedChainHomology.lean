import EnvelopeProperty.Vanishing.SpecializationDerivedFiniteApproximation
import EnvelopeProperty.Vanishing.SpecializationOriginalFreeModules

/-! # Actual native chain homology specializes from a closed fibre

Finite free triples and their arbitrary-scalar comparisons are constructed
from the original flat complex and its finite native homology.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedFiniteApproximation

open SpecializationDerivedReplacementStep

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Finite R (C.homology n)]

/-- Actual native homology of the original scalar-extended chain complex
vanishes on a produced principal neighborhood of the original closed point. -/
theorem exists_chain_homology_zero_neighborhood
    (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hzero : IsZero (baseChangeComplex (segment C q) p.ResidueField).homology) :
    ∃ r : R, r ∉ p ∧ ∀ (K : Type u) [Field K] [Algebra R K],
      algebraMap R K r ≠ 0 →
        IsZero (baseChangeComplex (segment C q) K).homology := by
  let E := finiteFreeTriple C q
  have hfree : IsZero (SpecializationOriginalFreeModules.baseChangeComplex
      p.ResidueField E.incoming E.outgoing E.zero).homology :=
    hzero.of_iso (E.homology_baseChange p.ResidueField)
  obtain ⟨r, hr, hfield⟩ :=
    SpecializationOriginalFreeModules.exists_original_homology_zero_neighborhood p
      (Pi.basisFun R (Fin E.incomingRank)) (Pi.basisFun R (Fin E.middleRank))
      (Pi.basisFun R (Fin E.outgoingRank)) E.incoming E.outgoing E.zero hfree
  refine ⟨r, hr, fun K _ _ hK => ?_⟩
  exact (hfield K hK).of_iso (E.homology_baseChange K).symm

/-- Over the original domain, zero original residue homology implies zero
native homology after extension to the original fraction field. -/
theorem generic_chain_homology_isZero_of_closed_fibre [IsDomain R]
    (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hzero : IsZero (baseChangeComplex (segment C q) p.ResidueField).homology)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsZero (baseChangeComplex (segment C q) K).homology := by
  obtain ⟨r, hr, hfield⟩ := exists_chain_homology_zero_neighborhood C p q hzero
  apply hfield K
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm)
  exact hr (hrzero ▸ p.zero_mem)

end EnvelopeProperty.Vanishing.SpecializationDerivedFiniteApproximation
