import EnvelopeProperty.Char0.ResidueTrdeg
import Mathlib.FieldTheory.FinTrdeg

/-! # Actual finite relative residue bases lift to genuine unit coefficient subfields -/
open IsLocalRing
noncomputable section
universe u
namespace EnvelopeProperty.RelativeResidueCoefficientLifts
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (V : Subalgebra k K) [IsLocalRing V] [Algebra.EssFiniteType k V]
    (L : Type u) [Field L] [Algebra k L] [Algebra L (ResidueField V)]
    [IsScalarTower k L (ResidueField V)]

/-- Derive ACTUAL finite relative residue basis lifts, containment of the TRUE
coefficient field in the SAME original local ring, and the actual finite
residue-field extension. No lift of the original center field L is assumed. -/
theorem exists_relativeResidue_unit_lifts :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → V),
      IsTranscendenceBasis L (residue V ∘ u) ∧
      (IntermediateField.adjoin k (Set.range fun i => (u i : K))).toSubalgebra ≤ V ∧
      FiniteDimensional (IntermediateField.adjoin L (Set.range (residue V ∘ u))) (ResidueField V) := by
  let : Algebra.EssFiniteType k (ResidueField V) :=
    inferInstanceAs (Algebra.EssFiniteType k (V ⧸ maximalIdeal V))
  let : Algebra.EssFiniteType L (ResidueField V) := Algebra.EssFiniteType.of_comp k L _
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis L (ResidueField V)
  let : Finite s := finite_of_isTranscendenceBasis hs
  choose u hu using fun x : s => residue_surjective (R := V) (x : ResidueField V)
  have hres : residue V ∘ u = ((↑) : s → ResidueField V) := funext hu
  have hb : IsTranscendenceBasis L (residue V ∘ u) := hres ▸ hs
  have hk : AlgebraicIndependent k (residue V ∘ u) :=
    AlgebraicIndependent.restrictScalars (algebraMap k L).injective hb.1
  refine ⟨s,inferInstance,u,hb,Char0.adjoin_le_of_algebraicIndependent_residue hk,?_⟩
  let E := IntermediateField.adjoin L (Set.range (residue V ∘ u))
  let : Algebra.IsAlgebraic E (ResidueField V) := hb.isAlgebraic_field
  let : Algebra.EssFiniteType E (ResidueField V) := Algebra.EssFiniteType.of_comp L E _
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end EnvelopeProperty.RelativeResidueCoefficientLifts
