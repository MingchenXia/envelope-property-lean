import EnvelopeProperty.Algebra.RelativeResidueCoefficientLifts

/-! # Actual relative-basis containment forces a finite center residue extension -/
noncomputable section
universe u
namespace EnvelopeProperty.RelativeBasisCenterFinite
variable {L M N : Type u} [Field L] [Field M] [Field N]
  [Algebra L M] [Algebra M N] [Algebra L N] [IsScalarTower L M N]
  {ι : Type u} (u : ι → N) (hu : IsTranscendenceBasis L u)
  (hrange : ∀ i, u i ∈ Set.range (algebraMap M N))

include hu hrange

/-- If the actual intermediate center residue contains the genuine relative
basis, the original residue extension is algebraic with its SAME scalar map. -/
theorem isAlgebraic_of_relativeBasis_in_range : Algebra.IsAlgebraic M N := by
  let f := IsScalarTower.toAlgHom L M N
  let F := IntermediateField.adjoin L (Set.range u)
  let G := f.fieldRange
  have hle : F ≤ G := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i,rfl⟩
    exact hrange i
  have hle' : F.toSubalgebra ≤ G.toSubalgebra := hle
  let : Algebra.IsAlgebraic F N := hu.isAlgebraic_field
  have hG : Algebra.IsAlgebraic G N :=
    ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).tower_top_of_subalgebra_le hle'⟩
  apply (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    f.equivFieldRange.toRingEquiv (RingEquiv.refl N) ?_).mp hG
  ext a
  exact f.equivFieldRange_apply_coe a

/-- The SAME original residue extension is finite once actual essential
finite type and true relative-basis containment have been derived. -/
theorem finite_of_relativeBasis_in_range [Algebra.EssFiniteType L N] :
    FiniteDimensional M N := by
  let : Algebra.IsAlgebraic M N := isAlgebraic_of_relativeBasis_in_range u hu hrange
  let : Algebra.EssFiniteType M N := Algebra.EssFiniteType.of_comp L M N
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end EnvelopeProperty.RelativeBasisCenterFinite
