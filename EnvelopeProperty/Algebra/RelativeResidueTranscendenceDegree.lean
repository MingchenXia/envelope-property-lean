import EnvelopeProperty.Algebra.RelativeResidueCoefficientLifts

/-! # Genuine relative residue and fraction transcendence degrees -/
open IsLocalRing Cardinal
noncomputable section
universe u
namespace EnvelopeProperty.RelativeResidueTranscendenceDegree
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (V : Subalgebra k K) [IsDiscreteValuationRing V]
  (L : Type u) [Field L] [Algebra k L] [Algebra L (ResidueField V)]
  [IsScalarTower k L (ResidueField V)]
  {ι : Type u} [Finite ι] (u : ι → V)
  (hu : IsTranscendenceBasis L (residue V ∘ u))

/-- The actual relative coefficient field removes precisely the relative
residue transcendence degree, retaining the dimension of the ORIGINAL L. -/
theorem trdeg_relativeResidue :
    let E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
    let hEV : E.toSubalgebra ≤ V := Char0.adjoin_le_of_algebraicIndependent_residue
      (AlgebraicIndependent.restrictScalars (algebraMap k L).injective hu.1)
    Algebra.trdeg E (ResidueField (Char0.extendScalarsOfLE V E hEV)) =
      Algebra.trdeg k L := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
  have hk : AlgebraicIndependent k (residue V ∘ u) :=
    AlgebraicIndependent.restrictScalars (algebraMap k L).injective hu.1
  let hEV : E.toSubalgebra ≤ V := Char0.adjoin_le_of_algebraicIndependent_residue hk
  let V' := Char0.extendScalarsOfLE V E hEV
  change Algebra.trdeg E (ResidueField V') = Algebra.trdeg k L
  have hE : Algebra.trdeg k E = #ι := by
    have h := (Char0.algebraicIndependent_coe_of_residue (K := K) hk).aevalEquivField.lift_trdeg_eq
    rw [Char0.trdeg_fractionRing_mvPolynomial,Cardinal.lift_lift] at h
    exact (Cardinal.lift_inj.1 h).symm
  have hr : Algebra.trdeg L (ResidueField V) = #ι := hu.cardinalMk_eq_trdeg.symm
  have he : Algebra.trdeg k (ResidueField V') = Algebra.trdeg k (ResidueField V) := by
    exact (ResidueField.mapAlgEquiv (Char0.extendScalarsOfLEEquiv V E hEV)).trdeg_eq.symm
  let : FaithfulSMul E (ResidueField V') :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E _).injective
  have ht := trdeg_add_eq k E (A := ResidueField V')
  have htL := trdeg_add_eq k L (A := ResidueField V)
  rw [hE,he,← htL,hr] at ht
  exact (Cardinal.add_right_inj_of_lt_aleph0 (Cardinal.mk_lt_aleph0 : #ι < Cardinal.aleph0)).mp
    ((add_comm _ _).trans ht)

include hu

/-- The SAME actual fraction field has one extra transcendence degree over
the genuine lifted coefficient field, with no original-residue equality premise. -/
theorem trdeg_relativeFractionField [Algebra.EssFiniteType k V] [IsFractionRing V K] :
    Algebra.trdeg (IntermediateField.adjoin k (Set.range fun i => (u i : K))) K =
      Algebra.trdeg k L + 1 := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
  let hEV : E.toSubalgebra ≤ V := Char0.adjoin_le_of_algebraicIndependent_residue
    (AlgebraicIndependent.restrictScalars (algebraMap k L).injective hu.1)
  let V' := Char0.extendScalarsOfLE V E hEV
  have h := Char0.trdeg_residueField_add_one V'
  rw [trdeg_relativeResidue V L u hu] at h
  exact h.symm

end EnvelopeProperty.RelativeResidueTranscendenceDegree
