import EnvelopeProperty.Algebra.RelativeResidueTranscendenceDegree

/-! # Actual relative curve fields keep the original nonzero central parameter -/
open IsLocalRing Cardinal
noncomputable section
universe u
namespace EnvelopeProperty.RelativeCoefficientParameterCurve

private theorem transcendental_of_nonzero_nonunit
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (V : Subalgebra F K) (t : V) (ht : t ≠ 0) (hnt : ¬IsUnit t) :
    Transcendental F (t : K) := by
  intro halg
  have hinv := V.inv_mem_of_algebraic halg
  have htK : (t : K) ≠ 0 := fun h => ht (Subtype.ext h)
  apply hnt
  refine IsUnit.of_mul_eq_one (⟨_,hinv⟩ : V) (Subtype.ext ?_)
  simp [mul_inv_cancel₀ htK]

/-- The SAME original nonzero nonunit parameter gives an ACTUAL curve field
when the SAME original ambient function field has transcendence degree two. -/
theorem trdeg_over_parameter
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (V : Subalgebra F K) (t : V) (ht : t ≠ 0) (hnt : ¬IsUnit t)
    (hK : Algebra.trdeg F K = 2) :
    Transcendental F (t : K) ∧
      Algebra.trdeg (IntermediateField.adjoin F ({(t : K)} : Set K)) K = 1 := by
  have htF := transcendental_of_nonzero_nonunit V t ht hnt
  let E := IntermediateField.adjoin F ({(t : K)} : Set K)
  have hrat : Algebra.trdeg F (RatFunc F) = 1 := by
    let : Algebra.IsAlgebraic (Polynomial F) (RatFunc F) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors _)
    have h := trdeg_add_eq F (Polynomial F) (A := RatFunc F)
    rw [trdeg_eq_zero (R := Polynomial F),add_zero,Polynomial.trdeg_of_isDomain] at h
    exact h.symm
  have hE : Algebra.trdeg F E = 1 :=
    (RatFunc.algEquivOfTranscendental (t : K) htF).trdeg_eq.symm.trans hrat
  have h := trdeg_add_eq F E (A := K)
  rw [hE,hK] at h
  refine ⟨htF,Cardinal.add_one_inj.mp ?_⟩
  simpa only [add_comm,show (2 : Cardinal) = 1 + 1 by norm_num] using h

/-- True finite relative residue lifts and the ORIGINAL parameter internally
produce an actual EFT curve function field over the actual E(t) inside SAME K. -/
theorem exists_relativeCoefficient_parameter_curve
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (V : Subalgebra k K) [IsDiscreteValuationRing V]
    [Algebra.EssFiniteType k V] [IsFractionRing V K]
    (L : Type u) [Field L] [Algebra k L] [Algebra L (ResidueField V)]
    [IsScalarTower k L (ResidueField V)] (hL : Algebra.trdeg k L = 1)
    (t : V) (ht : t ≠ 0) (hnt : ¬IsUnit t) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → V),
      IsTranscendenceBasis L (residue V ∘ u) ∧
      let E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
      E.toSubalgebra ≤ V ∧ Transcendental E (t : K) ∧
      Algebra.trdeg (IntermediateField.adjoin E ({(t : K)} : Set K)) K = 1 ∧
      Algebra.EssFiniteType (IntermediateField.adjoin E ({(t : K)} : Set K)) K := by
  obtain ⟨ι,hι,u,hu,hEV,_⟩ :=
    RelativeResidueCoefficientLifts.exists_relativeResidue_unit_lifts V L
  let := hι
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
  let V' := Char0.extendScalarsOfLE V E hEV
  let e := Char0.extendScalarsOfLEEquiv V E hEV
  let t' : V' := e t
  have ht' : t' ≠ 0 := fun h => ht (e.injective (h.trans (map_zero e).symm))
  have hnt' : ¬IsUnit t' := fun h => hnt (h.map e.symm.toMonoidHom)
  have hK : Algebra.trdeg E K = 2 := by
    rw [RelativeResidueTranscendenceDegree.trdeg_relativeFractionField V L u hu,hL]
    norm_num
  obtain ⟨htrans,hdim⟩ := trdeg_over_parameter V' t' ht' hnt' hK
  let : Algebra.EssFiniteType V' K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors V')
  let : Algebra.EssFiniteType E K := Algebra.EssFiniteType.comp E V' K
  refine ⟨ι,hι,u,hu,hEV,htrans,hdim,?_⟩
  exact Algebra.EssFiniteType.of_comp E (IntermediateField.adjoin E ({(t : K)} : Set K)) K

end EnvelopeProperty.RelativeCoefficientParameterCurve
