import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients

/-! # The actual original finite coordinate family and its native zero padding -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
open SchemeGeneratedLineCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] {ι : Type u} [Fintype ι] {m : ℕ}

/-- The ACTUAL original padded variables define a genuine original graded map,
retaining the SAME original finite enumeration, over every commutative ring. -/
def paddingGradedMap (e : ι ≃ Fin (m + 1)) :
    projectiveSpaceGrading R (Fintype.card ι) →+*ᵍ projectiveSpaceGrading R m where
  __ := (MvPolynomial.aeval (paddedCoefficients (fun i : ι => (MvPolynomial.X (e i) :
    MvPolynomial (Fin (m + 1)) R)))).toRingHom
  map_mem {i p} hp := by
    change (MvPolynomial.aeval (paddedCoefficients (fun a : ι =>
      (MvPolynomial.X (e a) : MvPolynomial (Fin (m + 1)) R))) p).IsHomogeneous i
    change p.IsHomogeneous i at hp
    have hv (j : Fin (Fintype.card ι + 1)) :
        (paddedCoefficients (fun a : ι => (MvPolynomial.X (e a) :
          MvPolynomial (Fin (m + 1)) R)) j).IsHomogeneous 1 := by
      refine Fin.cases ?_ (fun a => ?_) j
      · change (0 : MvPolynomial (Fin (m + 1)) R).IsHomogeneous 1
        exact (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 1).zero_mem
      · exact MvPolynomial.isHomogeneous_X R (e ((Fintype.equivFin ι).symm a))
    simpa only [one_mul] using hp.aeval _ hv

/-- The SAME actual original presentation is surjective, via the original
variable renaming right inverse, without any projective-map certificate. -/
theorem paddingGradedMap_surjective (e : ι ≃ Fin (m + 1)) :
    Function.Surjective (paddingGradedMap R e) := by
  let s : Fin (m + 1) → Fin (Fintype.card ι + 1) :=
    fun j => ((Fintype.equivFin ι) (e.symm j)).succ
  intro p
  refine ⟨MvPolynomial.rename s p, ?_⟩
  change MvPolynomial.aeval (paddedCoefficients (fun i : ι =>
    (MvPolynomial.X (e i) : MvPolynomial (Fin (m + 1)) R))) (MvPolynomial.rename s p) = p
  rw [MvPolynomial.aeval_rename]
  have hc : paddedCoefficients (fun i : ι =>
      (MvPolynomial.X (e i) : MvPolynomial (Fin (m + 1)) R)) ∘ s = MvPolynomial.X := by
    funext j
    change MvPolynomial.X (e ((Fintype.equivFin ι).symm
      ((Fintype.equivFin ι) (e.symm j)))) = MvPolynomial.X j
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  exact (congrArg (fun a => MvPolynomial.aeval a p) hc).trans
    (MvPolynomial.aeval_X_left_apply p)

private theorem paddingGradedMap_X_zero (e : ι ≃ Fin (m + 1)) :
    paddingGradedMap R e (MvPolynomial.X (0 : Fin (Fintype.card ι + 1))) = 0 := by
  change MvPolynomial.aeval _ (MvPolynomial.X (0 : Fin (Fintype.card ι + 1))) = 0
  rw [MvPolynomial.aeval_X]
  rfl

private theorem paddingGradedMap_X_succ (e : ι ≃ Fin (m + 1)) (i : ι) :
    paddingGradedMap R e (MvPolynomial.X ((Fintype.equivFin ι) i).succ) =
      MvPolynomial.X (e i) := by
  change MvPolynomial.aeval _ (MvPolynomial.X ((Fintype.equivFin ι) i).succ) = _
  rw [MvPolynomial.aeval_X]
  change MvPolynomial.X (e ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i))) =
    MvPolynomial.X (e i)
  rw [Equiv.symm_apply_apply]

/-- Native Proj of the SAME actual original zero-padded presentation produces
the whole original projective padding map, with its own irrelevant containment. -/
def paddingMap (e : ι ≃ Fin (m + 1)) :
    projectiveSpace R m ⟶ projectiveSpace R (Fintype.card ι) :=
  Proj.map (paddingGradedMap R e)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _ (paddingGradedMap_surjective R e))

/-- The SAME actual original whole padding morphism is a closed immersion,
internally derived from its original polynomial surjection. -/
instance paddingMap_isClosedImmersion (e : ι ≃ Fin (m + 1)) :
    IsClosedImmersion (paddingMap R e) :=
  ProjClosedImmersion.isClosedImmersion_map _ (paddingGradedMap_surjective R e) _

/-- Its actual original coordinate opens retain the SAME original finite index;
the padded zero coordinate has empty inverse image. -/
theorem paddingMap_preimages (e : ι ≃ Fin (m + 1)) :
    paddingMap R e ⁻¹ᵁ coordinateOpen (R := R) (0 : Fin (Fintype.card ι + 1)) = ⊥ ∧
      ∀ i : ι, paddingMap R e ⁻¹ᵁ coordinateOpen (R := R) ((Fintype.equivFin ι) i).succ =
        coordinateOpen (R := R) (e i) := by
  constructor
  · change Proj.map _ _ ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading R (Fintype.card ι))
      (MvPolynomial.X (0 : Fin (Fintype.card ι + 1))) = ⊥
    rw [Proj.map_preimage_basicOpen, paddingGradedMap_X_zero, Proj.basicOpen_zero]
  · intro i
    change Proj.map _ _ ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading R (Fintype.card ι))
      (MvPolynomial.X ((Fintype.equivFin ι) i).succ) =
        Proj.basicOpen (projectiveSpaceGrading R m) (MvPolynomial.X (e i))
    rw [Proj.map_preimage_basicOpen, paddingGradedMap_X_succ]

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
