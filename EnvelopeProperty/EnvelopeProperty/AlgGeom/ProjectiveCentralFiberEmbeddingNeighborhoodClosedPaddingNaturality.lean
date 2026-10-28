import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
import EnvelopeProperty.AlgGeom.GeneratedTupleProjectiveCoordinates

/-! # The same original affine tuple morphism commutes with actual zero padding -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open DeJongAlterations DeJongAlterations.Geometry
open DeJongAlterations.Geometry.FiniteProjective
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding
open DeJongAlterations.Geometry.UnitIdealBlowup
open DeJongAlterations.Algebra.ReesPresentation
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPaddingNaturality
open SchemeGeneratedLineCoefficients GeneratedTupleProjectiveCoordinates
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ} {ι : Type u}

private theorem relabeled_span (a : Fin (m + 1) → A) (ha : Ideal.span (Set.range a) = ⊤)
    (e : ι ≃ Fin (m + 1)) : Ideal.span (Set.range (fun i : ι => a (e i))) = ⊤ := by
  have h : Set.range (fun i : ι => a (e i)) = Set.range a := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, congrArg a (e.apply_symm_apply j)⟩
  exact (congrArg Ideal.span h).trans ha

variable [Fintype ι]

private theorem padded_span (a : Fin (m + 1) → A) (ha : Ideal.span (Set.range a) = ⊤)
    (e : ι ≃ Fin (m + 1)) :
    Ideal.span (Set.range (paddedCoefficients (fun i : ι => a (e i)))) = ⊤ :=
  span_paddedCoefficients_eq_top _ (relabeled_span a ha e)

private theorem paddingGradedMap_C (e : ι ≃ Fin (m + 1)) (c : R) :
    paddingGradedMap R e (MvPolynomial.C c) = MvPolynomial.C c := by
  change MvPolynomial.aeval _ (MvPolynomial.C c) = MvPolynomial.C c
  rw [MvPolynomial.aeval_C]
  rfl

private theorem paddingGradedMap_X (e : ι ≃ Fin (m + 1)) (j : Fin (Fintype.card ι + 1)) :
    paddingGradedMap R e (MvPolynomial.X j) =
      paddedCoefficients (fun i : ι => (MvPolynomial.X (e i) : MvPolynomial (Fin (m + 1)) R)) j := by
  change MvPolynomial.aeval _ (MvPolynomial.X j) = _
  rw [MvPolynomial.aeval_X]

private theorem tupleGradedMap_C (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (c : R) :
    tupleGradedMap r a ha (MvPolynomial.C c) = algebraMap A (reesAlgebra (⊤ : Ideal A)) (r c) := by
  change reesPolynomialEval ⊤ a _ (MvPolynomial.map r (MvPolynomial.C c)) = _
  rw [MvPolynomial.map_C, reesPolynomialEval, MvPolynomial.aeval_C]

private theorem tuple_padding_graded (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (e : ι ≃ Fin (m + 1)) :
    (tupleGradedMap r a ha).comp (paddingGradedMap R e) =
      tupleGradedMap r (paddedCoefficients (fun i : ι => a (e i))) (padded_span a ha e) := by
  have h : ((tupleGradedMap r a ha).comp (paddingGradedMap R e)).toRingHom =
      (tupleGradedMap r (paddedCoefficients (fun i : ι => a (e i)))
        (padded_span a ha e)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change tupleGradedMap r a ha (paddingGradedMap R e (MvPolynomial.C c)) =
        tupleGradedMap r (paddedCoefficients (fun i : ι => a (e i)))
          (padded_span a ha e) (MvPolynomial.C c)
      rw [paddingGradedMap_C, tupleGradedMap_C, tupleGradedMap_C]
    · intro j
      change tupleGradedMap r a ha (paddingGradedMap R e (MvPolynomial.X j)) =
        tupleGradedMap r (paddedCoefficients (fun i : ι => a (e i)))
          (padded_span a ha e) (MvPolynomial.X j)
      rw [paddingGradedMap_X, tupleGradedMap_X]
      refine Fin.cases ?_ (fun i => ?_) j
      · change tupleGradedMap r a ha 0 = reesDegreeOne (⊤ : Ideal A) 0 (by trivial)
        rw [map_zero]
        apply Subtype.ext
        change (0 : Polynomial A) = Polynomial.monomial 1 0
        simp only [map_zero]
      · change tupleGradedMap r a ha (MvPolynomial.X (e ((Fintype.equivFin ι).symm i))) = _
        rw [tupleGradedMap_X]
        rfl
  exact GradedRingHom.ext (RingHom.congr_fun h)

/-- The WHOLE actual original affine tuple map followed by the SAME original
zero-padding map equals the actual native map for its SAME original relabeled
and padded tuple. Its original unit-span proof is internally derived. -/
theorem affineTupleMap_comp_padding (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (e : ι ≃ Fin (m + 1)) :
    affineTupleMap r a ha ≫ paddingMap R e =
      affineTupleMap r (paddedCoefficients (fun i : ι => a (e i))) (padded_span a ha e) := by
  let hp := ProjClosedImmersion.irrelevant_le_map_of_surjective _ (paddingGradedMap_surjective R e)
  let ht := tupleGradedMap_irrelevant r a ha
  have hc := Proj.map_comp (paddingGradedMap R e) (tupleGradedMap r a ha) hp ht
  have he := projMap_congr (tuple_padding_graded r a ha e)
    (HomogeneousIdeal.irrelevant_le_map_comp hp ht)
    (tupleGradedMap_irrelevant r (paddedCoefficients (fun i : ι => a (e i))) (padded_span a ha e))
  have hn := congrArg (fun f => f ≫ paddingMap R e) (affineTupleMap_graded r a ha)
  exact hn.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun f => (unitIdealBlowupIso A).inv ≫ f) hc.symm).trans
      ((congrArg (fun f => (unitIdealBlowupIso A).inv ≫ f) he).trans
        (affineTupleMap_graded r (paddedCoefficients (fun i : ι => a (e i)))
          (padded_span a ha e)).symm)))

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPaddingNaturality
