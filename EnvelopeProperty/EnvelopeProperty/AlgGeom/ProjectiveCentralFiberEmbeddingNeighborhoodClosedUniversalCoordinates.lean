import EnvelopeProperty.AlgGeom.GeneratedTupleProjectiveCoordinates

/-! # The actual original universal coordinate tuple is its native chart inclusion -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
open GeneratedTupleProjectiveCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

private theorem coordinateTuple_span (i : Fin (m + 1)) :
    Ideal.span (Set.range (coordinateDehomCoord (R := R) i)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h : coordinateDehomCoord (R := R) i i ∈
      Ideal.span (Set.range (coordinateDehomCoord (R := R) i)) :=
    Ideal.subset_span (Set.mem_range_self i)
  rw [coordinateDehomCoord_self] at h
  exact h

variable [IsDomain R]

/-- The SAME native original unit-ideal tuple map of all actual original
coordinate ratios is the ORIGINAL native projective chart inclusion.
Its original unit-span and its entire original chart-ring identity are proved
internally from the actual coordinate polynomials. -/
theorem affineTupleMap_coordinateTuple (i : Fin (m + 1)) :
    affineTupleMap (algebraMap R (CoordinateRing R i)) (coordinateDehomCoord i)
        (coordinateTuple_span i) =
      DeJongAlterations.Geometry.Segre.coordinateChartInclusion i := by
  rw [affineTupleMap_eq_eval_chart _ _ _ i (coordinateDehomCoord_self i)]
  have he : MvPolynomial.eval₂Hom (algebraMap R (CoordinateRing R i))
      (fun a : ChartIndex i => coordinateDehomCoord i a.1) =
        RingHom.id (CoordinateRing R i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    · intro a
      rw [MvPolynomial.eval₂Hom_X']
      exact coordinateDehomCoord_ne i a
  rw [he, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
