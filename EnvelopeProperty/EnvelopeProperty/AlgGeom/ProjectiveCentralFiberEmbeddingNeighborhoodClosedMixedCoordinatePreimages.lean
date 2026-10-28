import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateCharts
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateAlgebra
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveAffineCharts

/-! # Entire actual diagonal preimages of the same mixed generated map -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinatePreimages
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateCharts
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateAlgebra
open GeneratedLineProjectiveMap SchemeGeneratedLineCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] [IsDomain R] {m : ℕ}

private instance mixedFamily_fintype (j : Fin (m + 1)) (d : ℕ) :
    Fintype (mixedCoordinateFamily (R := R) j d).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1) × Fin (m + 1))))

/-- The WHOLE inverse image of each actual target diagonal coordinate open
under the SAME native mixed generated map is the original coordinate open.
No preimage, matching or chart certificate is supplied. -/
theorem mixedProjectiveMap_preimage_diagonal (j i : Fin (m + 1)) (d : ℕ) :
    projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
        (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
        (mixedCoordinateFamily (R := R) j d) ⁻¹ᵁ
        (nativeCoordinateOpen (pairCoordinate.{u} i i) :
          (DeJongAlterations.projectiveSpace R
            (Fintype.card (mixedCoordinateFamily (R := R) j d).I)).Opens) =
      coordinateOpen (R := R) i := by
  let Φ := projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
    (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
    (mixedCoordinateFamily (R := R) j d)
  ext x
  obtain ⟨k, y, rfl⟩ := (DeJongAlterations.Geometry.Segre.coordinateCover R m).exists_eq x
  change Fin (m + 1) at k
  change (Spec (.of (CoordinateRing R k)) : Type u) at y
  change y ∈ (DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ≫ Φ) ⁻¹ᵁ
      nativeCoordinateOpen (pairCoordinate.{u} i i) ↔
    y ∈ DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ⁻¹ᵁ
      coordinateOpen (R := R) i
  have hchart : DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ≫ Φ =
      affineTupleMap (algebraMap R (CoordinateRing R k))
        (paddedCoefficients (mixedCoordinateTuple k d))
        (span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span k d)) :=
    (Category.assoc _ _ _).trans (mixedProjectiveMap_coordinateChart j k d)
  let a := paddedCoefficients (mixedCoordinateTuple (R := R) k d)
  let ha : Ideal.span (Set.range a) = ⊤ :=
    span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span k d)
  let T : (DeJongAlterations.projectiveSpace R
      (Fintype.card (mixedCoordinateFamily (R := R) j d).I)).Opens :=
    nativeCoordinateOpen (pairCoordinate.{u} i i)
  have hpre : affineTupleMap (algebraMap R (CoordinateRing R k)) a ha ⁻¹ᵁ T =
      (PrimeSpectrum.basicOpen (a (pairCoordinate.{u} i i)) :
        (Spec (.of (CoordinateRing R k))).Opens) :=
    affineTupleMap_preimage_coordinate _ _ _ _
  have hright : DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ⁻¹ᵁ
      coordinateOpen (R := R) i =
      (PrimeSpectrum.basicOpen (coordinateDehomCoord (R := R) k i) :
        (Spec (.of (CoordinateRing R k))).Opens) :=
    DeJongAlterations.Geometry.Segre.coordinateChartInclusion_preimage_coordinate k i
  have hdiag : paddedCoefficients (mixedCoordinateTuple (R := R) k d)
      (pairCoordinate.{u} i i) = coordinateDehomCoord (R := R) k i ^ (d + 1) := by
    simp only [pairCoordinate, paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply,
      mixedCoordinateTuple]
    exact (pow_succ _ _).symm
  have hb : (PrimeSpectrum.basicOpen (a (pairCoordinate.{u} i i)) :
      (Spec (.of (CoordinateRing R k))).Opens) =
      PrimeSpectrum.basicOpen (coordinateDehomCoord (R := R) k i) :=
    (congrArg (fun z : CoordinateRing R k =>
      (PrimeSpectrum.basicOpen z : (Spec (.of (CoordinateRing R k))).Opens)) hdiag).trans
        (PrimeSpectrum.basicOpen_pow _ (d + 1) (Nat.succ_pos d))
  have hopen : (DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ≫ Φ) ⁻¹ᵁ T =
      DeJongAlterations.Geometry.Segre.coordinateChartInclusion k ⁻¹ᵁ
        coordinateOpen (R := R) i :=
    (congrArg (fun f => f ⁻¹ᵁ T) hchart).trans (hpre.trans (hb.trans hright.symm))
  exact Iff.of_eq (congrArg (fun U : (Spec (.of (CoordinateRing R k))).Opens => y ∈ U) hopen)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinatePreimages
