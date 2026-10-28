import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinatePreimages
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import DeJongAlterations.Geometry.ProjIntegral

/-! # The actual same mixed map is a closed immersion with its whole original twist -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateCharts
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateAlgebra
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinatePreimages
open GeneratedLineProjectiveMap SchemeGeneratedLineCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] [IsDomain R] {m : ℕ}

private instance mixedFamily_fintype (j : Fin (m + 1)) (d : ℕ) :
    Fintype (mixedCoordinateFamily (R := R) j d).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1) × Fin (m + 1))))

private def mixedChartMorphism (i : Fin (m + 1)) (d : ℕ) :
    Spec (.of (CoordinateRing R i)) ⟶ Spec (.of (CoordinateRing R (pairCoordinate.{u} i i))) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (algebraMap R (CoordinateRing R i))
      (fun a : ChartIndex (pairCoordinate.{u} i i) =>
        paddedCoefficients (mixedCoordinateTuple i d) a.1)))

omit [IsDomain R] in
private theorem mixedChartMorphism_closed (i : Fin (m + 1)) (d : ℕ) :
    IsClosedImmersion (mixedChartMorphism (R := R) i d) :=
  IsClosedImmersion.spec_of_surjective _ (mixedChartMap_surjective i d)

/-- The actual surjective polynomial chart is a genuine native Cartesian
chart of the SAME mixed generated map, using its internally proved whole preimage. -/
theorem mixedProjectiveMap_chart_isPullback (j i : Fin (m + 1)) (d : ℕ) :
    IsPullback (mixedChartMorphism (R := R) i d)
      (DeJongAlterations.Geometry.Segre.coordinateChartInclusion i)
      (DeJongAlterations.Geometry.Segre.coordinateChartInclusion (pairCoordinate.{u} i i))
      (projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
        (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
        (mixedCoordinateFamily (R := R) j d)) := by
  apply IsOpenImmersion.isPullback
  · let a := paddedCoefficients (mixedCoordinateTuple (R := R) i d)
    let ha : Ideal.span (Set.range a) = ⊤ :=
      span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span i d)
    have hdiag : a (pairCoordinate.{u} i i) = 1 := by
      simp only [a, pairCoordinate, paddedCoefficients, Fin.cases_succ,
        Equiv.symm_apply_apply, mixedCoordinateTuple, coordinateDehomCoord_self,
        one_pow, one_mul]
    have hc := GeneratedTupleProjectiveCoordinates.affineTupleMap_eq_eval_chart
      (algebraMap R (CoordinateRing R i)) a ha (pairCoordinate.{u} i i) hdiag
    have hm : DeJongAlterations.Geometry.Segre.coordinateChartInclusion i ≫
        projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
          (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
          (mixedCoordinateFamily (R := R) j d) =
        affineTupleMap (algebraMap R (CoordinateRing R i)) a ha :=
      (Category.assoc _ _ _).trans (mixedProjectiveMap_coordinateChart j i d)
    exact hm.trans hc
  · have ht : (DeJongAlterations.Geometry.Segre.coordinateChartInclusion
        (R := R) (pairCoordinate.{u} i i)).opensRange =
        nativeCoordinateOpen (R := R) (pairCoordinate.{u} i i) :=
      DeJongAlterations.Geometry.Segre.coordinateChartInclusion_opensRange _
    have hs : (DeJongAlterations.Geometry.Segre.coordinateChartInclusion
        (R := R) i).opensRange = coordinateOpen (R := R) i :=
      DeJongAlterations.Geometry.Segre.coordinateChartInclusion_opensRange _
    exact (congrArg (fun V => (projectiveMap
      (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
      (mixedCoordinateFamily (R := R) j d)) ⁻¹ᵁ V) ht).trans
        ((mixedProjectiveMap_preimage_diagonal j i d).trans hs.symm)

private theorem mixedProjectiveMap_diagonal_restrict_closed
    (j i : Fin (m + 1)) (d : ℕ) :
    let Φ := projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
      (mixedCoordinateFamily (R := R) j d)
    IsClosedImmersion (Φ ∣_ nativeCoordinateOpen (pairCoordinate.{u} i i)) := by
  let Φ := projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
    (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
    (mixedCoordinateFamily (R := R) j d)
  let c := DeJongAlterations.Geometry.Segre.coordinateChartInclusion (R := R)
    (pairCoordinate.{u} i i)
  have hcOpen : IsOpenImmersion c := by dsimp [c]; infer_instance
  have hp : IsClosedImmersion (pullback.snd Φ c) := by
    let h := (mixedProjectiveMap_chart_isPullback (R := R) j i d).flip
    have he : h.isoPullback.inv ≫ mixedChartMorphism (R := R) i d =
        pullback.snd Φ c := h.isoPullback_inv_snd
    have hc : IsClosedImmersion
        (h.isoPullback.inv ≫ mixedChartMorphism (R := R) i d) := by
      let : IsClosedImmersion (mixedChartMorphism (R := R) i d) :=
        mixedChartMorphism_closed i d
      infer_instance
    exact he ▸ hc
  have hr : IsClosedImmersion (Φ ∣_ c.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (@morphismRestrictOpensRange _ _ _ Φ c hcOpen)).mpr hp
  have ho : c.opensRange = nativeCoordinateOpen (R := R) (pairCoordinate.{u} i i) :=
    DeJongAlterations.Geometry.Segre.coordinateChartInclusion_opensRange _
  exact (congrArg (fun V => IsClosedImmersion (Φ ∣_ V)) ho).mp hr

/-- The SAME actual mixed generated projective map is a closed immersion.
Its local surjectivity, entire chart preimages and proper closed image are
all derived internally; the diagonal opens cover its image, not the entire target. -/
theorem mixedProjectiveMap_isClosedImmersion (j : Fin (m + 1)) (d : ℕ) :
    IsClosedImmersion (projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
      (mixedCoordinateFamily (R := R) j d)) := by
  let Φ := projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
    (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
    (mixedCoordinateFamily (R := R) j d)
  let V : Fin (m + 1) → (DeJongAlterations.projectiveSpace R
      (Fintype.card (mixedCoordinateFamily (R := R) j d).I)).Opens :=
    fun i => nativeCoordinateOpen (pairCoordinate.{u} i i)
  let : MorphismProperty.RespectsRight
      (@IsPreimmersion : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    { postcomp := fun i hi f hf => by
        let : IsOpenImmersion i := hi
        let : IsPreimmersion f := hf
        infer_instance }
  have hpre : IsPreimmersion Φ := by
    apply IsZariskiLocalAtTarget.of_range_subset_iSup V
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ ⨆ i : Fin (m + 1), coordinateOpen (R := R) i := by
        rw [iSup_coordinateOpen_eq_top]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      apply (TopologicalSpace.Opens.mem_iSup).mpr
      refine ⟨i, ?_⟩
      change x ∈ Φ ⁻¹ᵁ V i
      rw [mixedProjectiveMap_preimage_diagonal]
      exact hi
    · intro i
      let : IsClosedImmersion (Φ ∣_ V i) := mixedProjectiveMap_diagonal_restrict_closed j i d
      infer_instance
  let : IsPreimmersion Φ := hpre
  let q := DeJongAlterations.projectiveSpaceStructure R
    (Fintype.card (mixedCoordinateFamily (R := R) j d).I)
  have hproperComp : IsProper (Φ ≫ q) :=
    (projectiveMap_structure (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
      (mixedCoordinateFamily (R := R) j d)).symm ▸ inferInstance
  have hq : IsSeparated q := inferInstance
  let : IsProper Φ := @IsProper.of_comp _ _ _ Φ q hproperComp hq
  exact IsClosedImmersion.of_isPreimmersion Φ Φ.isClosedMap.isClosed_range

private theorem ambient_integral : IsIntegral (DeJongAlterations.projectiveSpace R m) := by
  apply DeJongAlterations.Geometry.ProjIntegral.isIntegral_proj
  intro h
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem
    (DeJongAlterations.projectiveSpaceGrading R m) (by decide : 0 < (1 : ℕ))
    (MvPolynomial.isHomogeneous_X R (0 : Fin (m + 1)))
  rw [h] at hx
  exact MvPolynomial.X_ne_zero (0 : Fin (m + 1)) hx

/-- The original positive twist is genuinely very ample via this SAME
actual closed mixed map and its native entire O(1) pullback isomorphism. -/
theorem mixedTwist_isVeryAmple (j : Fin (m + 1)) (d : ℕ) :
    SchemeLineAmpleness.IsVeryAmple (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ)) := by
  let : IsIntegral (DeJongAlterations.projectiveSpace R m) := ambient_integral
  let G := mixedCoordinateFamily (R := R) j d
  let hL := coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ)
  exact ⟨Fintype.card G.I,
    projectiveMap (DeJongAlterations.projectiveSpaceStructure R m) hL G,
    mixedProjectiveMap_isClosedImmersion j d,
    projectiveMap_structure (DeJongAlterations.projectiveSpaceStructure R m) hL G,
    ⟨GeneratedLineProjectiveTwist.projectiveTwistIso
      (DeJongAlterations.projectiveSpaceStructure R m) hL G 0⟩⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding
