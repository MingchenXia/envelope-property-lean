import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateFamily
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPaddingNaturality
import EnvelopeProperty.Alterations.Geometry.SegreGluing

/-! # The SAME actual original coordinate-generated map is the actual closed zero padding -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open Alterations.Geometry.ProjectiveIdeal
open Alterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateMap
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedPaddingNaturality
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap GeneratedLineLocalCoefficients
open SchemeGeneratedLineCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

private def coordinateFamilyEquiv (j : Fin (m + 1)) :
    (coordinateFamily (R := R) j).I ≃ Fin (m + 1) where
  toFun := ULift.down
  invFun := ULift.up
  left_inv a := by cases a; rfl
  right_inv _ := rfl

private theorem coordinateTuple_span (i : Fin (m + 1)) :
    Ideal.span (Set.range (coordinateDehomCoord (R := R) i)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h : coordinateDehomCoord (R := R) i i ∈
      Ideal.span (Set.range (coordinateDehomCoord (R := R) i)) :=
    Ideal.subset_span (Set.mem_range_self i)
  rw [coordinateDehomCoord_self] at h
  exact h

variable [IsDomain R]

private theorem chartFactor_eq_inverse (i : Fin (m + 1)) :
    GeneratedTupleTwistSections.chartFactor (algebraMap R (CoordinateRing R i))
        (coordinateDehomCoord i) (coordinateTuple_span i) i (coordinateDehomCoord_self i) =
      (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv := by
  apply (cancel_mono (coordinateOpen (R := R) i).ι).mp
  exact (GeneratedTupleTwistSections.chartFactor_comp _ _ _ _ _).trans
    (affineTupleMap_coordinateTuple i)

private theorem inverseChart_coefficient (i a : Fin (m + 1)) :
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv.appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X a)
          (MvPolynomial.isHomogeneous_X R a))) =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv.hom (coordinateDehomCoord i a) := by
  have h := GeneratedTupleTwistSections.chartFactor_coordinate
    (algebraMap R (CoordinateRing R i)) (coordinateDehomCoord i) (coordinateTuple_span i)
    i (coordinateDehomCoord_self i) a
  rw [chartFactor_eq_inverse] at h
  exact h

private theorem localMap_inverseChart (j i : Fin (m + 1)) :
    let G := coordinateFamily (R := R) j
    let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
      ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
    let E := pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j 1) U.1
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j 1)
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv ≫
        localMap (Alterations.projectiveSpaceStructure R m) G U E =
      Alterations.Geometry.Segre.coordinateChartInclusion i ≫
        paddingMap R (coordinateFamilyEquiv j) := by
  let G := coordinateFamily (R := R) j
  let V := coordinateOpen (R := R) i
  let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
    ⟨V, coordinateOpen_isAffineOpen i⟩
  let : IsAffine (coordinateOpen (R := R) i).toScheme := coordinateOpen_isAffineOpen i
  let E := pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j 1) V
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j 1)
  let c := Alterations.Geometry.Segre.coordinateChartIso (R := R) i
  let q : Γ(V.toScheme, ⊤) →+* CoordinateRing R i :=
    (Scheme.ΓSpecIso (.of (CoordinateRing R i))).hom.hom.comp c.inv.appTop.hom
  let p := Alterations.projectiveSpaceStructure R m
  let r := baseCoefficients (V.ι ≫ p)
  let b := localCoefficient G V E
  let e := coordinateFamilyEquiv (R := R) j
  let a := coordinateDehomCoord (R := R) i
  have hcoeff : ∀ t : G.I, q (b t) = a (e t) := by
    intro t
    have hc : b t = V.topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X t.down)
          (MvPolynomial.isHomogeneous_X R t.down)) :=
      coordinateFamily_localCoefficient (R := R) j i t
    have hh : q (V.topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X t.down)
          (MvPolynomial.isHomogeneous_X R t.down))) = a (e t) :=
      (congrArg (Scheme.ΓSpecIso (.of (CoordinateRing R i))).hom.hom
        (inverseChart_coefficient i t.down)).trans
          (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (CoordinateRing R i))) (a t.down))
    exact (congrArg q hc).trans hh
  have hiso : Spec.map (CommRingCat.ofHom q) = c.inv ≫ V.toScheme.isoSpec.hom := by
    have h := Scheme.isoSpec_hom_naturality c.inv
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp] at h
    exact h
  have hqr : q.comp r = algebraMap R (CoordinateRing R i) := by
    have hbase := baseCoefficients_structure (V.ι ≫ p)
    have hstructure : c.inv ≫ (V.ι ≫ p) =
        Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R i))) :=
      (Category.assoc _ _ _).symm.trans
        (Alterations.Geometry.Segre.coordinateChartInclusion_structure (R := R) i)
    have hmap : Spec.map (CommRingCat.ofHom (q.comp r)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R i))) := by
      change Spec.map (CommRingCat.ofHom r ≫ CommRingCat.ofHom q) = _
      rw [Spec.map_comp]
      exact (congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom r)) hiso).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => c.inv ≫ f) hbase).trans hstructure))
    exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of (CoordinateRing R i) => h.hom)
      (Spec.map_injective hmap)
  let hb : Ideal.span (Set.range (paddedCoefficients b)) = ⊤ :=
    span_paddedCoefficients_eq_top b
      (span_coefficients_eq_top (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.ι G) E)
  have hspan : Ideal.span (Set.range (fun t : G.I => a (e t))) = ⊤ := by
    have hr : Set.range (fun t : G.I => a (e t)) = Set.range a := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨e t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨e.symm t, congrArg a (e.apply_symm_apply t)⟩
    exact (congrArg Ideal.span hr).trans (coordinateTuple_span (R := R) i)
  let ht : Ideal.span (Set.range (paddedCoefficients (fun t : G.I => a (e t)))) = ⊤ :=
    span_paddedCoefficients_eq_top _ hspan
  have hc : paddedCoefficients (fun t : G.I => a (e t)) =
      fun t => q (paddedCoefficients b t) :=
    (congrArg paddedCoefficients (funext hcoeff)).symm.trans (paddedCoefficients_map b q)
  have hbq : Ideal.span (Set.range (fun t => q (paddedCoefficients b t))) = ⊤ := by
    rw [← hc]
    exact ht
  have hn := affineTupleMap_naturality r (paddedCoefficients b) hb q hbq
  have he := affineTupleMap_congr hqr hc.symm hbq ht
  have hp : affineTupleMap (algebraMap R (CoordinateRing R i))
        (paddedCoefficients (fun t : G.I => a (e t))) ht =
      affineTupleMap (algebraMap R (CoordinateRing R i)) a (coordinateTuple_span i) ≫
        paddingMap R e :=
    (affineTupleMap_comp_padding _ a (coordinateTuple_span i) e).symm
  let F := affineTupleMap r (paddedCoefficients b) hb
  have hfinal : c.inv ≫ (V.toScheme.isoSpec.hom ≫ F) =
      Alterations.Geometry.Segre.coordinateChartInclusion i ≫ paddingMap R e :=
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ F) hiso.symm).trans
        (hn.trans (he.trans (hp.trans (congrArg (fun f => f ≫ paddingMap R e)
          (affineTupleMap_coordinateTuple i)))))))
  exact hfinal

/-- The ENTIRE actual original generated projective map of the SAME actual
original homogeneous coordinate family is the SAME actual closed zero padding.
All original coefficient and whole-map comparisons are derived internally. -/
theorem coordinateProjectiveMap_eq_padding (j : Fin (m + 1)) :
    projectiveMap (Alterations.projectiveSpaceStructure R m)
        (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j) =
      paddingMap R (coordinateFamilyEquiv j) := by
  apply (Alterations.Geometry.Segre.coordinateCover R m).hom_ext
  intro i
  change Fin (m + 1) at i
  let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let E := pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j 1) U.1
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j 1)
  have h := projectiveMap_on_frame (Alterations.projectiveSpaceStructure R m)
    (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j) U E
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv ≫ f) h).trans
      (localMap_inverseChart j i))

/-- Closed immersion holds for this SAME actual original generated coordinate
map, with no incoming map equality, chart map or closedness certificate. -/
theorem coordinateProjectiveMap_isClosedImmersion (j : Fin (m + 1)) :
    IsClosedImmersion (projectiveMap (Alterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j)) := by
  rw [coordinateProjectiveMap_eq_padding]
  exact paddingMap_isClosedImmersion R (coordinateFamilyEquiv j)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateMap
