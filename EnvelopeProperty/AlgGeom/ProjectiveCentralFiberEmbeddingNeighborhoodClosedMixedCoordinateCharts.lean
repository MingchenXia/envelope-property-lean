import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedFractions
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections
import EnvelopeProperty.Alterations.Geometry.SegreGluing

/-! # Actual entire affine charts of the same mixed generated projective map -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open Alterations.Geometry.ProjectiveIdeal
open Alterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateCharts
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedFractions
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedUniversalCoordinates
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap GeneratedLineLocalCoefficients
open SchemeGeneratedLineCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

/-- The actual mixed ratios in the original polynomial coordinate chart. -/
def mixedCoordinateTuple (i : Fin (m + 1)) (d : ℕ) :
    ULift.{u} (Fin (m + 1) × Fin (m + 1)) → CoordinateRing R i :=
  fun a => coordinateDehomCoord i a.down.1 ^ d * coordinateDehomCoord i a.down.2

/-- The actual diagonal coordinate is one, so this actual tuple spans the unit ideal. -/
theorem mixedCoordinateTuple_span (i : Fin (m + 1)) (d : ℕ) :
    Ideal.span (Set.range (mixedCoordinateTuple (R := R) i d)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h : mixedCoordinateTuple (R := R) i d (ULift.up (i, i)) ∈
      Ideal.span (Set.range (mixedCoordinateTuple (R := R) i d)) :=
    Ideal.subset_span (Set.mem_range_self (ULift.up (i, i)))
  have hone : mixedCoordinateTuple (R := R) i d (ULift.up (i, i)) = 1 := by
    simp only [mixedCoordinateTuple, coordinateDehomCoord_self, one_pow, one_mul]
  rw [hone] at h
  exact h

private instance mixedFamily_fintype (j : Fin (m + 1)) (d : ℕ) :
    Fintype (mixedCoordinateFamily (R := R) j d).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1) × Fin (m + 1))))

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

private theorem inverseChart_mixedCoefficient (i a b : Fin (m + 1)) (d : ℕ) :
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv.appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i (d + 1)
          (MvPolynomial.X a ^ d * MvPolynomial.X b)
          ((MvPolynomial.isHomogeneous_X_pow (R := R) a d).mul
            (MvPolynomial.isHomogeneous_X R b)))) =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv.hom
        (coordinateDehomCoord i a ^ d * coordinateDehomCoord i b) := by
  simp only [coefficient_mixed, map_mul, map_pow, inverseChart_coefficient]

private theorem localMap_inverseChart (j i : Fin (m + 1)) (d : ℕ) :
    let G := mixedCoordinateFamily (R := R) j d
    let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
      ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
    let E := pullbackIsoOfRestrictIso
      (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ)) U.1
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j (d + 1))
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv ≫
        localMap (Alterations.projectiveSpaceStructure R m) G U E =
      affineTupleMap (algebraMap R (CoordinateRing R i))
        (paddedCoefficients (mixedCoordinateTuple i d))
        (span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span i d)) := by
  let G := mixedCoordinateFamily (R := R) j d
  let V := coordinateOpen (R := R) i
  let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
    ⟨V, coordinateOpen_isAffineOpen i⟩
  let : IsAffine V.toScheme := coordinateOpen_isAffineOpen i
  let E := pullbackIsoOfRestrictIso
    (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ)) V
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j (d + 1))
  let c := Alterations.Geometry.Segre.coordinateChartIso (R := R) i
  let q : Γ(V.toScheme, ⊤) →+* CoordinateRing R i :=
    (Scheme.ΓSpecIso (.of (CoordinateRing R i))).hom.hom.comp c.inv.appTop.hom
  let p := Alterations.projectiveSpaceStructure R m
  let r := baseCoefficients (V.ι ≫ p)
  let b := localCoefficient G V E
  let a := mixedCoordinateTuple (R := R) i d
  have hcoeff : ∀ t : G.I, q (b t) = a t := by
    intro t
    have hc := mixedCoordinateFamily_localCoefficient (R := R) j i d t
    have hh : q (V.topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i (d + 1)
          (MvPolynomial.X t.down.1 ^ d * MvPolynomial.X t.down.2)
          ((MvPolynomial.isHomogeneous_X_pow (R := R) t.down.1 d).mul
            (MvPolynomial.isHomogeneous_X R t.down.2)))) = a t :=
      (congrArg (Scheme.ΓSpecIso (.of (CoordinateRing R i))).hom.hom
        (inverseChart_mixedCoefficient i t.down.1 t.down.2 d)).trans
          (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (CoordinateRing R i))) (a t))
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
  let ht : Ideal.span (Set.range (paddedCoefficients a)) = ⊤ :=
    span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span i d)
  have hc : paddedCoefficients a = fun t => q (paddedCoefficients b t) :=
    (congrArg paddedCoefficients (funext hcoeff)).symm.trans (paddedCoefficients_map b q)
  have hbq : Ideal.span (Set.range (fun t => q (paddedCoefficients b t))) = ⊤ := by
    rw [← hc]
    exact ht
  have hn := affineTupleMap_naturality r (paddedCoefficients b) hb q hbq
  have he := affineTupleMap_congr hqr hc.symm hbq ht
  let F := affineTupleMap r (paddedCoefficients b) hb
  have hfinal : c.inv ≫ (V.toScheme.isoSpec.hom ≫ F) =
      affineTupleMap (algebraMap R (CoordinateRing R i)) (paddedCoefficients a) ht :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ F) hiso.symm).trans (hn.trans he))
  exact hfinal

/-- The SAME whole native mixed generated map has this actual tuple map on
every original entire affine coordinate chart. No chart matching is input. -/
theorem mixedProjectiveMap_coordinateChart (j i : Fin (m + 1)) (d : ℕ) :
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv ≫
        (coordinateOpen (R := R) i).ι ≫
        projectiveMap (Alterations.projectiveSpaceStructure R m)
          (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
          (mixedCoordinateFamily (R := R) j d) =
      affineTupleMap (algebraMap R (CoordinateRing R i))
        (paddedCoefficients (mixedCoordinateTuple i d))
        (span_paddedCoefficients_eq_top _ (mixedCoordinateTuple_span i d)) := by
  let U : (Alterations.projectiveSpace R m).AffineZariskiSite :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let E := pullbackIsoOfRestrictIso
    (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ)) U.1
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j (d + 1))
  have h := projectiveMap_on_frame (Alterations.projectiveSpaceStructure R m)
    (coordinateHyperplaneTwist_isInvertible (R := R) j ((d + 1 : ℕ) : ℤ))
    (mixedCoordinateFamily (R := R) j d) U E
  exact (congrArg (fun f =>
    (Alterations.Geometry.Segre.coordinateChartIso (R := R) i).inv ≫ f) h).trans
      (localMap_inverseChart j i d)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateCharts
