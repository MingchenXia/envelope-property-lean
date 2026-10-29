import EnvelopeProperty.AlgGeom.GeneratedTupleProjectiveCoordinates
import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections

/-! # SAME original O(1) sections in the actual native tuple-map frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules
open Alterations Alterations.Geometry.ProjectiveIdeal
open Alterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.GeneratedTupleTwistSections
open GeneratedTupleProjectiveCoordinates SchemeLineSectionEvaluation
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [IsDomain A] {m : ℕ}

private theorem homogeneousSectionsMap_eq {B τ : Type u} [CommRing B]
    [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ℕ → τ) [GradedRing ℬ]
    (f : B) {d : ℕ} (hf : f ∈ ℬ d) (hd : 0 < d) :
    (Proj.basicOpenIsoAway ℬ f hf hd).hom =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away ℬ f))).inv ≫
        (Proj.basicOpenIsoSpec ℬ f hf hd).hom.appTop ≫ (Proj.basicOpen ℬ f).topIso.hom := by
  rw [Proj.basicOpenIsoSpec_hom]
  simp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private def chartSectionsIso (i : Fin (m + 1)) :
    CommRingCat.of (CoordinateRing R i) ≅ Γ(Alterations.projectiveSpace R m, coordinateOpen i) :=
  (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.symm ≪≫
    Proj.basicOpenIsoAway (projectiveSpaceGrading R m) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))

private theorem chartSectionsIso_eq (i : Fin (m + 1)) :
    chartSectionsIso (R := R) i =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).symm ≪≫
        Scheme.Γ.mapIso (Alterations.Geometry.Segre.coordinateChartIso i).op ≪≫
          (coordinateOpen (R := R) i).topIso := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv ≫
    (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) i).symm.toRingHom)).appTop ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading R m) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))).hom.appTop ≫
          (coordinateOpen (R := R) i).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [Category.assoc, ← homogeneousSectionsMap_eq]
  rfl

private theorem chartSectionsIso_cancel (i : Fin (m + 1)) :
    (chartSectionsIso (R := R) i).hom ≫ (coordinateOpen (R := R) i).topIso.inv ≫
      (Alterations.Geometry.Segre.coordinateChartIso i).inv.appTop =
        (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv := by
  rw [chartSectionsIso_eq]
  change ((Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv ≫
    (Scheme.Γ.mapIso (Alterations.Geometry.Segre.coordinateChartIso i).op).hom ≫
      (coordinateOpen (R := R) i).topIso.hom) ≫
    (coordinateOpen (R := R) i).topIso.inv ≫
      (Scheme.Γ.mapIso (Alterations.Geometry.Segre.coordinateChartIso i).op).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The ACTUAL original tuple map factors through the SAME original coordinate open. -/
def chartFactor (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    Spec (.of A) ⟶ (coordinateOpen (R := R) i).toScheme :=
  Spec.map (CommRingCat.ofHom (chartRingMap r a ha i hi)) ≫
    (Alterations.Geometry.Segre.coordinateChartIso i).inv

/-- Its entire original triangle is derived from the SAME actual coordinate-map formula. -/
theorem chartFactor_comp (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    chartFactor r a ha i hi ≫ (coordinateOpen (R := R) i).ι = affineTupleMap r a ha := by
  exact (affineTupleMap_coordinateChart r a ha i hi).symm

/-- Every actual original coordinate polynomial is pulled back by the SAME original chart map. -/
theorem chartFactor_section (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (c : CoordinateRing R i) :
    (chartFactor r a ha i hi).appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom ((chartSectionsIso i).hom.hom c)) =
      (Scheme.ΓSpecIso (.of A)).inv.hom (chartRingMap r a ha i hi c) := by
  have h := chartSectionsIso_cancel (R := R) i
  have hs := congrArg (fun q => q.hom c) h
  change (Alterations.Geometry.Segre.coordinateChartIso i).inv.appTop.hom
    ((coordinateOpen (R := R) i).topIso.inv.hom ((chartSectionsIso i).hom.hom c)) =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv.hom c at hs
  simp only [chartFactor, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [hs]
  exact congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartRingMap r a ha i hi))).symm

private theorem chartSectionsIso_coordinate (i j : Fin (m + 1)) :
    (chartSectionsIso (R := R) i).hom.hom (coordinateDehomCoord i j) =
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) := by
  change (Proj.awayToSection (projectiveSpaceGrading R m) (MvPolynomial.X i)).hom
    (homogeneousChartRatioHom i (coordinateDehomCoord i j)) = _
  rw [Alterations.Algebra.Segre.homogeneousChartRatioHom_coordinate]
  rfl

/-- The actual whole original coordinate equation pulls back to the SAME original a_j. -/
theorem chartFactor_coordinate (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (j : Fin (m + 1)) :
    (chartFactor r a ha i hi).appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X R j))) =
      (Scheme.ΓSpecIso (.of A)).inv.hom (a j) := by
  have hc := chartFactor_section r a ha i hi (coordinateDehomCoord i j)
  rw [chartSectionsIso_coordinate, chartRingMap_coordinate] at hc
  exact hc

private theorem affineOpenTopSection_eq {B : Scheme.{u}} (U : B.affineOpens) (c : Γ(B, U.1)) :
    ModularCurves.affineOpenTopSection U c = U.1.topIso.inv.hom c := by
  rw [ModularCurves.affineOpenTopSection, Scheme.Opens.ι_appIso]
  rfl

/-- The actual ORIGINAL global coordinate section has its true whole original chart scalar. -/
theorem coordinateSection_localScalar (i k j : Fin (m + 1)) :
    pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) ≫
      (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) k 1) (coordinateOpen (R := R) i)
        (coordinateHyperplaneTwistTrivialization (R := R) i k 1)).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((coordinateOpen (R := R) i).topIso.inv.hom
          (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
            (MvPolynomial.isHomogeneous_X R j))) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) k 1
  let U : (Alterations.projectiveSpace R m).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i k 1
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) =
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient i k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j))
  have hr := sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection k 1 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j))
  rw [hcoeff, affineOpenTopSection_eq] at hr
  exact hr

/-- The SAME actual original pulled O(1) has its genuine original coordinate frame. -/
def twistFrame (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (k : Fin (m + 1)) :
    (Scheme.Modules.pullback (affineTupleMap r a ha)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ unitObj (Spec (.of A)) :=
  frameViaFactor (chartFactor r a ha i hi) (coordinateOpen (R := R) i).ι
    (affineTupleMap r a ha) (chartFactor_comp r a ha i hi)
    (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) k 1) (coordinateOpen (R := R) i)
      (coordinateHyperplaneTwistTrivialization (R := R) i k 1))

end EnvelopeProperty.GeneratedTupleTwistSections
