import EnvelopeProperty.AlgGeom.ProjectiveCoordinateSectionRelations
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import DeJongAlterations.Geometry.SegreGluingCoordinates

/-! # Original projective coordinate sections on arbitrary actual polynomial chart maps -/
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open Scheme.Modules DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre DeJongAlterations.Geometry.Segre
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveChartSectionRatios
open SchemeLineSectionEvaluation SchemeLineSectionFactorization
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {m : ℕ}
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
    CommRingCat.of (CoordinateRing R i) ≅ Γ(DeJongAlterations.projectiveSpace R m, coordinateOpen i) :=
  (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.symm ≪≫
    Proj.basicOpenIsoAway (projectiveSpaceGrading R m) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))

private theorem chartSectionsIso_eq (i : Fin (m + 1)) :
    chartSectionsIso (R := R) i =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).symm ≪≫
        Scheme.Γ.mapIso (DeJongAlterations.Geometry.Segre.coordinateChartIso i).op ≪≫
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
      (DeJongAlterations.Geometry.Segre.coordinateChartIso i).inv.appTop =
        (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv := by
  rw [chartSectionsIso_eq]
  change ((Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv ≫
    (Scheme.Γ.mapIso (DeJongAlterations.Geometry.Segre.coordinateChartIso i).op).hom ≫
      (coordinateOpen (R := R) i).topIso.hom) ≫
    (coordinateOpen (R := R) i).topIso.inv ≫
      (Scheme.Γ.mapIso (DeJongAlterations.Geometry.Segre.coordinateChartIso i).op).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]


private theorem chartSectionsIso_coordinate (i j : Fin (m + 1)) :
    (chartSectionsIso (R := R) i).hom.hom (coordinateDehomCoord i j) =
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) := by
  change (Proj.awayToSection (projectiveSpaceGrading R m) (MvPolynomial.X i)).hom
    (homogeneousChartRatioHom i (coordinateDehomCoord i j)) = _
  rw [DeJongAlterations.Algebra.Segre.homogeneousChartRatioHom_coordinate]
  rfl

/-- The SAME arbitrary original map into the polynomial chart factors through
the SAME native projective open, using its actual original chart isomorphism. -/
def chartFactor {T : Scheme.{u}} (i : Fin (m + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i))) : T ⟶ (coordinateOpen (R := R) i).toScheme :=
  f ≫ (coordinateChartIso i).inv

/-- Every entire original coordinate coefficient is its true polynomial-chart pullback. -/
theorem coefficient_pullback {T : Scheme.{u}} (i j : Fin (m + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i))) :
    (chartFactor i f).appTop.hom ((coordinateOpen (R := R) i).topIso.inv.hom
      (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j))) = pullRingHom f (coordinateDehomCoord i j) := by
  have hs := congrArg (fun q => q.hom (coordinateDehomCoord i j)) (chartSectionsIso_cancel (R := R) i)
  change (coordinateChartIso (R := R) i).inv.appTop.hom
    ((coordinateOpen (R := R) i).topIso.inv.hom
      ((chartSectionsIso i).hom.hom (coordinateDehomCoord i j))) =
    (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv.hom (coordinateDehomCoord i j) at hs
  rw [chartSectionsIso_coordinate] at hs
  simpa only [chartFactor, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    pullRingHom] using congrArg f.appTop.hom hs

/-- The SAME original pivot coordinate is a true whole section isomorphism
on every arbitrary original scheme mapping into its polynomial chart. -/
theorem sectionHom_isIso {T : Scheme.{u}} (i k : Fin (m + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i))) :
    IsIso (pullbackSectionHom (f ≫ coordinateChartInclusion i)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i))) := by
  exact isIso_pullbackSectionHom_factor (chartFactor i f) (coordinateOpen (R := R) i).ι
    (f ≫ coordinateChartInclusion i) (Category.assoc _ _ _)
    _ (ProjectiveCoordinateSectionRelations.sectionHom_isIso_on_own_chart i k)

/-- EVERY original coordinate section retains its TRUE original polynomial
ratio to its SAME original pivot under an arbitrary whole chart map. -/
theorem sectionHom_relation {T : Scheme.{u}} (i k j : Fin (m + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i))) :
    pullbackSectionHom (f ≫ coordinateChartInclusion i)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) =
      ModularCurves.unitEndomorphismOfTopSection (pullRingHom f (coordinateDehomCoord i j)) ≫
        pullbackSectionHom (f ≫ coordinateChartInclusion i)
          (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i)) := by
  have h := factor_scalar_relation (chartFactor i f) (coordinateOpen (R := R) i).ι
    (f ≫ coordinateChartInclusion i) (Category.assoc _ _ _)
    _ _ _ (ProjectiveCoordinateSectionRelations.sectionHom_ratio_on_chart i k j)
  rw [coefficient_pullback] at h
  exact h

end EnvelopeProperty.ProjectiveChartSectionRatios
