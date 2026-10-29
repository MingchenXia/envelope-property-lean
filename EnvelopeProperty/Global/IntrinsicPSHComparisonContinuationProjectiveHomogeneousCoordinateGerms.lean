import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveCoordinateAlgebras
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateSectionRelations
import EnvelopeProperty.Projective.NativeCharts

/-!
# Original homogeneous global-section coefficients and finite field generation

The polynomial chart section map is identified with the native
homogeneous-away section map, not by an assumed coordinate or frame match.
Thus the proved finite field generators are the germs of
the glued original degree-one global-section coefficients.
Route: owned `projective-homogeneous-coordinate-germs-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal Alterations.Algebra.Segre
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The existing native whole section comparison is the DeJong polynomial chart pullback. -/
theorem nativeCoordinateSectionsIso_deJong (j : Fin (n + 1)) :
    ProjBerk.nativeCoordinateSectionsIso (R := R) j =
      (Scheme.ΓSpecIso (.of (CoordinateRing R j))).symm ≪≫
        Scheme.Γ.mapIso (coordinateChartIso j).op ≪≫ (coordinateOpen (R := R) j).topIso := by
  have hhom : (Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X j)) =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away (projectiveSpaceGrading R n)
        (MvPolynomial.X j)))).inv ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading R n) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ))).hom.appTop ≫
      (coordinateOpen (R := R) j).topIso.hom := by
    change (Proj.basicOpenIsoAway (projectiveSpaceGrading R n) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ))).hom = _
    rw [Proj.basicOpenIsoSpec_hom]
    simp only [Scheme.Hom.appTop]
    rw [Proj.basicOpenToSpec_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (.of (CoordinateRing R j))).inv ≫
    (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).symm.toRingHom)).appTop ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading R n) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ))).hom.appTop ≫
      (coordinateOpen (R := R) j).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  change CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).symm.toRingHom ≫
      (ProjBerk.nativeHomogeneousChartSectionsIso (R := R) j).hom = _
  rw [ProjBerk.nativeHomogeneousChartSectionsIso_hom]
  change CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).symm.toRingHom ≫
      Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X j) = _
  simpa only [Category.assoc] using congrArg
    (fun g : CommRingCat.of (HomogeneousLocalization.Away (projectiveSpaceGrading R n)
      (MvPolynomial.X j)) ⟶ Γ(projectiveSpace R n, coordinateOpen (R := R) j) =>
        CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).symm.toRingHom ≫ g) hhom

/-- The polynomial coordinate chart has exactly the original homogeneous standard open as range. -/
theorem projectiveCoordinateChart_opensRange (j : Fin (n + 1)) :
    (coordinateChartInclusion (R := R) j).opensRange = coordinateOpen (R := R) j := by
  unfold coordinateChartInclusion
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- Its whole original section pullback on the standard open is the original chart pullback. -/
theorem coordinateChartInclusion_appLE_coordinateOpen (j : Fin (n + 1))
    (h : (⊤ : (Spec (.of (CoordinateRing R j))).Opens) ≤
      (coordinateChartInclusion (R := R) j) ⁻¹ᵁ coordinateOpen (R := R) j) :
    (coordinateChartInclusion (R := R) j).appLE (coordinateOpen (R := R) j) ⊤ h =
      (coordinateOpen (R := R) j).topIso.inv ≫ (coordinateChartIso j).inv.appTop := by
  let U := coordinateOpen (R := R) j
  let g := (coordinateChartIso (R := R) j).inv
  have hu : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    apply (projectiveSpace R n).presheaf.congr_map
    exact Subsingleton.elim _ _
  have hg : g.appLE ⊤ ⊤ le_top = g.appTop := by simp [Scheme.Hom.appLE]
  have hc := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top
  rw [hu, hg] at hc
  exact hc.symm

/-- The homogeneous O(1) frame coefficient restricted to the same original polynomial chart range. -/
def homogeneousCoordinateOnChartRange (j l : Fin (n + 1)) :
    Γ(projectiveSpace R n, (coordinateChartInclusion (R := R) j).opensRange) :=
  (projectiveSpace R n).presheaf.map (eqToHom (projectiveCoordinateChart_opensRange (R := R) j)).op
    (ProjectiveHomogeneousSections.coefficient j 1 (MvPolynomial.X l)
      (MvPolynomial.isHomogeneous_X R l))

/-- The original polynomial coordinate is the original homogeneous global-section frame coefficient. -/
theorem projectiveChartSectionRingEquiv_homogeneous (j l : Fin (n + 1)) :
    OpenImmersionGenericCoordinates.sectionRingEquiv (coordinateChartInclusion (R := R) j)
        (coordinateDehomCoord j l) = homogeneousCoordinateOnChartRange (R := R) j l := by
  let f := coordinateChartInclusion (R := R) j
  let U := coordinateOpen (R := R) j
  let E := ProjBerk.nativeCoordinateSectionsIso (R := R) j
  let a := coordinateDehomCoord (R := R) j l
  have ha : E.hom a = ProjectiveHomogeneousSections.coefficient j 1 (MvPolynomial.X l)
      (MvPolynomial.isHomogeneous_X R l) := by
    change (ProjBerk.nativeHomogeneousChartSectionsIso (R := R) j).hom
      (ProjBerk.homogeneousChartRatioHom j (coordinateDehomCoord j l)) = _
    rw [ProjBerk.nativeHomogeneousChartSectionsIso_hom]
    change (Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X j)).hom
      (homogeneousChartRatioHom j (coordinateDehomCoord j l)) = _
    rw [homogeneousChartRatioHom_coordinate]
    rfl
  let e := OpenImmersionGenericCoordinates.sectionRingEquiv f
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change a = (Scheme.ΓSpecIso (.of (CoordinateRing R j))).hom
    (f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩)
      ((projectiveSpace R n).presheaf.map
        (eqToHom (projectiveCoordinateChart_opensRange (R := R) j)).op
        (ProjectiveHomogeneousSections.coefficient j 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X R l))))
  rw [← ha]
  have hm := f.map_appLE (show (⊤ : (Spec (.of (CoordinateRing R j))).Opens) ≤
      f ⁻¹ᵁ f.opensRange from by intro x _; exact ⟨x, rfl⟩)
    (eqToHom (projectiveCoordinateChart_opensRange (R := R) j)).op
  have hma := ConcreteCategory.congr_hom hm (E.hom a)
  change f.appLE f.opensRange ⊤ _
    ((projectiveSpace R n).presheaf.map (eqToHom
      (projectiveCoordinateChart_opensRange (R := R) j)).op (E.hom a)) =
        f.appLE U ⊤ _ (E.hom a) at hma
  rw [hma, coordinateChartInclusion_appLE_coordinateOpen]
  have hcancel : E.hom ≫ U.topIso.inv ≫ (coordinateChartIso (R := R) j).inv.appTop =
      (Scheme.ΓSpecIso (.of (CoordinateRing R j))).inv := by
    dsimp only [E]
    rw [nativeCoordinateSectionsIso_deJong]
    change ((Scheme.ΓSpecIso (.of (CoordinateRing R j))).inv ≫
      (Scheme.Γ.mapIso (coordinateChartIso j).op).hom ≫ U.topIso.hom) ≫ U.topIso.inv ≫
        (Scheme.Γ.mapIso (coordinateChartIso j).op).inv = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hc := ConcreteCategory.congr_hom hcancel a
  change (coordinateChartIso (R := R) j).inv.appTop (U.topIso.inv (E.hom a)) =
    (Scheme.ΓSpecIso (.of (CoordinateRing R j))).inv a at hc
  exact ((congrArg (fun z : Γ(Spec (.of (CoordinateRing R j)), ⊤) =>
    (Scheme.ΓSpecIso (.of (CoordinateRing R j))).hom z) hc).trans
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (CoordinateRing R j))) a)).symm

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- Every original projective coordinate generic value is the original homogeneous frame-coefficient germ. -/
theorem projectiveCoordinateGenericHom_homogeneous (i : X ⟶ projectiveSpace k n)
    (j l : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    projectiveCoordinateGenericHom i j (coordinateDehomCoord j l) =
      X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
        (i.app (coordinateChartInclusion (R := k) j).opensRange
          (homogeneousCoordinateOnChartRange (R := k) j l)) := by
  rw [projectiveCoordinateGenericHom_apply, projectiveChartSectionRingEquiv_homogeneous]

/-- Finitely many original homogeneous global-section coefficient germs generate the whole original field. -/
theorem projectiveHomogeneousCoordinateGenerics_generate (i : X ⟶ projectiveSpace k n)
    [IsClosedImmersion i] (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k (Set.range (fun l : ChartIndex j =>
      X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
        (i.app (coordinateChartInclusion (R := k) j).opensRange
          (homogeneousCoordinateOnChartRange (R := k) j l.1)))) = ⊤ := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  have hv (l : ChartIndex j) :
      X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
        (i.app (coordinateChartInclusion (R := k) j).opensRange
          (homogeneousCoordinateOnChartRange (R := k) j l.1)) =
        projectiveCoordinateGenericHom i j (MvPolynomial.X l) := by
    rw [← projectiveCoordinateGenericHom_homogeneous, coordinateDehomCoord_ne]
  simp_rw [hv]
  exact projectiveCoordinateGenericVariables_generate i j

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateChart_opensRange
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateChart_opensRange

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.coordinateChartInclusion_appLE_coordinateOpen
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.coordinateChartInclusion_appLE_coordinateOpen

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.homogeneousCoordinateOnChartRange
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.homogeneousCoordinateOnChartRange

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveChartSectionRingEquiv_homogeneous
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveChartSectionRingEquiv_homogeneous

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_homogeneous
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_homogeneous

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveHomogeneousCoordinateGenerics_generate
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveHomogeneousCoordinateGenerics_generate

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.nativeCoordinateSectionsIso_deJong
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.nativeCoordinateSectionsIso_deJong
