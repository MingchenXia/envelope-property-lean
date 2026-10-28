import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsParameterCharts
import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsSectionAlgebra

/-! # The whole SAME original family chart algebra is the SAME old chart polynomial ring -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk Berkovich Char0.EnvelopeGradedBaseIdealsSectionAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME actual full homogeneous defining ideal sheaf of the parameter family. -/
def familyCutIdeal : (NativeProjectiveScheme k[X] M).IdealSheafData :=
  GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X)

/-- The actual ORIGINAL quotient is isomorphic to its actual closed image. -/
def familyCutIso : familyScheme X ≅ (familyCutIdeal X).subscheme :=
  asIso (familyInclusion X).toImage

/-- Its ENTIRE original inclusion triangle is retained. -/
theorem familyCutIso_inclusion :
    (familyCutIso X).hom ≫ (familyCutIdeal X).subschemeι = familyInclusion X :=
  Scheme.Hom.toImage_imageι (familyInclusion X)

/-- The same original actual parameter structure on the whole image subscheme. -/
def familyCutProjection : (familyCutIdeal X).subscheme ⟶ Spec (.of k[X]) :=
  (familyCutIdeal X).subschemeι ≫ nativeStructureMap

/-- The actual original scheme isomorphism preserves the SAME parameter projection. -/
theorem familyCutIso_projection :
    (familyCutIso X).hom ≫ familyCutProjection X = familyProjection X := by
  change (familyCutIso X).hom ≫ (familyCutIdeal X).subschemeι ≫ nativeStructureMap = _
  rw [← Category.assoc, familyCutIso_inclusion]
  rfl

/-- The whole genuine coordinate open on the same actual closed image. -/
def familyCutChartOpen (j : Fin (M + 1)) : (familyCutIdeal X).subscheme.Opens :=
  (familyCutIdeal X).subschemeι ⁻¹ᵁ nativeCoordinateOpen (R := k[X]) j

/-- The SAME original coordinate open on the SAME original family. -/
def familyChartOpen (j : Fin (M + 1)) : (familyScheme X).Opens :=
  (familyCutIso X).hom ⁻¹ᵁ familyCutChartOpen X j

/-- This is exactly the inverse image under the ORIGINAL family inclusion. -/
theorem familyChartOpen_eq (j : Fin (M + 1)) :
    familyChartOpen X j = familyInclusion X ⁻¹ᵁ nativeCoordinateOpen (R := k[X]) j := by
  change ((familyCutIso X).hom ≫ (familyCutIdeal X).subschemeι) ⁻¹ᵁ nativeCoordinateOpen j = _
  rw [familyCutIso_inclusion]

/-- The actual original coordinate inverse image is genuinely affine. -/
theorem familyChartOpen_isAffine (j : Fin (M + 1)) : IsAffineOpen (familyChartOpen X j) :=
  ((nativeCoordinateOpen_isAffine (R := k[X]) j).preimage (familyCutIdeal X).subschemeι).preimage
    (familyCutIso X).hom

/-- The whole actual family coordinate section algebra is its ENTIRE original quotient,
linear for the SAME original parameter projection. -/
def familyChartCoordinateAlgEquiv (j : Fin (M + 1)) :
    letI := (familyProjection X).sectionsAlgebra (familyChartOpen X j)
    Γ(familyScheme X, familyChartOpen X j) ≃ₐ[k[X]]
      CoordinateRing k[X] j ⧸ (familyHomogeneousIdeal X).toIdeal.map (coordinateDehom j).toRingHom := by
  letI := (familyProjection X).sectionsAlgebra (familyChartOpen X j)
  letI := (familyProjection X).sectionsAlgebra
    ((familyCutIso X).hom ⁻¹ᵁ familyCutChartOpen X j)
  letI := (familyCutProjection X).sectionsAlgebra (familyCutChartOpen X j)
  exact (sectionAlgEquivOfIso (familyCutIso X) (familyProjection X) (familyCutProjection X)
    (familyCutIso_projection X) (familyCutChartOpen X j)).symm.trans
      (nativeQuotientCoordinateSectionsAlgEquiv (familyHomogeneousIdeal X) j)

/-- The whole original affine chart, with the original field action used by
scheme multiplier/DVR estimates, is the SAME original old chart polynomial ring. -/
def familyChartSectionsEquiv (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    letI := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
    Γ(familyScheme X, familyChartOpen X j) ≃ₐ[k] (QuotChartAlg X.ideal (MvPolynomial.X j) 1)[X] := by
  letI := (familyProjection X).sectionsAlgebra (familyChartOpen X j)
  letI := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
  letI : IsScalarTower k k[X] Γ(familyScheme X, familyChartOpen X j) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      RingHom.congr_fun (sectionBaseMap_comp (familyProjection X)
        (Polynomial.C : k →+* k[X]) (familyChartOpen X j)) a
  exact ((familyChartCoordinateAlgEquiv X j).restrictScalars k).trans
    (familyCoordinateQuotientEquiv X j hj)

private local instance familyGradedRing : GradedRing
    (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal) :=
  GradedQuotient.gradedRing _ _ (familyHomogeneousIdeal X).isHomogeneous

/-- Original relevance internally proves nonemptiness of this SAME actual original chart. -/
theorem familyChartOpen_nonempty (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    Nonempty (familyChartOpen X j) := by
  let z := DeJongAlterations.Geometry.ProjIntegral.zeroPoint _ (family_irrelevant_ne_bot X)
  refine ⟨⟨z, ?_⟩⟩
  rw [familyChartOpen_eq]
  change (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k[X]) ∉ (familyInclusion X z).asHomogeneousIdeal
  exact fun h => coordinate_notMem_familyIdeal X hj ((familyInclusion_zeroPoint_mem_iff X _).mp h)

/-- The SAME actual original affine chart as genuine affine-open data. -/
def familyChartAffineOpen (j : Fin (M + 1)) : (familyScheme X).affineOpens :=
  ⟨familyChartOpen X j, familyChartOpen_isAffine X j⟩

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
