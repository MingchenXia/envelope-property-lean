import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonCoordinates
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateSectionRelations

/-! # The original Rees map retains its actual whole coordinate sections -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [IsDomain A] {m : ℕ}

/-- The actual original fraction restriction factors through its original
projective pivot chart, with no supplied factorization certificate. -/
def originalFractionProjectiveChartFactor (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    Spec (CommRingCat.of (affineBlowupFractionChart I (g i))) ⟶
      (coordinateOpen (R := R) i).toScheme :=
  GeneratedTupleTwistSections.chartFactor
    ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
    (originalFractionRatioTuple I g hspan i)
    (originalFractionRatioTuple_span I g hspan i hi) i
    (originalFractionRatioTuple_pivot I g hspan i hi)

/-- Its whole triangle is the actual original Rees morphism, with the same
original projective target and the same original coefficient map. -/
theorem originalFractionProjectiveChartFactor_comp (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    originalFractionProjectiveChartFactor r I g hspan i hi ≫
        (coordinateOpen (R := R) i).ι =
      affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan :=
  (GeneratedTupleTwistSections.chartFactor_comp
    ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
    (originalFractionRatioTuple I g hspan i)
    (originalFractionRatioTuple_span I g hspan i hi) i
    (originalFractionRatioTuple_pivot I g hspan i hi)).trans
      (affineGeneratorMap_eq_originalFractionRatioTuple r I g hspan i hi).symm

/-- The original projective pivot section is a basis on the actual original
Rees fraction restriction. Its factor and its own-chart basis are derived. -/
theorem originalFractionCoordinateSection_isIso (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) (k : Fin (m+1)) :
    IsIso (SchemeLineSectionEvaluation.pullbackSectionHom
      (affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i))) :=
  SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
    (originalFractionProjectiveChartFactor r I g hspan i hi)
    (coordinateOpen (R := R) i).ι _
    (originalFractionProjectiveChartFactor_comp r I g hspan i hi)
    (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i))
    (ProjectiveCoordinateSectionRelations.sectionHom_isIso_on_own_chart (R := R) i k)

/-- Every original projective coordinate section has exactly the actual
original generator ratio to the same original pivot on the whole fraction
chart. No section-matching hypothesis is supplied. -/
theorem originalFractionCoordinateSection_ratio (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) (k j : Fin (m+1)) :
    SchemeLineSectionEvaluation.pullbackSectionHom
      (affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart I (g i)))).inv.hom
          (originalFractionRatioTuple I g hspan i j)) ≫
        SchemeLineSectionEvaluation.pullbackSectionHom
          (affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
            affineProjectiveMap r I g hspan)
          (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i)) := by
  have h := SchemeLineSectionFactorization.factor_scalar_relation
    (originalFractionProjectiveChartFactor r I g hspan i hi)
    (coordinateOpen (R := R) i).ι _
    (originalFractionProjectiveChartFactor_comp r I g hspan i hi)
    (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j))
    (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i))
    ((coordinateOpen (R := R) i).topIso.inv.hom
      (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)))
    (ProjectiveCoordinateSectionRelations.sectionHom_ratio_on_chart (R := R) i k j)
  have hs : (originalFractionProjectiveChartFactor r I g hspan i hi).appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X R j))) =
      (Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart I (g i)))).inv.hom
        (originalFractionRatioTuple I g hspan i j) :=
    GeneratedTupleTwistSections.chartFactor_coordinate
      ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
      (originalFractionRatioTuple I g hspan i)
      (originalFractionRatioTuple_span I g hspan i hi) i
      (originalFractionRatioTuple_pivot I g hspan i hi) j
  rw [hs] at h
  exact h

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
