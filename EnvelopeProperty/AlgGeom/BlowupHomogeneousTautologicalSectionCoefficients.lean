import EnvelopeProperty.Alterations.Geometry.BlowupProjectiveEmbeddingForms
import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation

/-! # The original homogeneous section as a whole scalar morphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open Alterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The actual original homogeneous section has its original whole scalar
morphism in the same native positive-power frame, including zero and degree zero. -/
theorem homogeneous_localScalar (i : Fin (n+1)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    SchemeLineSectionEvaluation.pullbackSectionHom (nativeCoordinateOpen (R := R) i).ι
        (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF) ≫
      (Scheme.Modules.pullbackIsoOfRestrictIso
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
        (nativeCoordinateOpen i)
        (coordinateHyperplanePoleSheafPowerTrivialization i (0 : Fin (n+1)) d)).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection
          (Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen i)
          (ProjectiveHomogeneousSections.coefficient i d F hF)) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let U := Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i (0 : Fin (n+1)) d
  let s := ProjectiveHomogeneousSections.homogeneousSection (R := R) (0 : Fin (n+1)) d F hF
  have hc : ModularCurves.localTrivializationCoefficient M U e s =
      ProjectiveHomogeneousSections.coefficient i d F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e s).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient i (0 : Fin (n+1)) d F hF)
  have hs := SchemeLineSectionEvaluation.sectionHom_localScalar M U e s
  exact hs.trans (congrArg
    (fun c : Γ(Alterations.projectiveSpace R n, U.1) =>
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection U c)) hc)


end EnvelopeProperty.BlowupHomogeneousTautologicalLine
