import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators
import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections

/-! # The actual original coordinate family and its entire coordinate frame coefficients -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open DeJongAlterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

private def coordinateForms : ULift.{u} (Fin (m + 1)) → MvPolynomial (Fin (m + 1)) R :=
  fun a => MvPolynomial.X a.down

private theorem coordinateForms_homogeneous (a : ULift.{u} (Fin (m + 1))) :
    (coordinateForms (R := R) a).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X R a.down

private theorem coordinateForms_diagonal (i : Fin (m + 1)) :
    coordinateForms (R := R) (ULift.up i) = MvPolynomial.X i ^ 1 := (pow_one _).symm

/-- The ACTUAL original degree-one homogeneous coordinate forms give a genuine
original generating family, with exactly their original universe-lifted index. -/
def coordinateFamily (j : Fin (m + 1)) :
    (coordinateHyperplaneTwist (R := R) j 1).GeneratingSections :=
  homogeneousGeneratingSections j 1 coordinateForms coordinateForms_homogeneous ULift.up
    coordinateForms_diagonal

private instance coordinateFamily_fintype (j : Fin (m + 1)) :
    Fintype (coordinateFamily (R := R) j).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1))))

/-- This SAME original coordinate family is actually finite, with no extra
original central generators or an all-global-sections basis. -/
theorem coordinateFamily_isFiniteType (j : Fin (m + 1)) :
    (coordinateFamily (R := R) j).IsFiniteType :=
  homogeneousGeneratingSections_isFiniteType j 1 coordinateForms coordinateForms_homogeneous
    ULift.up coordinateForms_diagonal

/-- In the ACTUAL original coordinate frame every original local coefficient
is the WHOLE original homogeneous coordinate ratio, in the actual affine
coordinate-open section ring. -/
theorem coordinateFamily_localCoefficient (j i : Fin (m + 1))
    (a : ULift.{u} (Fin (m + 1))) :
    GeneratedLineLocalCoefficients.localCoefficient (coordinateFamily (R := R) j)
        (coordinateOpen (R := R) i)
        (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j 1)
          (coordinateOpen (R := R) i)
          (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j 1)) a =
      (coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X a.down)
          (MvPolynomial.isHomogeneous_X R a.down)) := by
  have h := localCoefficient_eq_fraction (R := R) j 1 coordinateForms coordinateForms_homogeneous
    ULift.up coordinateForms_diagonal i a
  refine h.trans ?_
  rw [ModularCurves.affineOpenTopSection, Scheme.Opens.ι_appIso]
  rfl

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateFamily
