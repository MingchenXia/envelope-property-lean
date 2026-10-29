import EnvelopeProperty.AlgGeom.ProjectiveCoordinateIdealBaseChange
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionPullback

/-! # Whole original O(d) under arbitrary actual coefficient base change -/
open CategoryTheory AlgebraicGeometry MvPolynomial MonoidalCategory
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjectiveTwistCoefficientPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
noncomputable local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
noncomputable local instance {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- The actual original O(1) pulls back to the SAME original O(1) over ANY
coefficient-ring map, derived from the true Cartier ideal and genuine dual
pullback evaluation. No line-comparison premise is supplied. -/
def coordinatePolePullbackIso (φ : R →+* S) (j : Fin (n+1)) :
    (Scheme.Modules.pullback (nativeCoefficientMap φ)).obj
      (coordinateHyperplanePoleSheaf (R := R) j) ≅ coordinateHyperplanePoleSheaf (R := S) j :=
  SchemeInvertibleHomSection.dualPullbackEvaluationIso (nativeCoefficientMap φ)
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))
    (coordinateHyperplaneIdealModule_isInvertible j) ≪≫
      (Scheme.Modules.dualIsoObj (ProjectiveCoordinateIdealBaseChange.coordinateIdealPullbackIso φ j)).symm

/-- Every actual ORIGINAL nonnegative projective twist commutes with ANY
coefficient-ring change as a WHOLE invertible sheaf. The original exponent is
retained exactly, without any flatness, injectivity or field assumption. -/
def coordinatePolePowerPullbackIso (φ : R →+* S) (j : Fin (n+1)) : ∀ d : ℕ,
    (Scheme.Modules.pullback (nativeCoefficientMap φ)).obj
      (coordinateHyperplanePoleSheafPower (R := R) j d) ≅ coordinateHyperplanePoleSheafPower (R := S) j d
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback (nativeCoefficientMap φ))).symm
  | d+1 =>
      (Functor.Monoidal.μIso (Scheme.Modules.pullback (nativeCoefficientMap φ))
        (coordinateHyperplanePoleSheafPower (R := R) j d) (coordinateHyperplanePoleSheaf (R := R) j)).symm ≪≫
          (coordinatePolePowerPullbackIso φ j d ⊗ᵢ coordinatePolePullbackIso φ j)

end EnvelopeProperty.ProjectiveTwistCoefficientPullback
