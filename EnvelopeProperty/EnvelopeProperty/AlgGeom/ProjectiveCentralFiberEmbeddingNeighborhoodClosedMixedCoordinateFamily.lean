import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators

/-! # Actual mixed coordinate sections and their original row ratios -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open DeJongAlterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators
open ProjectiveHomogeneousSections
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

private def mixedForms (d : ℕ) :
    ULift.{u} (Fin (m + 1) × Fin (m + 1)) → MvPolynomial (Fin (m + 1)) R :=
  fun a => MvPolynomial.X a.down.1 ^ d * MvPolynomial.X a.down.2

private theorem mixedForms_homogeneous (d : ℕ)
    (a : ULift.{u} (Fin (m + 1) × Fin (m + 1))) :
    (mixedForms (R := R) d a).IsHomogeneous (d + 1) :=
  (MvPolynomial.isHomogeneous_X_pow (R := R) a.down.1 d).mul
    (MvPolynomial.isHomogeneous_X R a.down.2)

private theorem mixedForms_diagonal (d : ℕ) (i : Fin (m + 1)) :
    mixedForms (R := R) d (ULift.up (i, i)) = MvPolynomial.X i ^ (d + 1) :=
  (pow_succ _ _).symm

/-- The actual mixed monomials of degree d+1 generate the original O(d+1),
with their literal finite pair index and no added global-section basis. -/
def mixedCoordinateFamily (j : Fin (m + 1)) (d : ℕ) :
    (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ)).GeneratingSections :=
  homogeneousGeneratingSections j (d + 1) (mixedForms d) (mixedForms_homogeneous d)
    (fun i => ULift.up (i, i)) (mixedForms_diagonal d)

private instance mixedCoordinateFamily_fintype (j : Fin (m + 1)) (d : ℕ) :
    Fintype (mixedCoordinateFamily (R := R) j d).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1) × Fin (m + 1))))

/-- This same actual mixed family is finite, retaining every original pair. -/
theorem mixedCoordinateFamily_isFiniteType (j : Fin (m + 1)) (d : ℕ) :
    (mixedCoordinateFamily (R := R) j d).IsFiniteType :=
  homogeneousGeneratingSections_isFiniteType j (d + 1) (mixedForms d)
    (mixedForms_homogeneous d) (fun i => ULift.up (i, i)) (mixedForms_diagonal d)

/-- Every mixed coefficient is its actual entire homogeneous ratio, over any
commutative coefficient ring, including nilpotents and the zero ring. -/
theorem mixedCoordinateFamily_localCoefficient (j i : Fin (m + 1)) (d : ℕ)
    (a : ULift.{u} (Fin (m + 1) × Fin (m + 1))) :
    GeneratedLineLocalCoefficients.localCoefficient (mixedCoordinateFamily (R := R) j d)
        (coordinateOpen (R := R) i)
        (pullbackIsoOfRestrictIso
          (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ))
          (coordinateOpen (R := R) i)
          (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j (d + 1))) a =
      (coordinateOpen (R := R) i).topIso.inv.hom
        (coefficient i (d + 1) (MvPolynomial.X a.down.1 ^ d * MvPolynomial.X a.down.2)
          ((MvPolynomial.isHomogeneous_X_pow (R := R) a.down.1 d).mul
            (MvPolynomial.isHomogeneous_X R a.down.2))) := by
  have h := localCoefficient_eq_fraction (R := R) j (d + 1) (mixedForms d)
    (mixedForms_homogeneous d) (fun i => ULift.up (i, i)) (mixedForms_diagonal d) i a
  refine h.trans ?_
  rw [ModularCurves.affineOpenTopSection, Scheme.Opens.ι_appIso]
  rfl

private theorem mixedRow_fraction (i a : Fin (m + 1)) (d : ℕ) :
    fraction i (d + 1) (MvPolynomial.X (R := R) i ^ d * MvPolynomial.X a)
        ((MvPolynomial.isHomogeneous_X_pow (R := R) i d).mul
          (MvPolynomial.isHomogeneous_X R a)) =
      fraction i 1 (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := R) i))
      (MvPolynomial.X i ^ d * MvPolynomial.X a)
      ⟨MvPolynomial.X i ^ (d + 1), ⟨d + 1, rfl⟩⟩ =
    Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := R) i))
      (MvPolynomial.X a) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one]
  ring

/-- In the i-th original frame the entire (i,a)-row coefficient is exactly
the original degree-one ratio X_a/X_i. This uses localization identities,
without reduction, points, nonzerodivisors or a domain assumption. -/
theorem mixedCoordinateFamily_row_localCoefficient (j i a : Fin (m + 1)) (d : ℕ) :
    GeneratedLineLocalCoefficients.localCoefficient (mixedCoordinateFamily (R := R) j d)
        (coordinateOpen (R := R) i)
        (pullbackIsoOfRestrictIso
          (coordinateHyperplaneTwist (R := R) j ((d + 1 : ℕ) : ℤ))
          (coordinateOpen (R := R) i)
          (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j (d + 1)))
        (ULift.up (i, a)) =
      (coordinateOpen (R := R) i).topIso.inv.hom
        (coefficient i 1 (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a)) := by
  refine (mixedCoordinateFamily_localCoefficient j i d (ULift.up (i, a))).trans ?_
  apply congrArg (fun s => (coordinateOpen (R := R) i).topIso.inv.hom s)
  exact congrArg
    (fun z => (Proj.awayToSection (homogeneousSubmodule (Fin (m + 1)) R)
      (MvPolynomial.X i)).hom z) (mixedRow_fraction i a d)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateFamily
