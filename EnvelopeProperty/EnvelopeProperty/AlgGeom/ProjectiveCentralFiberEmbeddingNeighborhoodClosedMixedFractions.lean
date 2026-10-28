import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections

/-! # Entire native mixed ratios, including the actual diagonal powers -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedFractions
open ProjectiveHomogeneousSections
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ}

private theorem fraction_mixed (i a b : Fin (m + 1)) (d : ℕ) :
    fraction i (d + 1) (MvPolynomial.X (R := R) a ^ d * MvPolynomial.X b)
        ((MvPolynomial.isHomogeneous_X_pow (R := R) a d).mul
          (MvPolynomial.isHomogeneous_X R b)) =
      fraction i 1 (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a) ^ d *
        fraction i 1 (MvPolynomial.X b) (MvPolynomial.isHomogeneous_X R b) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  change Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := R) i))
      (MvPolynomial.X a ^ d * MvPolynomial.X b)
      ⟨MvPolynomial.X i ^ (d + 1), ⟨d + 1, rfl⟩⟩ =
    Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := R) i))
        (MvPolynomial.X a) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩ ^ d *
      Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := R) i))
        (MvPolynomial.X b) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one]
  ring

/-- Every entire mixed homogeneous coefficient factors into the actual
degree-one coordinate coefficients, without a domain or reducedness premise. -/
theorem coefficient_mixed (i a b : Fin (m + 1)) (d : ℕ) :
    coefficient i (d + 1) (MvPolynomial.X (R := R) a ^ d * MvPolynomial.X b)
        ((MvPolynomial.isHomogeneous_X_pow (R := R) a d).mul
          (MvPolynomial.isHomogeneous_X R b)) =
      coefficient i 1 (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a) ^ d *
        coefficient i 1 (MvPolynomial.X b) (MvPolynomial.isHomogeneous_X R b) := by
  change (Proj.awayToSection (homogeneousSubmodule (Fin (m + 1)) R)
      (MvPolynomial.X i)).hom _ = _
  rw [fraction_mixed, map_mul, map_pow]
  rfl

/-- The entire actual diagonal mixed coefficient is the actual coordinate
ratio to the same positive power d+1, retaining nilpotent coefficients. -/
theorem coefficient_diagonal (i a : Fin (m + 1)) (d : ℕ) :
    coefficient i (d + 1) (MvPolynomial.X (R := R) a ^ d * MvPolynomial.X a)
        ((MvPolynomial.isHomogeneous_X_pow (R := R) a d).mul
          (MvPolynomial.isHomogeneous_X R a)) =
      coefficient i 1 (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a) ^ (d + 1) :=
  (coefficient_mixed i a a d).trans (pow_succ _ _).symm

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedFractions
