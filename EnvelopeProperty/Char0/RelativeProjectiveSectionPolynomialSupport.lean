import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialMaps

/-! # Every original native chart fraction has its exact shifted Laurent support

Only its own original coordinate can be a denominator. Original exponents,
original numerator homogeneity and original coefficients are retained.
-/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
open Alterations.Geometry.ProperSteinProjectiveCech
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem homogeneous_to_integral {τ : Type u} [Fintype τ]
    (F : MvPolynomial τ R) (e : ℕ) (hF : F.IsHomogeneous e) :
    F ∈ polynomialIntegralGrading (e : ℤ) := by
  intro d hd
  have h := hF hd
  simp only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one] at h ⊢
  exact_mod_cast h

/-- The ACTUAL native degree-zero chart fraction, shifted by its OWN original coordinate power, lies in exactly its native allowed Laurent piece. -/
theorem originalAwayToLaurent_shift_mem (i : σ) (e : ℕ)
    (z : Away (homogeneousSubmodule σ R) (X i)) :
    originalAwayToLaurent (X i) (originalPolynomialToLaurent_X_isUnit i) z *
        originalPolynomialToLaurent (X i) ^ e ∈
      subsetHomogeneousLaurentModule (K := R) (I := ULift.{u} σ) (e : ℤ) {ULift.up i} := by
  classical
  obtain ⟨n, F, hF, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ R) (isHomogeneous_X R i) z
  have hFn : F.IsHomogeneous n := by simpa using hF
  let Q : MvPolynomial (ULift.{u} σ) R := MvPolynomial.rename ULift.up F * X (ULift.up i) ^ e
  have hQ : Q.IsHomogeneous (n + e) := by
    exact (hFn.rename_isHomogeneous).mul (by simpa using (isHomogeneous_X R (ULift.up i)).pow e)
  have hQ' : Q ∈ polynomialIntegralGrading
      ((e : ℤ) + (n : ℤ) * (({ULift.up i} : Finset (ULift.{u} σ)).card : ℤ)) := by
    simpa only [Finset.card_singleton, Nat.cast_one, mul_one, Nat.cast_add, add_comm] using
      homogeneous_to_integral Q (n + e) hQ
  let w : polynomialCoordinateHomogeneousPiece (K := R) (I := ULift.{u} σ) (e : ℤ) {ULift.up i} :=
    ⟨LocalizedModule.mk Q (homogeneousPowerDenominator (polynomialCoordinateProduct {ULift.up i}) n),
      n, Q, hQ', rfl⟩
  have hd := polynomialCoordinateModuleToLaurent_clear_polynomial (K := R) (I := ULift.{u} σ)
    {ULift.up i} Q n
  have hd' : polynomialCoordinateModuleToLaurent {ULift.up i} w.val *
      originalPolynomialToLaurent (X i) ^ n =
      originalPolynomialToLaurent F * originalPolynomialToLaurent (X i) ^ e := by
    simpa only [w, Q, polynomialCoordinateProduct, Finset.prod_singleton, map_mul, map_pow,
      originalPolynomialToLaurent, AlgHom.comp_apply, MvPolynomial.rename_X] using hd
  have hn := originalAwayToLaurent_mk_clear (X i) (originalPolynomialToLaurent_X_isUnit i)
    (isHomogeneous_X R i) n F hF
  have heq : polynomialCoordinateModuleToLaurent {ULift.up i} w.val =
      originalAwayToLaurent (X i) (originalPolynomialToLaurent_X_isUnit i)
        (Away.mk (homogeneousSubmodule σ R) (isHomogeneous_X R i) n F hF) *
          originalPolynomialToLaurent (X i) ^ e := by
    apply ((originalPolynomialToLaurent_X_isUnit (R := R) i).pow n).mul_right_cancel
    calc
      _ = originalPolynomialToLaurent F * originalPolynomialToLaurent (X i) ^ e := hd'
      _ = _ := by rw [← hn]; ring
  rw [← heq]
  exact polynomialCoordinateModuleToLaurent_mem (e : ℤ) {ULift.up i} w

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
