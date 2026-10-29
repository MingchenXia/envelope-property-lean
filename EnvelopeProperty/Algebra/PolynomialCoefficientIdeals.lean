/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.PolynomialCoefficientSwap
import Mathlib.RingTheory.Polynomial.Basic

open scoped Polynomial
noncomputable section
namespace EnvelopeProperty
set_option backward.isDefEq.respectTransparency false
variable {R σ : Type*} [CommRing R]

private theorem coefficientSwap_comp_map_C :
    (polynomialCoefficientSwap R σ).toRingHom.comp
        (MvPolynomial.map (Polynomial.C : R →+* R[X])) =
      (Polynomial.C : MvPolynomial σ R →+* (MvPolynomial σ R)[X]) := by
  ext r i <;> simp

private theorem ideal_map_coefficientSwap (J : Ideal (MvPolynomial σ R)) :
    (J.map (MvPolynomial.map (Polynomial.C : R →+* R[X]))).map
        (polynomialCoefficientSwap R σ).toRingHom =
      J.map (Polynomial.C : MvPolynomial σ R →+* (MvPolynomial σ R)[X]) := by
  rw [Ideal.map_map, coefficientSwap_comp_map_C]

/-- Every original polynomial belongs to the actual coefficient extension
iff all original univariate coefficients after the existing interchange
belong to the same original ideal, without reducedness or finiteness. -/
theorem mem_polynomialCoefficientIdeal_iff (J : Ideal (MvPolynomial σ R))
    (F : MvPolynomial σ R[X]) :
    F ∈ J.map (MvPolynomial.map (Polynomial.C : R →+* R[X])) ↔
      ∀ n, (polynomialCoefficientSwap R σ F).coeff n ∈ J := by
  rw [← Ideal.apply_mem_of_equiv_iff
    (f := (polynomialCoefficientSwap R σ).toRingEquiv)]
  change polynomialCoefficientSwap R σ F ∈
    (J.map (MvPolynomial.map (Polynomial.C : R →+* R[X]))).map
      (polynomialCoefficientSwap R σ).toRingHom ↔ _
  rw [ideal_map_coefficientSwap, Ideal.mem_map_C_iff]

/-- Original prime ideals remain prime under the actual polynomial
coefficient extension; no field or finite variable hypothesis is needed. -/
theorem isPrime_polynomialCoefficientIdeal (J : Ideal (MvPolynomial σ R))
    [J.IsPrime] :
    (J.map (MvPolynomial.map (Polynomial.C : R →+* R[X]))).IsPrime := by
  have hp : (J.map (Polynomial.C : MvPolynomial σ R →+* (MvPolynomial σ R)[X])).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  have he : J.map (MvPolynomial.map (Polynomial.C : R →+* R[X])) =
      (J.map (Polynomial.C : MvPolynomial σ R →+* (MvPolynomial σ R)[X])).comap
        (polynomialCoefficientSwap R σ).toRingHom := by
    rw [← ideal_map_coefficientSwap]
    exact (Ideal.comap_map_of_bijective (polynomialCoefficientSwap R σ).toRingHom
      (polynomialCoefficientSwap R σ).bijective).symm
  rw [he]
  exact Ideal.comap_isPrime _ _

end EnvelopeProperty
