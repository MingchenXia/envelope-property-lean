/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.JacobianBaseChange
import EnvelopeProperty.Char0.ResolutionScalarTowers

/-!
# Actual Jacobian ideals in restricted étale coordinates

The transported differential basis is the actual basis of the restricted
coordinate functions. This identifies the extended Jacobian image ideal with
the genuine image ideal in those actual restricted coordinates.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module
open scoped Classical

universe u

variable {k A₀ A : Type u} [CommRing k] [CommRing A₀] [CommRing A]
  [Algebra k A₀] [Algebra k A] [Algebra A₀ A] [IsScalarTower k A₀ A] {n : ℕ}

/-- Transport of the actual coordinate basis equals the actual basis of the image coordinates. -/
theorem etaleDifferentialBasis_baseChange [Algebra.FormallyEtale A₀ A]
    (v : Fin n → A₀) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (hv' : (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))).toRingHom.Etale) :
    differentialBasisBaseChange (A := A) (etaleDifferentialBasis v hv) =
      etaleDifferentialBasis (fun i => algebraMap A₀ A (v i)) hv' := by
  apply DFunLike.ext
  intro i
  rw [differentialBasisBaseChange_apply, etaleDifferentialBasis_apply,
    etaleDifferentialBasis_apply, KaehlerDifferential.map_D]

variable {R : Type u} [CommRing R] [Algebra k R] [Algebra R A₀] [Algebra R A]
  [IsScalarTower k R A₀] [IsScalarTower k R A] [IsScalarTower R A₀ A]

/-- The extended actual image ideal is the genuine image ideal in the actual image coordinates. -/
theorem map_affineRelativeJacobianIdeal_etale_coordinates [Algebra.FormallyEtale A₀ A]
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → A₀) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (hv' : (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))).toRingHom.Etale) :
    (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map (algebraMap A₀ A) =
      affineRelativeJacobianIdeal (R := R)
        (etaleDifferentialBasis (fun i => algebraMap A₀ A (v i)) hv') := by
  rw [map_affineRelativeJacobianIdeal z hz, etaleDifferentialBasis_baseChange v hv hv']

end EnvelopeProperty.Char0
