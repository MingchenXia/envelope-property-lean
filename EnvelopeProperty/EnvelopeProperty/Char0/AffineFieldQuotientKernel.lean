import EnvelopeProperty.Char0.AffineFieldRoundedColon
import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalKernel

/-!
# The same actual affine rounded quotient kernel under change of fields

Both sides are the actual original section-map kernels in the literal
coefficient rings. Every new coordinate, morphism and pulled ideal is
manufactured from the original input; no kernel comparison is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

variable {k L : Type u} [Field k] [Field L] [CharZero k] [Algebra k L]
  (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) {n : ℕ}

/-- The WHOLE actual original affine quotient-kernel ideal has exactly its literal tensor extension. -/
theorem specQuotientKernel_fieldTensor
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (specQuotientKernel A B φ z hz J hJ q).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom =
      specQuotientKernel (.of (L ⊗[k] A)) (.of (L ⊗[k] B))
        (Algebra.TensorProduct.map (AlgHom.id L L) φ)
        (fieldTensorCoordinates (k := k) (L := L) z) (etale_fieldTensorCoordinates z hz)
        (J.comap (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom)))
        (isIdealOfSncDivisor_fieldTensor v hv J hJ) q := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  rw [specQuotientKernel_eq_colon A B φ z hz J hJ q v hv,
    specQuotientKernel_eq_colon (.of (L ⊗[k] A)) (.of (L ⊗[k] B))
      (Algebra.TensorProduct.map (AlgHom.id L L) φ)
      (fieldTensorCoordinates (k := k) (L := L) z) (etale_fieldTensorCoordinates z hz)
      _ _ q (fieldTensorCoordinates (k := k) (L := L) v) (etale_fieldTensorCoordinates v hv)]
  exact roundedColon_fieldTensor (L := L) z hz v hv J hJ q

end EnvelopeProperty.Char0.RoundedCanonicalModule
