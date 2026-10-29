import EnvelopeProperty.Char0.EtaleSourceInputs
import EnvelopeProperty.AlgGeom.Canonical.ExteriorFieldBaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.RingHom.Etale

/-!
# Actual etale coordinates on the literal field tensor

The new coordinates are exactly `1 ⊗ z`, and their etaleness and
actual differential-basis readback are derived from the original map.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct

universe u

section Rings

variable {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
  [Algebra k L] [Algebra k A] {n : ℕ}

/-- The actual changed coordinates in the literal tensor ring. -/
def fieldTensorCoordinates (z : Fin n → A) : Fin n → L ⊗[k] A :=
  fun i => 1 ⊗ₜ[k] z i

/-- EVERY original polynomial has its literal coefficient readback. -/
theorem aeval_fieldTensorCoordinates (z : Fin n → A) (P : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval (R := L) (fieldTensorCoordinates (k := k) (L := L) z)
      (MvPolynomial.map (algebraMap k L) P) =
      (1 ⊗ₜ[k] MvPolynomial.aeval (R := k) z P : L ⊗[k] A) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact (Algebra.TensorProduct.includeRight.commutes r).symm
  | add P Q hP hQ => simp only [map_add, hP, hQ, TensorProduct.tmul_add]
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hP,
      fieldTensorCoordinates, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

/-- Etaleness of the literal new coordinate map is a producer, not an input. -/
theorem etale_fieldTensorCoordinates (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    (MvPolynomial.aeval (R := L) (fieldTensorCoordinates (k := k) (L := L) z)).toRingHom.Etale := by
  let : Algebra (MvPolynomial (Fin n) k) A := (MvPolynomial.aeval (R := k) z).toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := k) z).commutes r).symm
  let : Algebra (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    (MvPolynomial.aeval (R := L) (fieldTensorCoordinates (k := k) (L := L) z)).toAlgebra
  let : IsScalarTower L (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := L) (fieldTensorCoordinates (k := k) (L := L) z)).commutes r).symm
  let : Algebra (MvPolynomial (Fin n) k) (L ⊗[k] A) :=
    ((algebraMap A (L ⊗[k] A)).comp (algebraMap (MvPolynomial (Fin n) k) A)).toAlgebra
  let : IsScalarTower (MvPolynomial (Fin n) k) A (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k (MvPolynomial (Fin n) k) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap k (L ⊗[k] A) r = algebraMap A (L ⊗[k] A)
        (algebraMap (MvPolynomial (Fin n) k) A (algebraMap k (MvPolynomial (Fin n) k) r))
      rw [← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) A,
        ← IsScalarTower.algebraMap_apply k A (L ⊗[k] A)]
  let : IsScalarTower k (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply k L (MvPolynomial (Fin n) L),
        ← IsScalarTower.algebraMap_apply L (MvPolynomial (Fin n) L) (L ⊗[k] A),
        ← IsScalarTower.algebraMap_apply k L (L ⊗[k] A)]
  let : IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) L)
      (L ⊗[k] A) := IsScalarTower.of_algebraMap_eq fun P =>
    (aeval_fieldTensorCoordinates (k := k) (L := L) z P).symm
  let : Algebra.IsPushout (MvPolynomial (Fin n) k) A (MvPolynomial (Fin n) L)
      (L ⊗[k] A) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin n) k) L
      (MvPolynomial (Fin n) L) (T := A) (T' := L ⊗[k] A)).mp
      TensorProduct.isPushout'
  exact RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin n) k) A
    (MvPolynomial (Fin n) L) (L ⊗[k] A) hz

/-- The literal tensor spectrum square retains the actual original coefficient maps. -/
theorem isPullback_fieldTensor :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := L)
        (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct k L A).flip

end Rings

section Fields

variable {k L A : Type u} [Field k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] {n : ℕ}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The new actual etale basis is the actual transported original basis on EVERY vector. -/
theorem etaleDifferentialBasis_fieldTensorCoordinates (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    etaleDifferentialBasis (fieldTensorCoordinates (k := k) (L := L) z)
      (etale_fieldTensorCoordinates z hz) =
      fieldDifferentialBasis (L := L) (A' := L ⊗[k] A) (etaleDifferentialBasis z hz) := by
  ext i
  rw [etaleDifferentialBasis_apply, fieldDifferentialBasis_apply,
    etaleDifferentialBasis_apply, KaehlerDifferential.map_D]
  rfl

end Fields

end EnvelopeProperty.Char0
