/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgebraicFractionLocalization
import Mathlib.RingTheory.Localization.BaseChange

open scoped nonZeroDivisors TensorProduct
noncomputable section
namespace EnvelopeProperty.AlgebraicFraction
variable {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.IsAlgebraic A B]
  [CommRing K] [Algebra A K] [IsFractionRing A K]
  [CommRing L] [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [Algebra K L] [IsScalarTower A K L] in
/-- Actual fraction scalar extension as a whole original-base algebra, before any separate fraction-coefficient action is chosen. -/
def tensorFractionEquivOverBase (hinj : Function.Injective (algebraMap A B)) :
    K ⊗[A] B ≃ₐ[A] L := by
  let := fraction_isLocalization (A := A) (B := B) L hinj
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) (K ⊗[A] B) L).restrictScalars A

omit [Algebra K L] [IsScalarTower A K L] in
/-- The original-base fraction comparison preserves every original element. -/
theorem tensorFractionEquivOverBase_one_tmul (hinj : Function.Injective (algebraMap A B)) (b : B) :
    tensorFractionEquivOverBase (K := K) (L := L) hinj (1 ⊗ₜ[A] b) = algebraMap B L b := by
  let := fraction_isLocalization (A := A) (B := B) L hinj
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) (K ⊗[A] B) L).commutes b

/-- Actual coefficient scalar extension is the true original fraction algebra, on the unchanged original maps. -/
def tensorFractionEquiv (hinj : Function.Injective (algebraMap A B)) :
    K ⊗[A] B ≃ₐ[K] L :=
  (tensorFractionEquivOverBase (K := K) (L := L) hinj).extendScalarsOfIsLocalization K A⁰

/-- The actual generic fraction comparison retains every whole original B element. -/
theorem tensorFractionEquiv_one_tmul (hinj : Function.Injective (algebraMap A B)) (b : B) :
    tensorFractionEquiv (K := K) (L := L) hinj (1 ⊗ₜ[A] b) = algebraMap B L b := by
  let := fraction_isLocalization (A := A) (B := B) L hinj
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) (K ⊗[A] B) L).commutes b

/-- All actual coefficient and original-element values are preserved by the genuine generic algebra comparison. -/
theorem tensorFractionEquiv_tmul (hinj : Function.Injective (algebraMap A B)) (k : K) (b : B) :
    tensorFractionEquiv (K := K) (L := L) hinj (k ⊗ₜ[A] b) =
      algebraMap K L k * algebraMap B L b := by
  have h : k ⊗ₜ[A] b = algebraMap K (K ⊗[A] B) k * (1 ⊗ₜ[A] b) := by
    change k ⊗ₜ[A] b = (k ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ[A] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, AlgEquiv.commutes, tensorFractionEquiv_one_tmul]

end EnvelopeProperty.AlgebraicFraction
