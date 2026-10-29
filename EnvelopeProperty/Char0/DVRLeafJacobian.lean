/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleDerivationJacobian
import EnvelopeProperty.Char0.DVRLogJacobian

/-!
# Actual original-source Jacobian ideals in contained DVRs

The actual DVR coordinate partials compose with the literal leaf inclusion.
The actual all-original-functions Jacobian ideal factors by the genuine leaf
monomial Jacobian, with an exact normalized ideal-order formula.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

section IdealOrder

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- The normalized order of an actual DVR ideal, including the zero ideal. -/
def dvrIdealOrder (J : Ideal V) : ℕ∞ := ⨅ x ∈ J, addVal V x

/-- Actual principal-ideal order is exactly the order of the actual generator. -/
theorem dvrIdealOrder_span_singleton (x : V) : dvrIdealOrder (span {x}) = addVal V x := by
  apply le_antisymm (iInf₂_le x (Ideal.subset_span (Set.mem_singleton x)))
  apply le_iInf₂
  intro y hy
  exact addVal_le_iff_dvd.mpr (Ideal.mem_span_singleton.mp hy)

/-- Actual product ideal orders add, including zero ideals. -/
theorem dvrIdealOrder_mul (J L : Ideal V) :
    dvrIdealOrder (J * L) = dvrIdealOrder J + dvrIdealOrder L := by
  conv_lhs => rw [← Ideal.span_singleton_generator J, ← Ideal.span_singleton_generator L]
  rw [Ideal.span_singleton_mul_span_singleton, dvrIdealOrder_span_singleton, addVal_mul]
  rw [← dvrIdealOrder_span_singleton, Ideal.span_singleton_generator,
    ← dvrIdealOrder_span_singleton, Ideal.span_singleton_generator]

end IdealOrder

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (E V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] (hEV : E ≤ V) {ι : Type u} [Fintype ι]
  {π : V} {u : ι → V} {n : ℕ}

/-- Actual DVR partials restricted through the original literal leaf inclusion. -/
def dvrLeafPartials (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    Fin n → Derivation k E V := by
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact fun j => (dvrCoordinatePartial V hπ hu (e j)).compAlgebraMap E

/-- The actual all-original-source DVR derivative Jacobian ideal has the exact actual
leaf monomial factor, under the literal inclusion maps. -/
theorem dvr_leaf_source_jacobian_ideal (C : Subalgebra k K) (hCE : C ≤ E)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type*} [Fintype τ] (c : τ → Fin n) (a : τ → ℕ)
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ i, v (c i) ^ a i}) :
    letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    derivationSourceJacobianIdeal (R := C) (dvrLeafPartials E V hEV hπ hu e) =
      span {(Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)).det *
        ∏ i, (Subalgebra.inclusion hEV (v (c i))) ^ a i} := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := derivationSourceJacobianIdeal_eq (R := C) v hv (dvrLeafPartials E V hEV hπ hu e)
  rw [hJ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton] at h
  have hmap (x : E) : algebraMap E V x = Subalgebra.inclusion hEV x := rfl
  simpa only [map_prod, map_pow, hmap] using h

/-- The exact original-source DVR Jacobian ideal order includes the actual leaf
Jacobian monomial order, with all coefficients and maps unchanged. -/
theorem dvr_leaf_source_jacobian_order (C : Subalgebra k K) (hCE : C ≤ E)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type*} [Fintype τ] (c : τ → Fin n) (a : τ → ℕ)
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ i, v (c i) ^ a i}) :
    letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    dvrIdealOrder (derivationSourceJacobianIdeal (R := C) (dvrLeafPartials E V hEV hπ hu e)) =
      addVal V (Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)).det +
        ∑ i, a i • addVal V (Subalgebra.inclusion hEV (v (c i))) := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [dvr_leaf_source_jacobian_ideal E V hEV C hCE hπ hu e v hv c a hJ,
    dvrIdealOrder_span_singleton, addVal_mul]
  congr 1
  have hprod (s : Finset τ) :
      addVal V (∏ i ∈ s, Subalgebra.inclusion hEV (v (c i)) ^ a i) =
        ∑ i ∈ s, a i • addVal V (Subalgebra.inclusion hEV (v (c i))) := by
    induction s using Finset.induction_on with
    | empty => exact addVal_one
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, addVal_pow, ih]
  exact hprod Finset.univ

end EnvelopeProperty.Char0
