/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SmoothFamilyDVRChart

/-!
# Actual original-source discrepancy bounds in monomial leaf coordinates

The exact original-source DVR Jacobian ideal order and the actual logarithmic
determinant bound give the leaf coordinate inequality without a supplied
discrepancy estimate, including infinite coordinate orders.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (E V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] (hEV : E ≤ V) {ι : Type u} [Fintype ι]
  {π : V} {u : ι → V} {n : ℕ}

/-- The actual leaf coordinate derivative determinant has the actual logarithmic order
bound, transported through the actual finite coordinate index equivalence. -/
theorem sum_addVal_leaf_le_one_add_dvrLeafDet (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) (v : Fin n → E) :
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (∑ i, addVal V (Subalgebra.inclusion hEV (v i))) ≤
      1 + addVal V (Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)).det := by
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let z : Option ι → V := fun j => Subalgebra.inclusion hEV (v (e.symm j))
  let M : Matrix (Option ι) (Option ι) V := Matrix.of fun i j => dvrCoordinatePartial V hπ hu j (z i)
  have h := sum_addVal_le_one_add_addVal_jacobian (dvrCoordinatePartial V hπ hu) hπ
    (dvrCoordinatePartial_uniformizer_some V hπ hu) z
  have hsum : (∑ i, addVal V (Subalgebra.inclusion hEV (v i))) = ∑ j, addVal V (z j) := by
    simpa only [z, Equiv.symm_apply_apply] using e.sum_comp (fun j => addVal V (z j))
  have hmat : (Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)) =
      Matrix.reindex e.symm e.symm M := by
    apply Matrix.ext
    intro i j
    change dvrCoordinatePartial V hπ hu (e j) (Subalgebra.inclusion hEV (v i)) =
      dvrCoordinatePartial V hπ hu (e j) (Subalgebra.inclusion hEV (v (e.symm (e i))))
    rw [Equiv.symm_apply_apply]
  have hdet : (Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)).det = M.det := by
    rw [hmat, Matrix.det_reindex_self]
  rw [hdet, hsum]
  exact h

/-- The actual original-source DVR Jacobian ideal gains exactly the actual monomial
leaf Jacobian orders, and therefore bounds the full leaf coordinate-order sum. -/
theorem dvr_original_source_leaf_logarithmic_bound (C : Subalgebra k K)
    (hCE : C ≤ E) (hCV : C ≤ V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type*} [Fintype τ] (c : τ → Fin n) (a : τ → ℕ)
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ i, v (c i) ^ a i}) :
    (∑ i, addVal V (Subalgebra.inclusion hEV (v i))) +
        (∑ l, a l • addVal V (Subalgebra.inclusion hEV (v (c l)))) ≤
      1 + dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e) := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := dvr_leaf_source_jacobian_order E V hEV C hCE hπ hu e v hv c a hJ
  rw [dvrSourceJacobianIdeal_through_leaf C V hCV E hCE hEV hπ hu e] at h
  rw [h, ← add_assoc]
  exact add_le_add (sum_addVal_leaf_le_one_add_dvrLeafDet E V hEV hπ hu e v) le_rfl

end EnvelopeProperty.Char0
