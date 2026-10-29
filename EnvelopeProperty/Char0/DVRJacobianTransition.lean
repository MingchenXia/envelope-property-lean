/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRLogJacobian

/-!
# Actual field Jacobian composition and intrinsic DVR discrepancy

The actual coordinate transition matrices have inverse determinant in the
actual DVR. Hence the actual log discrepancy is independent of uniformizer
and residue-transcendence coordinate choices.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing IsLocalRing
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
  {σ : Type*} [Fintype σ] [DecidableEq σ] {w v : σ → K}

omit [DecidableEq σ] in
/-- Expanding actual field coordinate partials gives the exact derivative matrix chain rule. -/
theorem partialDeriv_matrix_comp (hw : IsTranscendenceBasis F w)
    (hv : IsTranscendenceBasis F v) (z : σ → K) :
    (Matrix.of fun i j => partialDeriv hw j (z i)) =
      (Matrix.of fun i j => partialDeriv hv j (z i)) *
        (Matrix.of fun i j => partialDeriv hw j (v i)) := by
  ext i j
  have h := congrArg (fun D : Derivation F K K => D (z i))
    (derivation_eq_sum hv (partialDeriv hw j))
  rw [sum_smul_derivation_apply] at h
  change partialDeriv hw j (z i) = ∑ l, partialDeriv hv l (z i) * partialDeriv hw j (v l)
  exact h.trans (Finset.sum_congr rfl (fun _ _ => mul_comm _ _))

/-- Actual field-coordinate Jacobians obey the exact chain rule. -/
theorem jacobian_comp (hw : IsTranscendenceBasis F w)
    (hv : IsTranscendenceBasis F v) (z : σ → K) :
    jacobian hw z = jacobian hw v * jacobian hv z := by
  rw [jacobian, partialDeriv_matrix_comp hw hv z, Matrix.det_mul]
  exact mul_comm _ _

/-- The actual self-coordinate Jacobian is one. -/
theorem jacobian_self (hw : IsTranscendenceBasis F w) : jacobian hw w = 1 := by
  have h : (Matrix.of fun i j => partialDeriv hw j (w i)) = 1 := by
    ext i j
    rw [Matrix.of_apply, partialDeriv_apply]
    rfl
  rw [jacobian, h, Matrix.det_one]

variable (V : Subalgebra F K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType F V] {ι : Type*} [Fintype ι]
  {π π' : V} {u u' : ι → V}

/-- The actual Jacobian between two genuine DVR coordinate systems is a unit of the
actual DVR; its inverse is the determinant of the reverse actual transition. -/
theorem isUnit_dvr_coordinate_jacobian (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (hπ' : Irreducible π')
    (hu' : IsTranscendenceBasis F (residue V ∘ u')) :
    IsUnit (⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u'),
      jacobian_mem hπ hu (fun i => by cases i <;> exact Subtype.mem _)⟩ : V) := by
  let hmem : ∀ i, dvrCoordinates π u i ∈ V := fun i => by cases i <;> exact Subtype.mem _
  let hmem' : ∀ i, dvrCoordinates π' u' i ∈ V := fun i => by cases i <;> exact Subtype.mem _
  let a : V := ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u'),
    jacobian_mem hπ hu hmem'⟩
  let b : V := ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ' hu') (dvrCoordinates π u),
    jacobian_mem hπ' hu' hmem⟩
  have hab : a * b = 1 := by
    apply Subtype.ext
    change jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u') *
      jacobian (isTranscendenceBasis_dvrCoordinates hπ' hu') (dvrCoordinates π u) = 1
    exact (jacobian_comp (isTranscendenceBasis_dvrCoordinates hπ hu)
      (isTranscendenceBasis_dvrCoordinates hπ' hu') (dvrCoordinates π u)).symm.trans
        (jacobian_self (isTranscendenceBasis_dvrCoordinates hπ hu))
  exact ⟨⟨a, b, hab, by simpa only [mul_comm] using hab⟩, rfl⟩

/-- The actual source-function log discrepancy is independent of actual DVR coordinates. -/
theorem logDiscrepancy_coordinate_independent (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (hπ' : Irreducible π')
    (hu' : IsTranscendenceBasis F (residue V ∘ u'))
    {z : Option ι → K} (hz : ∀ i, z i ∈ V) :
    logDiscrepancy hπ hu hz = logDiscrepancy hπ' hu' hz := by
  let hmem' : ∀ i, dvrCoordinates π' u' i ∈ V := fun i => by cases i <;> exact Subtype.mem _
  let a : V := ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u'),
    jacobian_mem hπ hu hmem'⟩
  have ha : IsUnit a := isUnit_dvr_coordinate_jacobian V hπ hu hπ' hu'
  have hJac :
      (⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) z, jacobian_mem hπ hu hz⟩ : V) =
        a * ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ' hu') z, jacobian_mem hπ' hu' hz⟩ := by
    apply Subtype.ext
    change jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) z =
      jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u') *
        jacobian (isTranscendenceBasis_dvrCoordinates hπ' hu') z
    exact jacobian_comp (isTranscendenceBasis_dvrCoordinates hπ hu)
      (isTranscendenceBasis_dvrCoordinates hπ' hu') z
  rw [logDiscrepancy, logDiscrepancy, hJac, addVal_mul, addVal_eq_zero_iff.mpr ha, zero_add]

end EnvelopeProperty.Char0
