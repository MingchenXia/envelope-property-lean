/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRSourceJacobian
import EnvelopeProperty.Char0.DVRJacobianTransition

/-!
# Coordinate invariance of the genuine original-source DVR Jacobian ideal

Every original tuple determinant changes by the actual unit DVR coordinate
transition. Thus the genuine generated ideal and its actual normalized order
are independent of uniformizer and residue-coordinate choices.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] (hCV : C ≤ V) {ι : Type u} [Fintype ι]
  {π π' : V} {u u' : ι → V} {n : ℕ}

/-- Mapping an actual original-source DVR tuple determinant into the actual common field
is exactly the original field-coordinate Jacobian after simultaneous finite reindexing. -/
theorem coe_original_source_dvr_tuple_det (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) (w : Fin n → C) :
    letI : Algebra C V := (Subalgebra.inclusion hCV).toAlgebra
    letI : IsScalarTower k C V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    ((Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det : K) =
      jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (fun i => (w (e.symm i) : K)) := by
  let _ : Algebra C V := (Subalgebra.inclusion hCV).toAlgebra
  have : IsScalarTower k C V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M : Matrix (Fin n) (Fin n) V := Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)
  let N : Matrix (Option ι) (Option ι) K := Matrix.of fun i j =>
    partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) j (w (e.symm i) : K)
  have hM : V.val.mapMatrix M = Matrix.reindex e.symm e.symm N := by
    apply Matrix.ext
    intro i j
    change partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) (e j) (w i : K) =
      partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) (e j) (w (e.symm (e i)) : K)
    rw [Equiv.symm_apply_apply]
  have h := V.val.map_det M
  rw [hM, Matrix.det_reindex_self] at h
  exact h

/-- Every actual original-source tuple changes by the same actual unit determinant under
a change of DVR coordinates; their genuine generated ideals are therefore identical. -/
theorem dvrOriginalSourceJacobianIdeal_coordinate_independent (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (hπ' : Irreducible π')
    (hu' : IsTranscendenceBasis k (residue V ∘ u')) (e : Fin n ≃ Option ι) :
    dvrOriginalSourceJacobianIdeal C V hCV hπ hu e =
      dvrOriginalSourceJacobianIdeal C V hCV hπ' hu' e := by
  let _ : Algebra C V := (Subalgebra.inclusion hCV).toAlgebra
  have : IsScalarTower k C V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let hmem : ∀ i, dvrCoordinates π' u' i ∈ V := fun i => by cases i <;> exact Subtype.mem _
  let a : V := ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (dvrCoordinates π' u'),
    jacobian_mem hπ hu hmem⟩
  have ha : IsUnit a := isUnit_dvr_coordinate_jacobian V hπ hu hπ' hu'
  have hfactor (w : Fin n → C) :
      (Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det =
        a * (Matrix.of fun i j => dvrLeafPartials C V hCV hπ' hu' e j (w i)).det := by
    apply Subtype.ext
    change ((Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det : K) =
      (a : K) * ((Matrix.of fun i j => dvrLeafPartials C V hCV hπ' hu' e j (w i)).det : K)
    rw [coe_original_source_dvr_tuple_det C V hCV hπ hu e w,
      coe_original_source_dvr_tuple_det C V hCV hπ' hu' e w]
    exact jacobian_comp (isTranscendenceBasis_dvrCoordinates hπ hu)
      (isTranscendenceBasis_dvrCoordinates hπ' hu') (fun i => (w (e.symm i) : K))
  obtain ⟨aunit, haunit⟩ := ha
  unfold dvrOriginalSourceJacobianIdeal derivationSourceJacobianIdeal
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change (Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det ∈
      span (Set.range fun w : Fin n → C =>
        (Matrix.of fun i j => dvrLeafPartials C V hCV hπ' hu' e j (w i)).det)
    rw [hfactor w]
    exact Ideal.mul_mem_left _ a (Ideal.subset_span ⟨w, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hmem' : (Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det ∈
        span (Set.range fun w : Fin n → C =>
          (Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det) :=
      Ideal.subset_span ⟨w, rfl⟩
    have h := Ideal.mul_mem_left _ ((aunit⁻¹ : Vˣ) : V) hmem'
    have heq : ((aunit⁻¹ : Vˣ) : V) *
        (Matrix.of fun i j => dvrLeafPartials C V hCV hπ hu e j (w i)).det =
        (Matrix.of fun i j => dvrLeafPartials C V hCV hπ' hu' e j (w i)).det := by
      rw [hfactor w, ← haunit]
      simp
    rwa [heq] at h

/-- The actual normalized original-source DVR Jacobian ideal order is independent of
the actual uniformizer and residue-coordinate choices. -/
theorem dvrOriginalSourceJacobianIdeal_order_coordinate_independent (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (hπ' : Irreducible π')
    (hu' : IsTranscendenceBasis k (residue V ∘ u')) (e : Fin n ≃ Option ι) :
    dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e) =
      dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ' hu' e) :=
  congrArg dvrIdealOrder (dvrOriginalSourceJacobianIdeal_coordinate_independent C V hCV hπ hu hπ' hu' e)

end EnvelopeProperty.Char0
