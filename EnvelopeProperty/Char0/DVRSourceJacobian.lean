/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SmoothFamilyDVRChart
import EnvelopeProperty.Char0.JacobianSourceLocalization

/-!
# Nonzero genuine original-source DVR Jacobian ideals

Every original source-function determinant is retained under passage to the
actual fraction field. Their actual field ideal is the unit ideal, deriving
nonzero DVR Jacobian ideals and finite discrepancy orders internally.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

section CoordinateBasis

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}

/-- Actual coordinate differentials forming a basis give a genuine unit Jacobian ideal
for the identity source, without an etale finite-presentation assumption. -/
theorem affineRelativeJacobianIdeal_self_eq_top_of_coordinate_basis
    (b : Basis (Fin n) A (KaehlerDifferential k A)) (z : Fin n → A)
    (hz : ∀ i, b i = KaehlerDifferential.D k A (z i)) :
    affineRelativeJacobianIdeal (R := A) b = ⊤ := by
  have hM : sourceFunctionDifferentialMatrix (R := A) b z = 1 := by
    apply Matrix.ext
    intro i j
    change b.repr (KaehlerDifferential.D k A (algebraMap A A (z j))) i = if i = j then 1 else 0
    rw [Algebra.algebraMap_self, RingHom.id_apply, ← hz j, Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]
  apply (Ideal.eq_top_iff_one _).mpr
  have h : (sourceFunctionDifferentialMatrix (R := A) b z).det ∈
      affineRelativeJacobianIdeal (R := A) b := Ideal.subset_span ⟨z, rfl⟩
  simpa only [hM, Matrix.det_one] using h

variable {R : Type u} [CommRing R] [Algebra k R] [Algebra R A] [IsScalarTower k R A]

/-- Actual source localization preserves every original source function and makes its
field-coordinate Jacobian ideal the unit ideal. -/
theorem affineRelativeJacobianIdeal_localization_eq_top_of_coordinate_basis
    (M : Submonoid R) [IsLocalization M A]
    (b : Basis (Fin n) A (KaehlerDifferential k A)) (z : Fin n → A)
    (hz : ∀ i, b i = KaehlerDifferential.D k A (z i)) :
    affineRelativeJacobianIdeal (R := R) b = ⊤ := by
  exact (affineRelativeJacobianIdeal_source_localization (R := R) (S := A) M b).trans
    (affineRelativeJacobianIdeal_self_eq_top_of_coordinate_basis b z hz)

end CoordinateBasis

/-- Every actual nonzero DVR ideal has finite normalized ideal order. -/
theorem dvrIdealOrder_ne_top_of_ne_bot {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (J : Ideal V) (hJ : J ≠ ⊥) : dvrIdealOrder J ≠ ⊤ := by
  intro htop
  have hgen : addVal V (Submodule.IsPrincipal.generator J) = ⊤ := by
    rw [← dvrIdealOrder_span_singleton, Ideal.span_singleton_generator]
    exact htop
  apply hJ
  exact (Ideal.span_singleton_generator J).symm.trans
    (Ideal.span_singleton_eq_bot.mpr (addVal_eq_top_iff.mp hgen))

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] {ι : Type u} [Fintype ι]
  {π : V} {u : ι → V} {n : ℕ}

/-- The actual produced DVR field differential basis, with its actual finite index. -/
def dvrFieldDifferentialBasis (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    Basis (Fin n) K (KaehlerDifferential k K) :=
  (kaehlerBasisOfIsTranscendenceBasis (isTranscendenceBasis_dvrCoordinates hπ hu)).reindex e.symm

/-- Extension to the actual common field maps the genuine original-source DVR Jacobian
ideal to exactly its original-source field differential-basis Jacobian ideal. -/
theorem map_dvrOriginalSourceJacobianIdeal (C : Subalgebra k K) (hCV : C ≤ V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e).map V.val =
      affineRelativeJacobianIdeal (R := C) (dvrFieldDifferentialBasis V hπ hu e) := by
  let _ : Algebra C V := (Subalgebra.inclusion hCV).toAlgebra
  have : IsScalarTower k C V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [dvrOriginalSourceJacobianIdeal, derivationSourceJacobianIdeal, Ideal.map_span,
    ← Set.range_comp, affineRelativeJacobianIdeal]
  congr 1
  apply congrArg Set.range
  funext w
  rw [Function.comp_apply, V.val.map_det,
    ← Matrix.det_transpose (sourceFunctionDifferentialMatrix (dvrFieldDifferentialBasis V hπ hu e) w)]
  congr 1

/-- The genuine all-original-source DVR Jacobian ideal is nonzero because it becomes the
unit ideal in the actual original function field. -/
theorem dvrOriginalSourceJacobianIdeal_ne_bot (C : Subalgebra k K) [IsFractionRing C K]
    (hCV : C ≤ V) (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    dvrOriginalSourceJacobianIdeal C V hCV hπ hu e ≠ ⊥ := by
  have hcoord (i : Fin n) : dvrFieldDifferentialBasis V hπ hu e i =
      KaehlerDifferential.D k K (dvrCoordinates π u (e i)) := by
    rw [dvrFieldDifferentialBasis, Basis.reindex_apply, kaehlerBasisOfIsTranscendenceBasis_apply]
    simp only [Equiv.symm_symm]
  have htop : (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e).map V.val = ⊤ := by
    rw [map_dvrOriginalSourceJacobianIdeal V C hCV hπ hu e]
    exact affineRelativeJacobianIdeal_localization_eq_top_of_coordinate_basis
      (nonZeroDivisors C) (dvrFieldDifferentialBasis V hπ hu e)
      (fun i => dvrCoordinates π u (e i)) hcoord
  have hmapne : (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e).map V.val ≠ ⊥ := by
    rw [htop]
    exact top_ne_bot
  exact Ideal.ne_bot_of_map_ne_bot hmapne

/-- The actual original-source DVR Jacobian ideal has finite normalized order; no
nonzero-Jacobian or finite-discrepancy premise is supplied. -/
theorem dvrOriginalSourceJacobianIdeal_order_ne_top (C : Subalgebra k K) [IsFractionRing C K]
    (hCV : C ≤ V) (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e) ≠ ⊤ :=
  dvrIdealOrder_ne_top_of_ne_bot _ (dvrOriginalSourceJacobianIdeal_ne_bot V C hCV hπ hu e)

end EnvelopeProperty.Char0
