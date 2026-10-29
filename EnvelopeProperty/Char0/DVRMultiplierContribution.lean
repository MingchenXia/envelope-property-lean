/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRSourceCoordinateInvariant
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Actual divisorial contributions to valuative multiplier ideals

The cutoff uses the actual finite ideal order and the genuine finite
original-source DVR Jacobian order. It defines an actual inverse-image ideal,
with exact strict-discrepancy membership and the exponent-one inclusion.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

/-- Actual DVR maximal-ideal power membership is exactly the normalized order cutoff. -/
theorem mem_dvr_maximalIdeal_pow_iff {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (N : ℕ) (x : V) :
    x ∈ IsLocalRing.maximalIdeal V ^ N ↔ (N : ℕ∞) ≤ addVal V x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hπ.addVal_pow]

/-- The natural cutoff is exactly the strict discrepancy inequality, for every rational
exponent and finite integer orders. -/
theorem multiplier_cutoff_le_iff (q : ℚ) (i j r : ℕ) :
    ⌊q * (i : ℚ)⌋₊ - j ≤ r ↔ q * (i : ℚ) < (r : ℚ) + 1 + j := by
  rw [Nat.sub_le_iff_le_add, ← Nat.lt_succ_iff, Nat.floor_lt' (Nat.succ_ne_zero (r + j))]
  push_cast
  ring_nf

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (C V : Subalgebra k K) [IsFractionRing C K]
  [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
  (hCV : C ≤ V) {ι : Type u} [Fintype ι] {π : V} {u : ι → V} {n : ℕ}

omit [CharZero k] [IsFractionRing C K] [IsFractionRing V K] [Algebra.EssFiniteType k V] in
/-- An actual nonzero original ideal has finite actual order after literal extension
to the actual DVR; no finite-ideal-order premise is assumed. -/
theorem dvrIdealOrder_map_inclusion_ne_top (I : Ideal C) (hI : I ≠ ⊥) :
    dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) ≠ ⊤ :=
  dvrIdealOrder_ne_top_of_ne_bot _
    ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCV)).mp.mt hI)

/-- The actual inverse-image DVR cutoff ideal, using the genuine original-source
Jacobian ideal order. On smooth sources this is the valuative multiplier contribution. -/
def dvrMultiplierContribution (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (I : Ideal C) (_hI : I ≠ ⊥) (q : ℚ) : Ideal C :=
  (IsLocalRing.maximalIdeal V ^
    (⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ -
      (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat)).comap
    (Subalgebra.inclusion hCV).toRingHom

omit [IsFractionRing C K] in
/-- Exact membership in the actual inverse-image DVR ideal. -/
theorem mem_dvrMultiplierContribution_iff_order (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C) :
    f ∈ dvrMultiplierContribution C V hCV hπ hu e I hI q ↔
      ((⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ -
        (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat : ℕ) : ℕ∞) ≤
          addVal V (Subalgebra.inclusion hCV f) := by
  rw [dvrMultiplierContribution, Ideal.mem_comap, mem_dvr_maximalIdeal_pow_iff]
  rfl

omit [IsFractionRing C K] in
/-- The actual ideal contribution is exactly the strict finite discrepancy condition,
with zero handled by its genuine ideal membership. -/
theorem mem_dvrMultiplierContribution_iff_strict (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C) :
    f ∈ dvrMultiplierContribution C V hCV hπ hu e I hI q ↔ f = 0 ∨
      q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) <
        ((addVal V (Subalgebra.inclusion hCV f)).toNat : ℚ) + 1 +
          (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat := by
  by_cases hf : f = 0
  · subst f
    simp
  · simp only [hf, false_or]
    rw [mem_dvrMultiplierContribution_iff_order]
    have hval : addVal V (Subalgebra.inclusion hCV f) ≠ ⊤ := by
      rw [ne_eq, addVal_eq_top_iff]
      exact (map_ne_zero_iff _ (Subalgebra.inclusion_injective hCV)).mpr hf
    rw [← ENat.natCast_toNat hval, ENat.natCast_le_natCast, multiplier_cutoff_le_iff]
    simp

omit [IsFractionRing C K] in
/-- The original ideal is contained in its genuine exponent-one DVR contribution. -/
theorem le_dvrMultiplierContribution_one (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (I : Ideal C) (hI : I ≠ ⊥) : I ≤ dvrMultiplierContribution C V hCV hπ hu e I hI 1 := by
  intro f hf
  rw [mem_dvrMultiplierContribution_iff_order]
  have hfinite := dvrIdealOrder_map_inclusion_ne_top C V hCV I hI
  have hval : dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) ≤
      addVal V (Subalgebra.inclusion hCV f) :=
    iInf₂_le _ (Ideal.mem_map_of_mem _ hf)
  apply le_trans _ hval
  rw [← ENat.natCast_toNat hfinite, ENat.natCast_le_natCast]
  simp only [one_mul, Nat.floor_natCast]
  exact Nat.sub_le _ _

end EnvelopeProperty.Char0
