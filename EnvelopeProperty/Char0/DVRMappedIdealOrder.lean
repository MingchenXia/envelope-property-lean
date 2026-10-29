import EnvelopeProperty.Char0.ValuativeMultiplierFunctoriality

/-!
# Original members attaining mapped DVR ideal orders

The order of a nonzero ideal extended to a DVR is attained by the image of an
original member. The proof uses the entire mapped ideal and its actual finite
order, without choosing a generator preimage or assuming injectivity.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing

private theorem dvrIdealOrder_maximalIdeal_pow
    {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r : ℕ) :
    dvrIdealOrder (IsLocalRing.maximalIdeal V ^ r) = (r : ℕ∞) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, dvrIdealOrder_span_singleton,
    hπ.addVal_pow]

/-- A nonzero ideal extended to a DVR has its actual order attained by an
original nonzero member, for an arbitrary original ring homomorphism. -/
theorem exists_mem_eq_dvrIdealOrder_map
    {R : Type*} {V : Type*} [CommRing R] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (g : R →+* V) (I : Ideal R) (hmap : I.map g ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ addVal V (g x) = dvrIdealOrder (I.map g) := by
  have hfinite := dvrIdealOrder_ne_top_of_ne_bot (I.map g) hmap
  let r := (dvrIdealOrder (I.map g)).toNat
  have hr : (r : ℕ∞) = dvrIdealOrder (I.map g) := ENat.natCast_toNat hfinite
  have hexists : ∃ x ∈ I, addVal V (g x) ≤ dvrIdealOrder (I.map g) := by
    by_contra hnone
    have hmap_le : I.map g ≤ IsLocalRing.maximalIdeal V ^ (r + 1) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      apply (mem_dvr_maximalIdeal_pow_iff (r + 1) (g x)).mpr
      have hgt : (r : ℕ∞) < addVal V (g x) := by
        rw [hr]
        exact lt_of_not_ge (fun hle => hnone ⟨x, hx, hle⟩)
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENat.natCast_add_one_le_iff.mpr hgt)
    have horder := dvrIdealOrder_antitone hmap_le
    rw [dvrIdealOrder_maximalIdeal_pow, ← hr] at horder
    have hnat : r + 1 ≤ r := by exact_mod_cast horder
    omega
  obtain ⟨x, hx, hle⟩ := hexists
  have heq : addVal V (g x) = dvrIdealOrder (I.map g) :=
    le_antisymm hle (iInf₂_le (g x) (Ideal.mem_map_of_mem g hx))
  refine ⟨x, hx, ?_, heq⟩
  intro hxzero
  apply hfinite
  rw [← heq, hxzero, map_zero, addVal_zero]

end EnvelopeProperty.Char0
