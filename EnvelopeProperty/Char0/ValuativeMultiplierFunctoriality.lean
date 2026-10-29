/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal

/-!
# Elementary properties of actual valuative multiplier ideals

Every statement concerns the genuine full intersection of original-source
DVR cutoff ideals. In particular, no subadditivity or generation hypothesis
is introduced.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

/-- Inclusion reverses actual DVR ideal orders, including the zero ideal. -/
theorem dvrIdealOrder_antitone {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {I J : Ideal V} (hIJ : I ≤ J) :
    dvrIdealOrder J ≤ dvrIdealOrder I := by
  apply le_iInf₂
  intro x hx
  exact iInf₂_le x (hIJ hx)

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

section DVR

variable (C V : Subalgebra k K) [IsDiscreteValuationRing V]
  [IsFractionRing V K] [Algebra.EssFiniteType k V] (hCV : C ≤ V)

/-- Increasing the exponent decreases each actual intrinsic DVR contribution. -/
theorem intrinsicDVRMultiplierContribution_antitone_exponent
    (I : Ideal C) (hI : I ≠ ⊥) {q q' : ℚ} (hqq' : q ≤ q') :
    intrinsicDVRMultiplierContribution C V hCV I hI q' ≤
      intrinsicDVRMultiplierContribution C V hCV I hI q := by
  intro f hf
  rw [mem_intrinsicDVRMultiplierContribution_iff] at hf ⊢
  rcases hf with hf | hf
  · exact Or.inl hf
  · exact Or.inr (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hqq' (Nat.cast_nonneg _)) hf)

/-- Enlarging the original ideal enlarges its actual DVR contribution at every
nonnegative rational exponent. -/
theorem intrinsicDVRMultiplierContribution_mono_ideal
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I ≤ J) (q : ℚ) (hq : 0 ≤ q) :
    intrinsicDVRMultiplierContribution C V hCV I hI q ≤
      intrinsicDVRMultiplierContribution C V hCV J hJ q := by
  have hord := dvrIdealOrder_antitone (Ideal.map_mono (f :=
    (Subalgebra.inclusion hCV).toRingHom) hIJ)
  have hn := ENat.toNat_le_toNat hord (dvrIdealOrder_map_inclusion_ne_top C V hCV I hI)
  have hrat : ((dvrIdealOrder (J.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) ≤
      ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) := by
    exact_mod_cast hn
  intro f hf
  rw [mem_intrinsicDVRMultiplierContribution_iff] at hf ⊢
  rcases hf with hf | hf
  · exact Or.inl hf
  · exact Or.inr (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrat hq) hf)

/-- At a nonpositive exponent the actual intrinsic DVR contribution is the unit ideal. -/
theorem intrinsicDVRMultiplierContribution_eq_top_of_nonpos
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (hq : q ≤ 0) :
    intrinsicDVRMultiplierContribution C V hCV I hI q = ⊤ := by
  apply top_le_iff.mp
  intro f _
  rw [mem_intrinsicDVRMultiplierContribution_iff]
  apply Or.inr
  have hmul : q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hq (Nat.cast_nonneg _)
  exact lt_of_le_of_lt hmul (by positivity)

/-- Multiplication by the actual original ideal shifts the actual DVR contribution
by one, using additivity of the genuine DVR order on every original product. -/
theorem mul_intrinsicDVRMultiplierContribution_le_shift
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    I * intrinsicDVRMultiplierContribution C V hCV I hI q ≤
      intrinsicDVRMultiplierContribution C V hCV I hI (q + 1) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  rw [mem_intrinsicDVRMultiplierContribution_iff] at hg ⊢
  by_cases hf0 : f = 0
  · exact Or.inl (by simp [hf0])
  rcases hg with hg0 | hg
  · exact Or.inl (by simp [hg0])
  by_cases hg0 : g = 0
  · exact Or.inl (by simp [hg0])
  apply Or.inr
  have hfv : addVal V (Subalgebra.inclusion hCV f) ≠ ⊤ := by
    rw [ne_eq, addVal_eq_top_iff]
    exact (map_ne_zero_iff _ (Subalgebra.inclusion_injective hCV)).mpr hf0
  have hgv : addVal V (Subalgebra.inclusion hCV g) ≠ ⊤ := by
    rw [ne_eq, addVal_eq_top_iff]
    exact (map_ne_zero_iff _ (Subalgebra.inclusion_injective hCV)).mpr hg0
  have hle : dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) ≤
      addVal V (Subalgebra.inclusion hCV f) :=
    iInf₂_le _ (Ideal.mem_map_of_mem _ hf)
  have hn := ENat.toNat_le_toNat hle hfv
  have hrat : ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) ≤
      ((addVal V (Subalgebra.inclusion hCV f)).toNat : ℚ) := by exact_mod_cast hn
  rw [map_mul, addVal_mul, ENat.toNat_add hfv hgv, Nat.cast_add]
  nlinarith

end DVR

section FullIntersection

variable (C : Subalgebra k K) [IsFractionRing C K]

/-- Increasing the exponent decreases the actual full valuative multiplier ideal. -/
theorem valuativeMultiplierIdeal_antitone_exponent
    (I : Ideal C) (hI : I ≠ ⊥) {q q' : ℚ} (hqq' : q ≤ q') :
    valuativeMultiplierIdeal C I hI q' ≤ valuativeMultiplierIdeal C I hI q := by
  apply iInf_mono
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  exact intrinsicDVRMultiplierContribution_antitone_exponent C D.val D.property.1 I hI hqq'

/-- Enlarging a nonzero original ideal enlarges its actual full valuative multiplier
ideal at a nonnegative exponent. -/
theorem valuativeMultiplierIdeal_mono_ideal
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I ≤ J) (q : ℚ) (hq : 0 ≤ q) :
    valuativeMultiplierIdeal C I hI q ≤ valuativeMultiplierIdeal C J hJ q := by
  apply iInf_mono
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  exact intrinsicDVRMultiplierContribution_mono_ideal C D.val D.property.1 I J hI hJ hIJ q hq

/-- Nonpositive rational exponents give the actual unit multiplier ideal. -/
theorem valuativeMultiplierIdeal_eq_top_of_nonpos
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (hq : q ≤ 0) :
    valuativeMultiplierIdeal C I hI q = ⊤ := by
  apply top_le_iff.mp
  apply le_iInf
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  rw [intrinsicDVRMultiplierContribution_eq_top_of_nonpos C D.val D.property.1 I hI q hq]

/-- Multiplication by the original ideal shifts the actual full valuative multiplier
ideal by one; both sides retain every actual divisorial DVR. -/
theorem mul_valuativeMultiplierIdeal_le_shift
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    I * valuativeMultiplierIdeal C I hI q ≤ valuativeMultiplierIdeal C I hI (q + 1) := by
  apply le_iInf
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  apply Ideal.mul_le.mpr
  intro f hf g hg
  exact mul_intrinsicDVRMultiplierContribution_le_shift C D.val D.property.1 I hI q
    (Ideal.mul_mem_mul hf
      (valuativeMultiplierIdeal_le_contribution C D.val D.property.1 I hI q hg))

end FullIntersection

end EnvelopeProperty.Char0
