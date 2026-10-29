/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ValuativeMultiplierFunctoriality

/-!
# Exact power rescaling of full intrinsic multiplier ideals

All actual divisorial DVRs and every original-source Jacobian contribution
are retained. This supplies the power identity needed by genuine asymptotic
multiplier ideals, without subadditivity or a generation hypothesis.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

/-- Actual DVR ideal order commutes with every actual ideal power. -/
theorem dvrIdealOrder_pow {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (J : Ideal V) (r : ℕ) :
    dvrIdealOrder (J ^ r) = r • dvrIdealOrder J := by
  induction r with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, zero_nsmul]
    have htop : (span {(1 : V)} : Ideal V) = ⊤ := by simp
    rw [← htop, dvrIdealOrder_span_singleton, addVal_one]
  | succ r ih => rw [pow_succ, dvrIdealOrder_mul, ih, succ_nsmul]

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- Every actual original-source divisorial contribution has exact power
rescaling, with unchanged original-source discrepancy and all rational exponents. -/
theorem intrinsicDVRMultiplierContribution_pow
    (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCV : C ≤ V) (I : Ideal C) (hI : I ≠ ⊥)
    (r : ℕ) (q : ℚ) :
    intrinsicDVRMultiplierContribution C V hCV (I ^ r) (pow_ne_zero r hI) q =
      intrinsicDVRMultiplierContribution C V hCV I hI ((r : ℚ) * q) := by
  have horder : dvrIdealOrder ((I ^ r).map (Subalgebra.inclusion hCV).toRingHom) =
      (r : ℕ∞) * dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) := by
    rw [Ideal.map_pow, dvrIdealOrder_pow, nsmul_eq_mul]
  have hmul : q * (((r : ℕ) * (dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℕ) : ℚ) =
      ((r : ℚ) * q) * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) := by
    push_cast
    ring
  ext f
  rw [mem_intrinsicDVRMultiplierContribution_iff, mem_intrinsicDVRMultiplierContribution_iff,
    horder, ENat.toNat_mul, ENat.toNat_natCast, hmul]

/-- The full all-divisorial-DVR multiplier ideal commutes exactly with original
ideal powers and the corresponding rational-exponent scaling. -/
theorem valuativeMultiplierIdeal_pow
    (C : Subalgebra k K) [IsFractionRing C K] (I : Ideal C) (hI : I ≠ ⊥)
    (r : ℕ) (q : ℚ) :
    valuativeMultiplierIdeal C (I ^ r) (pow_ne_zero r hI) q =
      valuativeMultiplierIdeal C I hI ((r : ℚ) * q) := by
  apply iInf_congr
  intro D
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  exact intrinsicDVRMultiplierContribution_pow C D.val D.property.1 I hI r q

end EnvelopeProperty.Char0
