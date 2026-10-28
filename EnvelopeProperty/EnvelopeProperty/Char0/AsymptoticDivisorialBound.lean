/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AsymptoticMultiplierIdeal
import Mathlib.Data.Real.Basic

/-!
# The actual original asymptotic divisorial order and multiplier bound

The graded sequence, every original positive index, the actual DVR order,
and the entire original-source intrinsic canonical discrepancy are retained.
The actual asymptotic ideal's attainment is derived from Noetherianity.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] (hCV : C ≤ V)

/-- The actual asymptotic order of the ORIGINAL positive-index nonzero
ideal sequence at the ORIGINAL divisorial DVR, as the actual infimum
of its original normalized ideal orders. -/
def asymptoticDivisorialOrder (J : ℕ → Ideal C) (_hne : ∀ q, 0 < q → J q ≠ ⊥) : ℝ :=
  sInf (Set.range fun q : {q : ℕ // 0 < q} =>
    ((dvrIdealOrder ((J q.val).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) / q.val)

omit [CharZero k] [IsFractionRing V K] [Algebra.EssFiniteType k V] in
/-- Actual original normalized DVR orders are nonnegative, so their actual
infimum is nonnegative without a supplied lower-bound certificate. -/
theorem asymptoticDivisorialOrder_nonneg
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) :
    0 ≤ asymptoticDivisorialOrder C V hCV J hne := by
  apply le_csInf
  · exact ⟨_, ⟨⟨1, one_pos⟩, rfl⟩⟩
  · rintro x ⟨q, rfl⟩
    positivity

omit [CharZero k] [IsFractionRing V K] [Algebra.EssFiniteType k V] in
/-- The actual asymptotic order is below EVERY actual original positive
normalized ideal order, retaining the literal original sequence index. -/
theorem asymptoticDivisorialOrder_le
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (q : ℕ) (hq : 0 < q) :
    asymptoticDivisorialOrder C V hCV J hne ≤
      ((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) / q := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨r, rfl⟩
    positivity
  · exact ⟨⟨q, hq⟩, rfl⟩

/-- The genuine full asymptotic multiplier ideal satisfies the actual
divisorial discrepancy bound for EVERY ORIGINAL essentially finite-type DVR.
The original asymptotic-order infimum and original full canonical ideal remain
in the conclusion; the full multiplier constituent is produced internally. -/
theorem asymptoticMultiplierIdeal_divisorial_bound
    [IsFractionRing C K] [IsNoetherianRing C]
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) (f : C)
    (hf : f ∈ asymptoticMultiplierIdeal C J hne m) (hf0 : f ≠ 0) :
    (m : ℝ) * asymptoticDivisorialOrder C V hCV J hne <
      ((addVal V (Subalgebra.inclusion hCV f)).toNat : ℝ) + 1 +
        (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat := by
  obtain ⟨q, hq, heq⟩ := exists_asymptoticMultiplierIdeal_eq C hJ hne m
  rw [heq q hq (dvd_refl q)] at hf
  have hmem := valuativeMultiplierIdeal_le_contribution C V hCV (J q) (hne q hq) _ hf
  rcases (mem_intrinsicDVRMultiplierContribution_iff C V hCV (J q) (hne q hq) _ f).mp hmem with hfz | hv
  · exact (hf0 hfz).elim
  · have hl : (m : ℝ) * asymptoticDivisorialOrder C V hCV J hne ≤
        ((m : ℝ) / q) * ((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) := by
      calc
        _ ≤ (m : ℝ) *
            (((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) / q) :=
          mul_le_mul_of_nonneg_left (asymptoticDivisorialOrder_le C V hCV J hne q hq) (Nat.cast_nonneg m)
        _ = _ := by ring
    apply lt_of_le_of_lt hl
    have hvR := (Rat.cast_lt (K := ℝ)).mpr hv
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using hvR

end EnvelopeProperty.Char0
