import EnvelopeProperty.Char0.CharacteristicZeroMultiplierSubadditivity
import EnvelopeProperty.Char0.MultiplierPowerRescaling

/-!
# Subadditivity at natural multiples of a rational exponent

Ordinary full valuative multiplier subadditivity applied to the original ideal
powers gives additive subadditivity at natural multiples of any rational level.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry

universe u

/-- Full multiplier subadditivity at natural multiples of a common rational
level on the original smooth affine algebra. -/
theorem valuativeMultiplierIdeal_add_nat_mul_le
    {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
    (C : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) (m n : ℕ) (q : ℚ) :
    valuativeMultiplierIdeal C I hI (((m + n : ℕ) : ℚ) * q) ≤
      valuativeMultiplierIdeal C I hI ((m : ℚ) * q) *
        valuativeMultiplierIdeal C I hI ((n : ℚ) * q) := by
  have h := valuativeMultiplierIdeal_mul_le C (I ^ m) (I ^ n)
    (pow_ne_zero m hI) (pow_ne_zero n hI) q
  have hleft := valuativeMultiplierIdeal_pow C I hI (m + n) q
  simp only [pow_add] at hleft
  rw [hleft,
    valuativeMultiplierIdeal_pow C I hI m q,
    valuativeMultiplierIdeal_pow C I hI n q] at h
  exact h

end EnvelopeProperty.Char0
