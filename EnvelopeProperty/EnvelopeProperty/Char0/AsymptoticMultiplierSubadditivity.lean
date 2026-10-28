import EnvelopeProperty.Char0.AsymptoticMultiplierIdeal
import EnvelopeProperty.Char0.MultiplierExponentSubadditivity

/-!
# Subadditivity of the full asymptotic multiplier ideals

The complete ideal join over the original positive-index family is subadditive
on a smooth affine algebra. The proof works on each genuine constituent, without
requiring gradedness or attainment of the join.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable (C : Subalgebra k K) [IsFractionRing C K]
variable [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]

/-- The full asymptotic multiplier ideal of the original positive-index family
is additively subadditive, with no gradedness or attainment hypothesis. -/
theorem asymptoticMultiplierIdeal_add_le
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m n : ℕ) :
    asymptoticMultiplierIdeal C J hne (m + n) ≤
      asymptoticMultiplierIdeal C J hne m * asymptoticMultiplierIdeal C J hne n := by
  apply iSup₂_le
  intro p hp
  refine le_trans ?_ (mul_le_mul'
    (valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal C J hne m hp)
    (valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal C J hne n hp))
  simpa only [mul_one_div] using
    (valuativeMultiplierIdeal_add_nat_mul_le C (J p) (hne p hp) m n (1 / (p : ℚ)))

/-- The full original asymptotic multiplier ideals satisfy the natural-power
bound, including zero indices and powers. -/
theorem asymptoticMultiplierIdeal_mul_le_pow
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m ℓ : ℕ) :
    asymptoticMultiplierIdeal C J hne (m * ℓ) ≤
      asymptoticMultiplierIdeal C J hne m ^ ℓ := by
  induction ℓ with
  | zero =>
    rw [Nat.mul_zero, pow_zero, Ideal.one_eq_top]
    exact le_top
  | succ ℓ ih =>
    rw [Nat.mul_succ, pow_succ]
    exact le_trans (asymptoticMultiplierIdeal_add_le C J hne (m * ℓ) m)
      (mul_le_mul' ih le_rfl)

end EnvelopeProperty.Char0
