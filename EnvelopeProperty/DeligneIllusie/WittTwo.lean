import Mathlib.RingTheory.WittVector.Truncated
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.FieldTheory.Perfect

/-!
# Witt Two

Actual length-two Witt arithmetic for divided Frobenius. -/

noncomputable section

namespace EnvelopeProperty.DeligneIllusie.WittTwo

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k]

abbrev Ring := TruncatedWittVector p 2 k

/-- Reduction of the actual length-two Witt ring to its first coordinate. -/
def reduction : Ring p k →+* k :=
  RingHom.liftOfRightInverse (WittVector.truncate 2)
    TruncatedWittVector.out TruncatedWittVector.truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      change x.coeff 0 = 0
      exact (WittVector.mem_ker_truncate 2 x).mp hx 0 (by decide)⟩

@[simp] theorem reduction_apply (x : Ring p k) : reduction p k x = x.coeff 0 := by
  change x.out.coeff 0 = x.coeff 0
  exact TruncatedWittVector.coeff_out x 0

/-- Every residue has an actual truncated Teichmuller lift. -/
theorem reduction_surjective : Function.Surjective (reduction p k) := by
  intro a
  refine ⟨WittVector.truncate 2 (WittVector.teichmuller p a), ?_⟩
  rw [reduction_apply, WittVector.coeff_truncate]
  exact WittVector.teichmuller_coeff_zero p a

variable [CharP k p]

/-- The first coefficient of the actual Witt product by the prime vanishes. -/
theorem mul_prime_coeff_zero (x : Ring p k) : (x * p).coeff 0 = 0 := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k x
  rw [← map_natCast (WittVector.truncate 2) p, ← map_mul, WittVector.coeff_truncate]
  exact WittVector.mul_charP_coeff_zero y

/-- The second coefficient of the actual Witt product by the prime. -/
theorem mul_prime_coeff_one (x : Ring p k) : (x * p).coeff 1 = x.coeff 0 ^ p := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k x
  rw [← map_natCast (WittVector.truncate 2) p, ← map_mul, WittVector.coeff_truncate,
    WittVector.coeff_truncate]
  exact WittVector.mul_charP_coeff_succ y 0

/-- The annihilator of the prime is the original reduction kernel. -/
theorem mul_prime_eq_zero_iff (x : Ring p k) : x * p = 0 ↔ reduction p k x = 0 := by
  constructor
  · intro hx
    have hpow : x.coeff 0 ^ p = 0 := by
      rw [← mul_prime_coeff_one, hx, TruncatedWittVector.coeff_zero]
    rw [reduction_apply]
    by_contra h
    exact pow_ne_zero p h hpow
  · intro hx
    rw [reduction_apply] at hx
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · rw [TruncatedWittVector.coeff_zero]
      change (x * p).coeff 0 = 0
      exact mul_prime_coeff_zero p k x
    · rw [TruncatedWittVector.coeff_zero]
      change (x * p).coeff 1 = 0
      rw [mul_prime_coeff_one, hx, zero_pow (Fact.out : p.Prime).ne_zero]

/-- The actual prime element has square zero in the actual length-two Witt ring. -/
theorem prime_square_zero : (p : Ring p k) ^ 2 = 0 := by
  rw [pow_two, mul_prime_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

/-- Equality of prime multiples determines exactly equality of their residues. -/
theorem mul_prime_eq_iff (x y : Ring p k) :
    x * p = y * p ↔ reduction p k x = reduction p k y := by
  rw [← sub_eq_zero, ← sub_mul, mul_prime_eq_zero_iff, map_sub, sub_eq_zero]

variable [PerfectRing k p]

/-- Perfectness identifies the original reduction kernel with actual prime multiples. -/
theorem exists_mul_prime_iff (x : Ring p k) :
    (∃ y : Ring p k, x = y * p) ↔ reduction p k x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [reduction_apply, mul_prime_coeff_zero]
  · intro hx
    rw [reduction_apply] at hx
    let b := (frobeniusEquiv k p).symm (x.coeff 1)
    have hb : b ^ p = x.coeff 1 := (frobeniusEquiv k p).apply_symm_apply (x.coeff 1)
    refine ⟨WittVector.truncate 2 (WittVector.teichmuller p b), ?_⟩
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change x.coeff 0 = (WittVector.truncate 2 (WittVector.teichmuller p b) * p).coeff 0
      rw [mul_prime_coeff_zero, hx]
    · change x.coeff 1 = (WittVector.truncate 2 (WittVector.teichmuller p b) * p).coeff 1
      rw [mul_prime_coeff_one, WittVector.coeff_truncate]
      change x.coeff 1 = (WittVector.teichmuller p b).coeff 0 ^ p
      rw [WittVector.teichmuller_coeff_zero, hb]

end EnvelopeProperty.DeligneIllusie.WittTwo
