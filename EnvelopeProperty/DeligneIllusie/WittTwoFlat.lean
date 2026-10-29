import EnvelopeProperty.DeligneIllusie.WittTwo
import Mathlib.RingTheory.Flat.Basic

/-!
# Witt Two Flat

Prime exactness in the actual flat length-two Witt modules. -/

noncomputable section

open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoFlat

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
variable (M : Type*) [AddCommGroup M] [Module (WittTwo.Ring p k) M]

/-- Multiplication by the actual Witt prime scalar. -/
def primeSmul : M →ₗ[WittTwo.Ring p k] M :=
  (p : WittTwo.Ring p k) • LinearMap.id

private theorem scalar_exact :
    Function.Exact (primeSmul p k (WittTwo.Ring p k))
      (primeSmul p k (WittTwo.Ring p k)) := by
  intro x
  change (p : WittTwo.Ring p k) * x = 0 ↔ ∃ y, (p : WittTwo.Ring p k) * y = x
  rw [mul_comm (p : WittTwo.Ring p k) x, WittTwo.mul_prime_eq_zero_iff]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (WittTwo.exists_mul_prime_iff p k x).mpr hx
    exact ⟨y, (mul_comm _ _).trans hy.symm⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

omit [CharP k p] [PerfectRing k p] in
private theorem tensor_primeSmul (z : WittTwo.Ring p k ⊗[WittTwo.Ring p k] M) :
    TensorProduct.lid (WittTwo.Ring p k) M
        ((primeSmul p k (WittTwo.Ring p k)).rTensor M z) =
      (p : WittTwo.Ring p k) • TensorProduct.lid (WittTwo.Ring p k) M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [primeSmul]
  | add z w hz hw => simp [hz, hw, smul_add]

variable [Module.Flat (WittTwo.Ring p k) M]

/-- Exactness derives from flatness of the actual module and the actual scalar sequence. -/
theorem primeSmul_exact : Function.Exact (primeSmul p k M) (primeSmul p k M) := by
  have ht := Module.Flat.rTensor_exact M (scalar_exact p k)
  let e := TensorProduct.lid (WittTwo.Ring p k) M
  intro m
  constructor
  · intro hm
    have hz : (primeSmul p k (WittTwo.Ring p k)).rTensor M (e.symm m) = 0 := by
      apply e.injective
      rw [tensor_primeSmul, LinearEquiv.apply_symm_apply, map_zero]
      exact hm
    obtain ⟨z, hz⟩ := (ht (e.symm m)).mp hz
    refine ⟨e z, ?_⟩
    change (p : WittTwo.Ring p k) • e z = m
    rw [← tensor_primeSmul, hz, LinearEquiv.apply_symm_apply]
  · rintro ⟨n, rfl⟩
    change (p : WittTwo.Ring p k) • ((p : WittTwo.Ring p k) • n) = 0
    rw [← mul_smul, ← pow_two, WittTwo.prime_square_zero, zero_smul]

/-- The actual annihilator of the prime in the flat module is exactly its prime image. -/
theorem prime_smul_eq_zero_iff (m : M) :
    (p : WittTwo.Ring p k) • m = 0 ↔ ∃ n : M, m = (p : WittTwo.Ring p k) • n := by
  constructor
  · intro hm
    obtain ⟨n, hn⟩ := (primeSmul_exact p k M m).mp hm
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact (primeSmul_exact p k M m).mpr ⟨n, hn.symm⟩

/-- Equality of prime multiples is exactly equality modulo the original prime image. -/
theorem prime_smul_eq_iff (m n : M) :
    (p : WittTwo.Ring p k) • m = (p : WittTwo.Ring p k) • n ↔
      ∃ z : M, m - n = (p : WittTwo.Ring p k) • z := by
  rw [← sub_eq_zero, ← smul_sub, prime_smul_eq_zero_iff]

end EnvelopeProperty.DeligneIllusie.WittTwoFlat
