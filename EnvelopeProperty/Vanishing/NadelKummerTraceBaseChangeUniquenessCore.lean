import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Defs

/-! # Native finite-free algebra trace on the actual tensor algebra -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

open scoped TensorProduct

variable {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Module.Free A B] [Module.Finite A B]

/-- Native algebra trace on the actual original unit pure tensor. -/
theorem trace_one_tmul (b : B) :
    Algebra.trace S (S ⊗[A] B) (1 ⊗ₜ[A] b) = algebraMap A S (Algebra.trace A B b) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rfl

/-- Native algebra trace on every actual original pure tensor. -/
theorem trace_tmul (s : S) (b : B) :
    Algebra.trace S (S ⊗[A] B) (s ⊗ₜ[A] b) =
      s * algebraMap A S (Algebra.trace A B b) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, smul_eq_mul, trace_one_tmul]

/-- A proved whole native trace normalization survives the actual tensor extension. -/
theorem trace_eq_extended_coefficient (ℓ : B →ₗ[A] A) (j : B)
    (h : ∀ b, Algebra.trace A B b = ℓ (j * b)) (c : S ⊗[A] B) :
    Algebra.trace S (S ⊗[A] B) c =
      Module.Dual.baseChange S ℓ ((1 ⊗ₜ[A] j) * c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [trace_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Module.Dual.baseChange_apply_tmul, one_mul, Algebra.smul_def, h]
    exact mul_comm _ _
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

end EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness
