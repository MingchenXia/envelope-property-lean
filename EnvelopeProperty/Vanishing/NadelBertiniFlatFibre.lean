import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Flat actual principal fibres remain Cartier

Flatness is required only of the actual principal quotient over the
original base. Tensor coefficients may be nonflat, disconnected or zero.
-/

noncomputable section
open scoped TensorProduct
universe u v w

namespace EnvelopeProperty.Vanishing.NadelBertiniFlatFibre

variable (R : Type u) [CommRing R] {B : Type v} [CommRing B] [Algebra R B] (h : B)

/-- Actual multiplication by the original equation, with its original base action. -/
def mulMap : B →ₗ[R] B where
  toFun b := h * b
  map_add' b c := mul_add h b c
  map_smul' r b := by simp only [RingHom.id_apply, Algebra.smul_def, mul_left_comm]

/-- The actual principal quotient map, retaining the original base ring. -/
def quotientMap : B →ₗ[R] B ⧸ Ideal.span ({h} : Set B) :=
  (Ideal.Quotient.mkₐ R (Ideal.span ({h} : Set B))).toLinearMap

/-- The full principal quotient sequence is exact over the original base. -/
theorem mulMap_exact : Function.Exact (mulMap R h) (quotientMap R h) := by
  intro b
  change Ideal.Quotient.mk (Ideal.span ({h} : Set B)) b = 0 ↔ ∃ a, h * a = b
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

/-- The actual flat principal quotient makes tensor multiplication injective,
even for nonflat tensor coefficients. -/
theorem mulMap_lTensor_injective (hh : IsSMulRegular B h)
    [Module.Flat R (B ⧸ Ideal.span ({h} : Set B))]
    (S : Type w) [AddCommGroup S] [Module R S] :
    Function.Injective ((mulMap R h).lTensor S) :=
  LinearMap.lTensor_injective_of_exact_of_flat (quotientMap R h)
    (Ideal.Quotient.mk_surjective) (mulMap R h) hh (mulMap_exact R h) S

/-- The entire tensor linear map is actual multiplication in the actual algebra. -/
theorem mulMap_lTensor_apply (S : Type w) [CommRing S] [Algebra R S]
    (z : S ⊗[R] B) :
    (mulMap R h).lTensor S z = ((1 : S) ⊗ₜ[R] h) * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul s b =>
      change s ⊗ₜ[R] (h * b) = ((1 : S) ⊗ₜ[R] h) * (s ⊗ₜ[R] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add z t hz ht => simpa only [map_add, mul_add] using congrArg₂ (· + ·) hz ht

/-- Every actual scalar fibre of a flat principal quotient remains Cartier. -/
theorem tensor_regular (hh : IsSMulRegular B h)
    [Module.Flat R (B ⧸ Ideal.span ({h} : Set B))]
    (S : Type w) [CommRing S] [Algebra R S] :
    IsSMulRegular (S ⊗[R] B) ((1 : S) ⊗ₜ[R] h) := by
  change Function.Injective (fun z : S ⊗[R] B => ((1 : S) ⊗ₜ[R] h) * z)
  intro z t hzt
  apply mulMap_lTensor_injective R h hh S
  rw [mulMap_lTensor_apply, mulMap_lTensor_apply]
  exact hzt

end EnvelopeProperty.Vanishing.NadelBertiniFlatFibre
