import EnvelopeProperty.Alterations.StableModification.Limits.System
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Actual finite coefficient stages for original tensor sections

Every original tensor and a pair of tensors in different modules lift to a
genuine common finitely generated coefficient subalgebra. No flatness of the
coefficient enlargement, finite module hypothesis, or supplied lift is assumed.
-/

noncomputable section
open TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineCoefficients
open Alterations.StableModification.Limits

variable {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The literal coefficient inclusion, retaining the original R-module. -/
def coefficientMap (B : FGSubalgebra R (⊤ : Subalgebra R k)) :
    B.1 ⊗[R] M →ₗ[R] k ⊗[R] M :=
  TensorProduct.map B.1.val.toLinearMap (LinearMap.id : M →ₗ[R] M)

/-- Every original pure tensor retains its actual original coefficient. -/
theorem coefficientMap_tmul (B : FGSubalgebra R (⊤ : Subalgebra R k)) (b : B.1) (m : M) :
    coefficientMap B (b ⊗ₜ[R] m) = (b : k) ⊗ₜ[R] m := rfl

/-- An actual original tensor descends to a produced finite coefficient stage
containing any fixed stage. No finite-module assumption is needed. -/
theorem exists_fg_tensor_lift (B₀ : FGSubalgebra R (⊤ : Subalgebra R k)) (z : k ⊗[R] M) :
    ∃ (B : FGSubalgebra R (⊤ : Subalgebra R k)), B₀ ≤ B ∧
      ∃ zB : B.1 ⊗[R] M, coefficientMap B zB = z := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  obtain ⟨B, hB₀, hB⟩ := exists_finset_subset (s.image Prod.fst) (by intro x hx; trivial) B₀
  let c : s → B.1 := fun x => ⟨x.val.1, hB (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩
  let zB : B.1 ⊗[R] M := ∑ x : s, c x ⊗ₜ[R] x.val.2
  refine ⟨B, hB₀, zB, ?_⟩
  dsimp only [zB]
  rw [map_sum]
  simp only [coefficientMap_tmul, c]
  exact (Finset.sum_coe_sort s (fun x => x.1 ⊗ₜ[R] x.2)).trans hs.symm

/-- An original tensor and an original inverse tensor, even in different
modules, lift to the SAME produced finite coefficient stage. -/
theorem exists_fg_tensor_pair_lift (B₀ : FGSubalgebra R (⊤ : Subalgebra R k))
    (z : k ⊗[R] M) (w : k ⊗[R] N) :
    ∃ (B : FGSubalgebra R (⊤ : Subalgebra R k)), B₀ ≤ B ∧
      ∃ (zB : B.1 ⊗[R] M) (wB : B.1 ⊗[R] N),
        coefficientMap B zB = z ∧ coefficientMap B wB = w := by
  obtain ⟨A, hA, zA, hzA⟩ := exists_fg_tensor_lift B₀ z
  obtain ⟨B, hAB, wB, hwB⟩ := exists_fg_tensor_lift A w
  let f : A.1 ⊗[R] M →ₗ[R] B.1 ⊗[R] M :=
    TensorProduct.map (Subalgebra.inclusion (show A.1 ≤ B.1 from hAB)).toLinearMap LinearMap.id
  have hcomp : (coefficientMap B (M := M)).comp f = coefficientMap A := by
    ext a m
    rfl
  refine ⟨B, hA.trans hAB, f zA, wB, ?_, hwB⟩
  exact (LinearMap.congr_fun hcomp zA).trans hzA

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineCoefficients
