import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Whole actual ideal conditions in literal field-tensor coefficients

An actual vector-space basis of the coefficient algebra gives unique
finite original-ring coefficients of EVERY entire tensor element.
They prove whole ideal preimage and arbitrary intersection formulas.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.FieldTensorIdealCoefficients

open scoped TensorProduct

universe u v w

section Basis

variable {k L A B : Type u} [CommRing k] [CommRing L] [CommRing A] [CommRing B]
  [Algebra k L] [Algebra k A] [Algebra k B] {ι : Type v}
  (b : Module.Basis ι k L)

/-- The actual finite-support original coefficients of EVERY whole literal tensor. -/
def coefficients (x : L ⊗[k] A) : ι →₀ A := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft b x

/-- The original coefficient formula on EVERY pure tensor. -/
theorem coefficients_tmul (l : L) (a : A) (i : ι) :
    coefficients b (l ⊗ₜ[k] a) i = b.repr l i • a := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b l a i

/-- The actual tensor morphism retains EVERY coefficient of EVERY whole original tensor. -/
theorem coefficients_map (φ : A →ₐ[k] B) (x : L ⊗[k] A) (i : ι) :
    coefficients b (Algebra.TensorProduct.map (AlgHom.id L L) φ x) i =
      φ (coefficients b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [coefficients]
  | tmul l a => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      coefficients_tmul, map_smul]
  | add x y hx hy => simp only [map_add, coefficients,
      Finsupp.add_apply] at hx hy ⊢; rw [hx, hy]

/-- Membership in the WHOLE actual extended ideal is detected by ALL original coefficients. -/
theorem mem_map_iff_coefficients (I : Ideal A) (x : L ⊗[k] A) :
    x ∈ I.map (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom ↔
      ∀ i, coefficients b x i ∈ I := by
  classical
  have hker := Algebra.TensorProduct.lTensor_ker (A := L) (g := Ideal.Quotient.mkₐ k I)
    Ideal.Quotient.mk_surjective
  change RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id k L) (Ideal.Quotient.mkₐ k I)).toRingHom =
    (RingHom.ker (Ideal.Quotient.mk I)).map
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom at hker
  rw [Ideal.mk_ker] at hker
  rw [← hker]
  change Algebra.TensorProduct.map (AlgHom.id k L) (Ideal.Quotient.mkₐ k I) x = 0 ↔ _
  rw [← (TensorProduct.equivFinsuppOfBasisLeft b).map_eq_zero_iff]
  rw [Finsupp.ext_iff]
  simp only [Finsupp.zero_apply]
  change (∀ i, coefficients b
    (Algebra.TensorProduct.map (AlgHom.id L L) (Ideal.Quotient.mkₐ k I) x) i = 0) ↔ _
  simp only [coefficients_map, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

end Basis

section Field

variable {k L A B : Type u} [Field k] [CommRing L] [CommRing A] [CommRing B]
  [Algebra k L] [Algebra k A] [Algebra k B]

/-- The WHOLE original ideal preimage commutes with the literal actual field tensor. -/
theorem map_comap (φ : A →ₐ[k] B) (I : Ideal B) :
    (I.comap φ.toRingHom).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom =
      (I.map (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom).comap
        (Algebra.TensorProduct.map (AlgHom.id L L) φ).toRingHom := by
  let b := Module.Free.chooseBasis k L
  ext x
  rw [mem_map_iff_coefficients b, Ideal.mem_comap, mem_map_iff_coefficients b]
  change (∀ i, φ (coefficients b x i) ∈ I) ↔
    ∀ i, coefficients b (Algebra.TensorProduct.map (AlgHom.id L L) φ x) i ∈ I
  simp only [coefficients_map]

/-- Field tensor extension preserves the WHOLE arbitrary family intersection, with no finite-cover certificate. -/
theorem map_iInf {ι : Type w} (I : ι → Ideal A) :
    (⨅ i, I i).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom =
      ⨅ i, (I i).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom := by
  let b := Module.Free.chooseBasis k L
  ext x
  simp only [mem_map_iff_coefficients b, Ideal.mem_iInf]
  exact forall_comm

/-- The actual WHOLE affine-chart kernel intersection retains all literal field-tensor morphisms. -/
theorem map_iInf_comap {ι : Type w} (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, Algebra k (B i)] (φ : (i : ι) → A →ₐ[k] B i) (I : (i : ι) → Ideal (B i)) :
    (⨅ i, (I i).comap (φ i).toRingHom).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom =
      ⨅ i, ((I i).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B i)).toRingHom).comap
        (Algebra.TensorProduct.map (AlgHom.id L L) (φ i)).toRingHom := by
  rw [map_iInf]
  congr 1
  funext i
  exact map_comap (φ i) (I i)

end Field

end EnvelopeProperty.FieldTensorIdealCoefficients
