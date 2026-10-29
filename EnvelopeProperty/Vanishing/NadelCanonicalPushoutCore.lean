import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Original scalar-preserving module comparison on an actual ring pushout -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalBaseChange

open scoped TensorProduct

variable {A S B C M N : Type u} [CommRing A] [CommRing S] [CommRing B] [CommRing C]
    [Algebra A S] [Algebra A B] [Algebra A C] [Algebra S C] [Algebra B C]
    [IsScalarTower A S C] [IsScalarTower A B C] [Algebra.IsPushout A S B C]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N] [Module S N] [Module C N] [IsScalarTower S C N]

/-- Original tensor cancellation and an actual C-linear comparison give an S-linear comparison. -/
def mixedTensorEquiv (e : C ⊗[B] M ≃ₗ[C] N) : S ⊗[A] M ≃ₗ[S] N := by
  let : IsScalarTower S C (C ⊗[B] M) := by
    apply IsScalarTower.of_algebraMap_smul
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul c w => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  let eS : C ⊗[B] M ≃ₗ[S] N :=
    { __ := e.toAddEquiv
      map_smul' s x := by
        rw [← IsScalarTower.algebraMap_smul C s x]
        exact (e.map_smul _ _).trans (IsScalarTower.algebraMap_smul C s (e x)) }
  exact (Algebra.IsPushout.cancelBaseChange A S B C M).symm.trans eS

/-- Every original pure tensor has its actual coefficient image in the pushout comparison. -/
theorem mixedTensorEquiv_tmul (e : C ⊗[B] M ≃ₗ[C] N) (s : S) (m : M) :
    mixedTensorEquiv e (s ⊗ₜ[A] m) = e (algebraMap S C s ⊗ₜ[B] m) := by
  dsimp only [mixedTensorEquiv, LinearEquiv.trans_apply]
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

end EnvelopeProperty.Vanishing.NadelCanonicalBaseChange
