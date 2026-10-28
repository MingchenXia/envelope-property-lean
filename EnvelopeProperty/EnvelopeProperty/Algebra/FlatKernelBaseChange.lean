import Mathlib.RingTheory.Flat.Equalizer

/-! # Flat scalar extension of an actual commuting square of kernels -/
open TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.FlatKernelBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M N M' N' : Type u}
variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable [AddCommGroup M'] [AddCommGroup N'] [Module S M'] [Module S N']

private def kernelCongr (d : M →ₗ[R] N) (d' : M' →ₗ[S] N')
    (e₀ : S ⊗[R] M ≃ₗ[S] M') (e₁ : S ⊗[R] N ≃ₗ[S] N')
    (h : d'.comp e₀.toLinearMap =
      e₁.toLinearMap.comp (AlgebraTensorModule.lTensor S S d)) :
    LinearMap.ker (AlgebraTensorModule.lTensor S S d) ≃ₗ[S] LinearMap.ker d' where
  toFun x := ⟨e₀ x, by
    change d' (e₀ x) = 0
    exact (LinearMap.congr_fun h (x : S ⊗[R] M)).trans
      ((congrArg e₁ x.property).trans (map_zero e₁))⟩
  invFun y := ⟨e₀.symm y, by
    apply e₁.injective
    rw [map_zero]
    have hh := LinearMap.congr_fun h (e₀.symm y)
    exact (show e₁ (AlgebraTensorModule.lTensor S S d (e₀.symm y)) =
      d' (e₀ (e₀.symm y)) from hh.symm).trans
      ((congrArg d' (e₀.apply_symm_apply (y : M'))).trans y.property)⟩
  left_inv x := by ext; exact e₀.symm_apply_apply (x : S ⊗[R] M)
  right_inv y := by ext; exact e₀.apply_symm_apply (y : M')
  map_add' x y := by ext; exact map_add e₀ (x : S ⊗[R] M) (y : S ⊗[R] M)
  map_smul' s x := by ext; exact map_smul e₀ s (x : S ⊗[R] M)

/-- Flatness and the actual two whole term comparisons derive the actual
kernel comparison, retaining the canonical pure-tensor map. -/
def kernelEquiv [Module.Flat R S]
    (d : M →ₗ[R] N) (d' : M' →ₗ[S] N')
    (e₀ : S ⊗[R] M ≃ₗ[S] M') (e₁ : S ⊗[R] N ≃ₗ[S] N')
    (h : d'.comp e₀.toLinearMap =
      e₁.toLinearMap.comp (AlgebraTensorModule.lTensor S S d)) :
    S ⊗[R] LinearMap.ker d ≃ₗ[S] LinearMap.ker d' :=
  (LinearMap.tensorKerEquiv S S d).trans (kernelCongr d d' e₀ e₁ h)

/-- Every actual pure tensor retains its original whole term image. -/
theorem kernelEquiv_tmul [Module.Flat R S]
    (d : M →ₗ[R] N) (d' : M' →ₗ[S] N')
    (e₀ : S ⊗[R] M ≃ₗ[S] M') (e₁ : S ⊗[R] N ≃ₗ[S] N')
    (h : d'.comp e₀.toLinearMap =
      e₁.toLinearMap.comp (AlgebraTensorModule.lTensor S S d))
    (s : S) (x : LinearMap.ker d) :
    (kernelEquiv d d' e₀ e₁ h (s ⊗ₜ[R] x) : M') = e₀ (s ⊗ₜ[R] (x : M)) := rfl

end EnvelopeProperty.FlatKernelBaseChange
