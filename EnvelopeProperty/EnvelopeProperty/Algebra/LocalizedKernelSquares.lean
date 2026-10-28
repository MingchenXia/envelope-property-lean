import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Actual commuting localization squares preserve their original kernels -/

noncomputable section
universe u
namespace EnvelopeProperty.LocalizedKernelSquares

variable {A M N Mₜ Nₜ : Type*} [CommRing A]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup Mₜ] [AddCommGroup Nₜ]
variable [Module A M] [Module A N] [Module A Mₜ] [Module A Nₜ]

/-- Restriction of the SAME original map to the actual two kernels. -/
def kernelMap (d : M →ₗ[A] N) (d' : Mₜ →ₗ[A] Nₜ)
    (a : M →ₗ[A] Mₜ) (b : N →ₗ[A] Nₜ) (comm : d' ∘ₗ a = b ∘ₗ d) :
    LinearMap.ker d →ₗ[A] LinearMap.ker d' :=
  a.restrict fun x hx => by
    change d' (a x) = 0
    exact (LinearMap.congr_fun comm x).trans
      ((congrArg b (LinearMap.mem_ker.mp hx)).trans (map_zero b))

/-- Every original kernel element retains its SAME actual image. -/
theorem kernelMap_apply (d : M →ₗ[A] N) (d' : Mₜ →ₗ[A] Nₜ)
    (a : M →ₗ[A] Mₜ) (b : N →ₗ[A] Nₜ) (comm : d' ∘ₗ a = b ∘ₗ d)
    (x : LinearMap.ker d) : (kernelMap d d' a b comm x : Mₜ) = a x := rfl

/-- Ordinary square commutativity internally identifies the ENTIRE actual
localized differential with the canonical localization map. -/
theorem differential_eq_localizedMap (T : Submonoid A)
    (d : M →ₗ[A] N) (d' : Mₜ →ₗ[A] Nₜ)
    (a : M →ₗ[A] Mₜ) (b : N →ₗ[A] Nₜ)
    [IsLocalizedModule T a] [IsLocalizedModule T b]
    (comm : d' ∘ₗ a = b ∘ₗ d) : d' = IsLocalizedModule.map T a b d := by
  apply IsLocalizedModule.linearMap_ext T a b
  exact comm.trans (IsLocalizedModule.map_comp T a b d).symm

/-- The actual kernel restriction of ANY actual commuting localization
square is itself a localization; no kernel-isomorphism certificate. -/
theorem kernelMap_isLocalizedModule (Aₜ : Type*) [CommRing Aₜ] [Algebra A Aₜ]
    [Module Aₜ Mₜ] [Module Aₜ Nₜ]
    [IsScalarTower A Aₜ Mₜ] [IsScalarTower A Aₜ Nₜ]
    (T : Submonoid A) [IsLocalization T Aₜ]
    (d : M →ₗ[A] N) (d' : Mₜ →ₗ[A] Nₜ)
    (a : M →ₗ[A] Mₜ) (b : N →ₗ[A] Nₜ)
    [IsLocalizedModule T a] [IsLocalizedModule T b]
    (comm : d' ∘ₗ a = b ∘ₗ d) :
    IsLocalizedModule T (kernelMap d d' a b comm) := by
  have hd := differential_eq_localizedMap T d d' a b comm
  subst d'
  exact LinearMap.toKerLocalized_isLocalizedModule Aₜ T a b d

end EnvelopeProperty.LocalizedKernelSquares
