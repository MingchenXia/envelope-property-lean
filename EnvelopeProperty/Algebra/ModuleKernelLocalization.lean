import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Actual ideal kernels of module maps commute with localization -/

namespace EnvelopeProperty

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S]
    {M : Type w} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S N]

/-- The ENTIRE ideal kernel of an actual localized unit-module map is
exactly the extension of its original whole ideal kernel. -/
theorem map_kernel_ideal_of_isLocalizedModule (α : R →ₗ[R] M) (β : S →ₗ[S] N)
    (ρ : M →ₗ[R] N) [IsLocalizedModule T ρ]
    (hsquare : ∀ a : R, ρ (α a) = β (algebraMap R S a)) :
    Ideal.map (algebraMap R S) α.ker = β.ker := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change β (algebraMap R S a) = 0
    change α a = 0 at ha
    exact (hsquare a).symm.trans ((congrArg ρ ha).trans (map_zero ρ))
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq T x
    change β (IsLocalization.mk' S a s) = 0 at hx
    have hρ : ρ (α a) = 0 := by
      rw [hsquare, ← IsLocalization.mk'_spec' S a s]
      change β ((algebraMap R S s) • IsLocalization.mk' S a s) = 0
      rw [map_smul, hx, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists T ρ).mp
      (show ρ (α a) = ρ 0 from hρ.trans (map_zero ρ).symm)
    apply (IsLocalization.mk'_mem_map_algebraMap_iff T S α.ker a s).mpr
    refine ⟨t, t.property, ?_⟩
    change α ((t : R) • a) = 0
    rw [map_smul]
    simpa only [Submonoid.smul_def, smul_zero] using ht

end EnvelopeProperty
