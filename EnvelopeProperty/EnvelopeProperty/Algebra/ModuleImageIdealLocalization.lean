import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Entire images of module-to-structure maps under localization -/

namespace EnvelopeProperty

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S]
    {M : Type w} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Localization preserves the entire original image ideal, with no finite
generation or flatness premise on the original module. -/
theorem map_image_ideal_of_isLocalizedModule (α : M →ₗ[R] R) (β : N →ₗ[S] S)
    (ρ : M →ₗ[R] N) [IsLocalizedModule T ρ]
    (hsquare : ∀ m : M, β (ρ m) = algebraMap R S (α m)) :
    Ideal.map (algebraMap R S) α.range = β.range := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro a ⟨m, rfl⟩
    exact ⟨ρ m, hsquare m⟩
  · rintro x ⟨n, rfl⟩
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj T ρ n
    have heq : algebraMap R S (α m) = algebraMap R S (s : R) * β n := by
      rw [← hsquare, ← hs]
      rw [Submonoid.smul_def, ← IsScalarTower.algebraMap_smul S (s : R) n]
      exact β.map_smul _ _
    have hfrac : IsLocalization.mk' S (α m) s = β n := by
      apply (IsLocalization.map_units S s).mul_left_cancel
      rw [IsLocalization.mk'_spec']
      exact heq
    rw [← hfrac]
    exact (IsLocalization.mk'_mem_map_algebraMap_iff T S α.range (α m) s).mpr
      ⟨1, T.one_mem, by exact ⟨m, by simp⟩⟩

end EnvelopeProperty
