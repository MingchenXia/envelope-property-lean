import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Actual quotient-index cancellation without flatness or normality -/
open Module
noncomputable section
universe u
namespace EnvelopeProperty.FiniteColengthEndomorphismIndices
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Actual nested original quotient lengths, from the SAME quotient inclusion and factor maps. -/
theorem length_nested_quotient (F G : Submodule R M) (hGF : G ≤ F) :
    Module.length R (M ⧸ G) = Module.length R (F ⧸ G.comap F.subtype) +
      Module.length R (M ⧸ F) := by
  let i : (F ⧸ G.comap F.subtype) →ₗ[R] M ⧸ G :=
    (G.comap F.subtype).mapQ G F.subtype le_rfl
  let j : (M ⧸ G) →ₗ[R] M ⧸ F := Submodule.factor hGF
  have hi : Function.Injective i := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, Submodule.mkQ_map_self]
  have hj : Function.Surjective j := Submodule.factor_surjective hGF
  have hex : Function.Exact i j := LinearMap.exact_iff.mpr (by
    rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.range_mapQ,
      Submodule.range_subtype])
  exact Module.length_eq_add_of_exact i j hi hj hex

/-- The true injective image gives the WHOLE original quotient comparison, no numerical certificate. -/
def imageQuotientEquiv (T : M →ₗ[R] M) (hT : Function.Injective T) (F : Submodule R M) :
    (M ⧸ F) ≃ₗ[R] T.range ⧸ (F.map T).comap T.range.subtype := by
  let e := LinearEquiv.ofInjective T hT
  apply Submodule.Quotient.equiv F ((F.map T).comap T.range.subtype) e
  ext x
  constructor
  · rintro ⟨m, hm, hmx⟩
    exact ⟨m, hm, congrArg Subtype.val hmx⟩
  · rintro ⟨m, hm, hmx⟩
    exact ⟨m, hm, Subtype.ext hmx⟩

/-- The SAME actual injective endomorphism has equal TRUE original quotient
indices on any original finite-colength stable submodule, without flatness/normality. -/
theorem length_cokernel_eq_on_finite_colength_submodule
    (T : M →ₗ[R] M) (hT : Function.Injective T) (F : Submodule R M)
    (hF : F.map T ≤ F) (hfinite : IsFiniteLength R (M ⧸ F)) :
    Module.length R (M ⧸ T.range) = Module.length R (F ⧸ (F.map T).comap F.subtype) := by
  have h₁ := length_nested_quotient F (F.map T) hF
  have h₂ := length_nested_quotient T.range (F.map T) LinearMap.map_le_range
  rw [← (imageQuotientEquiv T hT F).length_eq] at h₂
  have h : Module.length R (F ⧸ (F.map T).comap F.subtype) + Module.length R (M ⧸ F) =
      Module.length R (M ⧸ T.range) + Module.length R (M ⧸ F) := by
    rw [add_comm (Module.length R (M ⧸ T.range))]
    exact h₁.symm.trans h₂
  exact (ENat.add_left_injective_of_ne_top (Module.length_ne_top_iff.mpr hfinite) h).symm

end EnvelopeProperty.FiniteColengthEndomorphismIndices
