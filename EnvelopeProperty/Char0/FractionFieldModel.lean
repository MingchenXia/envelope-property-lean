import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # A genuine original affine domain inside its own actual fraction field -/

set_option autoImplicit false
noncomputable section
namespace EnvelopeProperty.Char0.AffineFractionFieldModel
universe u v
variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]

/-- The SAME original affine domain, as an actual subalgebra of its own fraction field. -/
def subalgebra : Subalgebra k (FractionRing R) :=
  (IsScalarTower.toAlgHom k R (FractionRing R)).range

/-- The entire original algebra maps isomorphically to the SAME actual fraction-field subalgebra. -/
def equiv : R ≃ₐ[k] subalgebra k R :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom k R (FractionRing R)).rangeRestrict
    ⟨fun _ _ h => (IsFractionRing.injective R (FractionRing R)) (Subtype.ext_iff.mp h),
      AlgHom.rangeRestrict_surjective _⟩

omit [IsDomain R] in
/-- EVERY original element reads back as its literal original fraction-field coefficient. -/
theorem equiv_apply_coe (a : R) :
    ((equiv k R a : subalgebra k R) : FractionRing R) = algebraMap R (FractionRing R) a := rfl

/-- The actual ambient fraction field is the fraction field of the SAME image subalgebra. -/
instance isFractionRing : IsFractionRing (subalgebra k R) (FractionRing R) := by
  apply IsFractionRing.of_ringEquiv_left (equiv k R).symm.toRingEquiv
  intro a
  have h := equiv_apply_coe k R ((equiv k R).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

end EnvelopeProperty.Char0.AffineFractionFieldModel
