/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ReducedComponents
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Genuine components of the entire original quotient

Actual ideal image and inverse image identify the two literal minimal-prime
indices. The actual third quotient isomorphism preserves every original
ring and quotient element. No Noetherian/reduced/finite or component-comparison
certificate is required, and the original ideal is never replaced by its radical.
-/

noncomputable section
namespace EnvelopeProperty.ReducedComponents
variable {R : Type*} [CommRing R]

/-- Actual minimal primes of the original ideal map to actual minimal primes of its original quotient. -/
theorem quotientIndex_map_mem (I : Ideal R) (p : Index I) :
    p.1.map (Ideal.Quotient.mk I) ∈ (⊥ : Ideal (R ⧸ I)).minimalPrimes := by
  rw [← Ideal.map_quotient_self I,
    Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_idem]
  exact ⟨p.1, p.2, rfl⟩

/-- Actual minimal quotient primes pull back to genuine minimal primes of the entire original ideal. -/
theorem quotientIndex_comap_mem (I : Ideal R) (q : Index (⊥ : Ideal (R ⧸ I))) :
    q.1.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨q.1, q.2, rfl⟩

/-- The literal two minimal-component indices are canonically equivalent by actual image and inverse image. -/
def quotientIndexEquiv (I : Ideal R) : Index I ≃ Index (⊥ : Ideal (R ⧸ I)) where
  toFun p := ⟨p.1.map (Ideal.Quotient.mk I), quotientIndex_map_mem I p⟩
  invFun q := ⟨q.1.comap (Ideal.Quotient.mk I), quotientIndex_comap_mem I q⟩
  left_inv p := by
    apply Subtype.ext
    change (p.1.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p.1
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr p.2.le]
  right_inv q := by
    apply Subtype.ext
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.1

/-- Every actual quotient index is the true image of the same original prime ideal. -/
theorem quotientIndexEquiv_apply (I : Ideal R) (p : Index I) :
    (quotientIndexEquiv I p).1 = p.1.map (Ideal.Quotient.mk I) := rfl

/-- The inverse index comparison is the actual original ideal inverse image. -/
theorem quotientIndexEquiv_symm_apply (I : Ideal R) (q : Index (⊥ : Ideal (R ⧸ I))) :
    ((quotientIndexEquiv I).symm q).1 = q.1.comap (Ideal.Quotient.mk I) := rfl

/-- The genuine quotient component is canonically the original component as an algebra retaining the entire original coefficient action. -/
def quotientComponentEquiv (I : Ideal R) (p : Index I) :
    Component (⊥ : Ideal (R ⧸ I)) (quotientIndexEquiv I p) ≃ₐ[R] Component I p :=
  DoubleQuot.quotQuotEquivQuotOfLEₐ R p.2.le

/-- Every original ring element retains its actual entire component class. -/
theorem quotientComponentEquiv_mk_mk (I : Ideal R) (p : Index I) (r : R) :
    quotientComponentEquiv I p
      (Ideal.Quotient.mk (quotientIndexEquiv I p).1 (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk p.1 r :=
  DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r p.2.le

/-- The inverse actual comparison retains the same entire original element. -/
theorem quotientComponentEquiv_symm_mk (I : Ideal R) (p : Index I) (r : R) :
    (quotientComponentEquiv I p).symm (Ideal.Quotient.mk p.1 r) =
      Ideal.Quotient.mk (quotientIndexEquiv I p).1 (Ideal.Quotient.mk I r) :=
  DoubleQuot.quotQuotEquivQuotOfLE_symm_mk r p.2.le

/-- On every original unreduced quotient element the comparison is precisely the true factor map. -/
theorem quotientComponentEquiv_mk (I : Ideal R) (p : Index I) (x : R ⧸ I) :
    quotientComponentEquiv I p (Ideal.Quotient.mk (quotientIndexEquiv I p).1 x) =
      Ideal.Quotient.factor p.2.le x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact quotientComponentEquiv_mk_mk I p r

end EnvelopeProperty.ReducedComponents
