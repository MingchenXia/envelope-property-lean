import EnvelopeProperty.Berkovich.ProjectiveNormForm
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The actual algebra summand cut out by an idempotent

The summand with unit `e` is the genuine unital quotient `E/(1-e)`.
Its projectivity is derived from the orthogonal-idempotent product
decomposition of `E`, rather than supplied as a separate hypothesis.
The tensor comparison retains every original tensor under arbitrary
coefficient base change. Zero and unit idempotents are allowed.
-/

open scoped TensorProduct
noncomputable section
namespace EnvelopeProperty
namespace IdempotentSummand

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]

/-- The genuine unital algebra corresponding to the image of multiplication by `e`. -/
abbrev Summand (e : E) := E ⧸ Ideal.span {1 - e}

/-- The actual quotient homomorphism, preserving the entire coefficient algebra. -/
def quotient (e : E) : E →ₐ[R] Summand e := Ideal.Quotient.mkₐ R _

/-- The given idempotent becomes the actual unit of its summand. -/
theorem quotient_idempotent (e : E) : quotient (R := R) e e = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (quotient (R := R) e), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : 1 - e ∈ Ideal.span ({1 - e} : Set E) := Ideal.subset_span (by simp)
  simpa using (Ideal.span ({1 - e} : Set E)).neg_mem h

/-- The original algebra is the product of its actual two complementary summands. -/
def productEquiv {e : E} (he : IsIdempotentElem e) :
    E ≃ₐ[R] Summand e × (E ⧸ Ideal.span {e}) :=
  AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self

/-- The first product coordinate is the same original quotient map. -/
theorem productEquiv_fst {e : E} (he : IsIdempotentElem e) (a : E) :
    (productEquiv (R := R) he a).1 = quotient (R := R) e a := rfl

/-- Every finite original algebra has a finite actual summand. -/
theorem finite [Module.Finite R E] (e : E) : Module.Finite R (Summand e) :=
  Module.Finite.of_surjective (quotient (R := R) e).toLinearMap
    Ideal.Quotient.mk_surjective

/-- The actual summand of a projective algebra is projective, including rank zero. -/
theorem projective [Module.Projective R E] {e : E} (he : IsIdempotentElem e) :
    Module.Projective R (Summand e) := by
  let p := productEquiv (R := R) he
  let : Module.Projective R (Summand e × (E ⧸ Ideal.span {e})) :=
    Module.Projective.of_equiv p.toLinearEquiv
  exact Module.Projective.of_split
    (LinearMap.inl R (Summand e) (E ⧸ Ideal.span {e}))
    (LinearMap.fst R (Summand e) (E ⧸ Ideal.span {e})) rfl

/-- The quotient is exactly the principal localization at the actual idempotent. -/
theorem isLocalization {e : E} (he : IsIdempotentElem e) :
    IsLocalization.Away e (Summand e) :=
  IsLocalization.Away.quotient_of_isIdempotentElem he

/-- Arbitrary scalar extension gives the literal quotient by the scalar-extended idempotent. -/
def baseChangeEquiv (S : Type*) [CommRing S] [Algebra R S] (e : E) :
    S ⊗[R] Summand e ≃ₐ[S]
      IdempotentSummand.Summand ((1 : S) ⊗ₜ[R] e) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S E S
    (Ideal.span {1 - e})).trans
      (Ideal.quotientEquivAlgOfEq S (by
        rw [Ideal.map_span]
        simp only [Set.image_singleton, map_sub, map_one]
        rfl))

/-- The scalar comparison retains every original tensor, not just the coefficient field. -/
theorem baseChangeEquiv_tmul (S : Type*) [CommRing S] [Algebra R S]
    (e a : E) (s : S) :
    baseChangeEquiv S e (s ⊗ₜ[R] quotient (R := R) e a) =
      quotient (R := S) ((1 : S) ⊗ₜ[R] e) (s ⊗ₜ[R] a) := rfl

/-- The zero idempotent gives the actual zero algebra. -/
theorem subsingleton_zero : Subsingleton (Summand (0 : E)) := by
  change Subsingleton (E ⧸ Ideal.span ({1 - 0} : Set E))
  rw [sub_zero, Ideal.span_singleton_one]
  infer_instance

/-- The unit idempotent gives the entire original algebra. -/
def oneEquiv : Summand (1 : E) ≃ₐ[R] E :=
  (Ideal.quotientEquivAlgOfEq R (by simp)).trans (AlgEquiv.quotientBot R E)

end IdempotentSummand
end EnvelopeProperty
