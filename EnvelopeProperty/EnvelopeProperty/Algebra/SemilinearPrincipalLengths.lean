import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Actual semilinear principal quotient lengths under original ring isomorphisms -/
noncomputable section
universe u
namespace EnvelopeProperty.SemilinearPrincipalLengths
variable {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

/-- A genuine bijective semilinear original map over a surjective original
coefficient map preserves TRUE module length over the respective original rings. -/
theorem length_eq_of_semilinear_bijective (σ : R →+* S) (hσ : Function.Surjective σ)
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  let : RingHomSurjective σ := ⟨hσ⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

omit [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] in
/-- The actual original principal quotient map is semilinear over the SAME original ring isomorphism. -/
def principalQuotientMap (e : R ≃+* S) (a : R) :
    (R ⧸ Ideal.span {a}) →ₛₗ[e.toRingHom] S ⧸ Ideal.span {e a} := by
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e
    (by rw [Ideal.map_span]; simp)
  refine { toFun := q, map_add' := q.map_add, map_smul' := ?_ }
  intro r b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change q (Ideal.Quotient.mk _ (r * b)) =
    Ideal.Quotient.mk _ (e r * e b)
  rw [Ideal.quotientEquiv_mk, map_mul]

omit [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] in
/-- The SAME original principal quotient semilinear map is genuinely bijective. -/
theorem principalQuotientMap_bijective (e : R ≃+* S) (a : R) :
    Function.Bijective (principalQuotientMap e a) :=
  (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e
    (by rw [Ideal.map_span]; simp)).bijective

omit [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] in
/-- TRUE original principal ring order is invariant under the SAME original
whole ring isomorphism, using actual respective-ring module lengths. -/
theorem ord_ringEquiv (e : R ≃+* S) (a : R) : Ring.ord R a = Ring.ord S (e a) :=
  length_eq_of_semilinear_bijective e.toRingHom e.surjective
    (principalQuotientMap e a) (principalQuotientMap_bijective e a)

end EnvelopeProperty.SemilinearPrincipalLengths
