import EnvelopeProperty.Berkovich.IdempotentNormBaseChange

/-! # The same actual idempotent summand under a whole algebra isomorphism -/

open scoped TensorProduct Classical
noncomputable section
namespace EnvelopeProperty.IdempotentSummand
variable {R E F : Type*} [CommRing R] [CommRing E] [CommRing F]
  [Algebra R E] [Algebra R F]

/-- A whole algebra isomorphism induces the actual isomorphism of the corresponding quotient summands. -/
def congr (g : E ≃ₐ[R] F) (e : E) : Summand e ≃ₐ[R] Summand (g e) :=
  Ideal.quotientEquivAlg _ _ g (by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, map_sub, map_one]
    rfl)

/-- The induced summand comparison retains the entire original function map. -/
theorem congr_quotient (g : E ≃ₐ[R] F) (e a : E) :
    congr g e (quotient (R := R) e a) = quotient (R := R) (g e) (g a) := rfl

attribute [local instance] finite

/-- The intrinsic actual summand scalar norm is preserved under the entire algebra isomorphism. -/
theorem norm_algEquiv [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (g : E ≃ₐ[R] F) {e : E} (he : IsIdempotentElem e) (b : E) :
    norm (R := R) (he.map g) (g b) = norm (R := R) he b := by
  let := projective (R := R) he
  let := projective (R := R) (he.map g)
  exact projectiveNorm_algEquiv (congr g e) (quotient (R := R) e b)

/-- The WHOLE actual summand norm polynomial is preserved under the entire algebra isomorphism. -/
theorem normForm_algEquiv [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (g : E ≃ₐ[R] F) {e : E} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → E) :
    normForm (R := R) (he.map g) (fun j => g (b j)) = normForm (R := R) he b := by
  let := projective (R := R) he
  let := projective (R := R) (he.map g)
  exact projectiveNormForm_algEquiv (congr g e) (fun j => quotient (R := R) e (b j))

end EnvelopeProperty.IdempotentSummand
