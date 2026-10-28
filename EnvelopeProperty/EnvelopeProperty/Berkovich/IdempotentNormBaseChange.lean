import EnvelopeProperty.Berkovich.IdempotentPieceNorm

/-!
# Entire idempotent-summand norm polynomials under arbitrary base change

The original actual quotient summand, the scalar-extended quotient summand,
and their entire polynomial norms are compared by the true tensor quotient
isomorphism. All projectivity assumptions on the summands are derived from
the original idempotent. No flatness of the coefficient homomorphism is used.
-/

open scoped TensorProduct Classical
noncomputable section
namespace EnvelopeProperty

/-- Whole intrinsic norm polynomials respect actual algebra isomorphisms. -/
theorem projectiveNormForm_algEquiv {R A B σ : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] [Fintype σ]
    (e : A ≃ₐ[R] B) (b : σ → A) :
    projectiveNormForm R (fun j => e (b j)) = projectiveNormForm R b := by
  let P := MvPolynomial σ R
  let eT : P ⊗[R] A ≃ₐ[P] P ⊗[R] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e
  unfold projectiveNormForm
  rw [← projectiveNorm_algEquiv eT]
  congr 1
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rfl)

namespace IdempotentSummand
variable {R E S : Type*} [CommRing R] [CommRing E] [Algebra R E]
  [Module.Finite R E] [Module.Projective R E] [CommRing S] [Algebra R S]
attribute [local instance] finite

/-- The unit piece has exactly the entire original intrinsic scalar norm. -/
theorem norm_one (b : E) :
    norm (R := R) (IsIdempotentElem.one : IsIdempotentElem (1 : E)) b =
      projectiveNorm R E b := by
  let := projective (R := R) (IsIdempotentElem.one : IsIdempotentElem (1 : E))
  exact (projectiveNorm_algEquiv (oneEquiv (R := R) (E := E))
    (quotient (R := R) (1 : E) b)).symm

/-- The unit piece has exactly the entire original norm polynomial. -/
theorem normForm_one {σ : Type*} [Fintype σ] (b : σ → E) :
    normForm (R := R) (IsIdempotentElem.one : IsIdempotentElem (1 : E)) b =
      projectiveNormForm R b := by
  let := projective (R := R) (IsIdempotentElem.one : IsIdempotentElem (1 : E))
  exact (projectiveNormForm_algEquiv (oneEquiv (R := R) (E := E))
    (fun j => quotient (R := R) (1 : E) (b j))).symm

/-- The actual scalar norm of the actual scalar-extended piece is the mapped original norm. -/
theorem norm_baseChange {e : E} (he : IsIdempotentElem e) (b : E) :
    norm (R := S) (he.map (Algebra.TensorProduct.includeRight : E →ₐ[R] S ⊗[R] E))
      ((1 : S) ⊗ₜ[R] b) = algebraMap R S (norm (R := R) he b) := by
  let := projective (R := R) he
  let : Module.Projective S (Summand ((1 : S) ⊗ₜ[R] e)) := projective (R := S)
    (he.map (Algebra.TensorProduct.includeRight : E →ₐ[R] S ⊗[R] E))
  change projectiveNorm S (Summand ((1 : S) ⊗ₜ[R] e))
    (quotient (R := S) ((1 : S) ⊗ₜ[R] e) ((1 : S) ⊗ₜ[R] b)) =
      algebraMap R S (projectiveNorm R (Summand e) (quotient (R := R) e b))
  rw [← baseChangeEquiv_tmul S e b 1, projectiveNorm_algEquiv, projectiveNorm_baseChange]

/-- The WHOLE norm polynomial of the actual scalar-extended piece is the mapped original polynomial. -/
theorem map_normForm_baseChange {e : E} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → E) :
    MvPolynomial.map (algebraMap R S) (normForm (R := R) he b) =
      normForm (R := S)
        (he.map (Algebra.TensorProduct.includeRight : E →ₐ[R] S ⊗[R] E))
        (fun j => (1 : S) ⊗ₜ[R] b j) := by
  let := projective (R := R) he
  let : Module.Projective S (Summand ((1 : S) ⊗ₜ[R] e)) := projective (R := S)
    (he.map (Algebra.TensorProduct.includeRight : E →ₐ[R] S ⊗[R] E))
  change MvPolynomial.map (algebraMap R S)
    (projectiveNormForm R (fun j => quotient (R := R) e (b j))) =
      projectiveNormForm S (fun j =>
        quotient (R := S) ((1 : S) ⊗ₜ[R] e) ((1 : S) ⊗ₜ[R] b j))
  rw [map_projectiveNormForm_baseChange]
  have h : (fun j => quotient (R := S) ((1 : S) ⊗ₜ[R] e) ((1 : S) ⊗ₜ[R] b j)) =
      (fun j => baseChangeEquiv S e ((1 : S) ⊗ₜ[R] quotient (R := R) e (b j))) := by
    funext j
    exact (baseChangeEquiv_tmul S e (b j) 1).symm
  rw [h, projectiveNormForm_algEquiv]

end IdempotentSummand
end EnvelopeProperty
