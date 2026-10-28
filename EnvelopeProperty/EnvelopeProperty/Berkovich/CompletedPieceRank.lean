import EnvelopeProperty.Berkovich.CompletedFibrePieceNorm
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Actual total original fibre-piece weights as genuine summand ranks -/

open scoped TensorProduct Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum

/-- Every additive weighted sum on the completed piece retains the ORIGINAL fibre weights. -/
theorem weightedSum_completedIdempotentPiece {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (x : Spectrum A) (e : H x ⊗[A] B)
    {M : Type*} [AddCommMonoid M] (u : Spectrum (H x ⊗[A] B) → M) :
    (∑ z ∈ idempotentFibrePiece e (normPoint (H x)), fibreNormMult (H x) z • u z) =
      ∑ y ∈ completedIdempotentFibrePiece x e, fibreNormMult A y.1 • u (fibrePoint y.2).1 := by
  simpa using congrArg Multiplicative.toAdd
    (weightedProduct_completedIdempotentPiece x e (fun z => Multiplicative.ofAdd (u z)))

/-- The actual total ORIGINAL piece weight is the actual completed quotient-summand dimension. -/
theorem sum_completedIdempotentFibrePiece_eq_finrank {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (x : Spectrum A)
    {e : H x ⊗[A] B} (he : IsIdempotentElem e) :
    (∑ y ∈ completedIdempotentFibrePiece x e, fibreNormMult A y.1) =
      Module.finrank (H x) (IdempotentSummand.Summand e) := by
  let := IdempotentSummand.finite (R := H x) e
  have hs := weightedSum_completedIdempotentPiece x e (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one] at hs
  rw [← hs, sum_fibreNormMult_idempotentPiece he, Module.finrank_baseChange]

/-- Every actual field fibre has the rank at the actual contracted zero prime, even for noninjective coefficients. -/
theorem finiteFlat_finrank_field_eq_rankAtStalk {R M F : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    [Field F] [Algebra R F] :
    Module.finrank F (F ⊗[R] M) =
      Module.rankAtStalk M ((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F).comap (algebraMap R F)) := by
  have h := Module.rankAtStalk_baseChange (R := R) (M := M)
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  rw [Module.rankAtStalk_eq_finrank_of_free (R := F) (M := F ⊗[R] M)] at h
  exact h

end EnvelopeProperty.Berkovich.Spectrum
