import EnvelopeProperty.Berkovich.SpectrumCompleteFieldWeights
import EnvelopeProperty.Berkovich.IdempotentNormBaseChange

/-! # Actual completed summand norms with original finite-fibre weights -/

open scoped TensorProduct NNReal Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum

/-- Prescribing the actual field norm is exactly the fibre over its genuine norm point. -/
def normFibreEquiv {K C : Type*} [NormedField K] [IsUltrametricDist K]
    [CommRing C] [Algebra K C] :
    RelativeSpectrum (NormedField.valuation (K := K)) C ≃ Fibre (B := C) (normPoint K) where
  toFun y := ⟨y.1, comap_normPoint y⟩
  invFun y := ⟨y.1, fun c => congrArg (fun z : Spectrum K => z.val c) y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The entire completed-tensor norm fibre is the same entire original fibre. -/
def completedNormFibreEquiv (x : Spectrum A) :
    Fibre (B := H x ⊗[A] B) (normPoint (H x)) ≃ Fibre (B := B) x :=
  normFibreEquiv.symm.trans (fibreEquiv x)

/-- Its inverse is precisely the original actual completed-tensor point. -/
theorem completedNormFibreEquiv_symm_coe (x : Spectrum A) (y : Fibre (B := B) x) :
    ((completedNormFibreEquiv x).symm y).1 = (fibrePoint y.2).1 := rfl

/-- The forward comparison recovers the entire original completed-tensor seminorm. -/
theorem fibrePoint_completedNormFibreEquiv (x : Spectrum A)
    (z : Fibre (B := H x ⊗[A] B) (normPoint (H x))) :
    (fibrePoint ((completedNormFibreEquiv x) z).2).1 = z.1 :=
  congrArg Subtype.val ((completedNormFibreEquiv x).symm_apply_apply z)

private local instance originalFibreFinite [Module.Finite A B] (x : Spectrum A) :
    Finite (Fibre (B := B) x) := finite_fibre x

/-- The literal original point-fibre piece cut out by an actual completed-tensor idempotent. -/
def completedIdempotentFibrePiece [Module.Finite A B] (x : Spectrum A)
    (e : H x ⊗[A] B) : Finset (Fibre (B := B) x) :=
  let := Fintype.ofFinite (Fibre (B := B) x)
  Finset.univ.filter (fun y => (fibrePoint y.2).1.val e = 1)

/-- Whole completed-piece products retain exactly the ORIGINAL point fibre and its ORIGINAL weights. -/
theorem weightedProduct_completedIdempotentPiece [Module.Finite A B]
    (x : Spectrum A) (e : H x ⊗[A] B) {M : Type*} [CommMonoid M]
    (u : Spectrum (H x ⊗[A] B) → M) :
    (∏ z ∈ idempotentFibrePiece e (normPoint (H x)), u z ^ fibreNormMult (H x) z) =
      ∏ y ∈ completedIdempotentFibrePiece x e,
        u (fibrePoint y.2).1 ^ fibreNormMult A y.1 := by
  let := Fintype.ofFinite (Fibre (B := B) x)
  let q := completedNormFibreEquiv (B := B) x
  let toOriginal (z : Spectrum (H x ⊗[A] B))
      (hz : z ∈ idempotentFibrePiece e (normPoint (H x))) : Fibre (B := B) x :=
    q ⟨z, (Set.Finite.mem_toFinset
      (finite_preimage_singleton (A := H x ⊗[A] B) (normPoint (H x)))).1
        (Finset.mem_filter.mp hz).1⟩
  have hpoint (z) (hz) : (fibrePoint (toOriginal z hz).2).1 = z :=
    fibrePoint_completedNormFibreEquiv x _
  refine Finset.prod_bij toOriginal ?_ ?_ ?_ ?_
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hpoint z hz]
    exact (Finset.mem_filter.mp hz).2
  · intro z₁ h₁ z₂ h₂ h
    exact congrArg Subtype.val (q.injective h)
  · intro y hy
    let z := q.symm y
    have hz : z.1 ∈ idempotentFibrePiece e (normPoint (H x)) := by
      apply Finset.mem_filter.mpr
      refine ⟨(Set.Finite.mem_toFinset _).2 z.2, ?_⟩
      exact (Finset.mem_filter.mp hy).2
    refine ⟨z.1, hz, ?_⟩
    exact q.apply_symm_apply y
  · intro z hz
    have hw := fibreNormMult_fibrePoint (toOriginal z hz).2
    rw [hpoint z hz] at hw
    exact congrArg₂ (fun v n => v ^ n) (congrArg u (hpoint z hz).symm) hw

/-- The actual completed quotient norm is the product over its actual ORIGINAL fibre piece. -/
theorem val_completedIdempotentNorm [Module.Finite A B] (x : Spectrum A)
    {e : H x ⊗[A] B} (he : IsIdempotentElem e) (b : H x ⊗[A] B) :
    NormedField.valuation (IdempotentSummand.norm (R := H x) he b) =
      ∏ y ∈ completedIdempotentFibrePiece x e,
        (fibrePoint y.2).1.val b ^ fibreNormMult A y.1 := by
  exact (IdempotentSummand.val_norm he b (normPoint (H x))).trans
    (weightedProduct_completedIdempotentPiece x e (fun z => z.val b))

/-- The whole completed quotient polynomial has the actual ORIGINAL weighted fibre maxima. -/
theorem wgaussValuation_completedIdempotentNormForm [Module.Finite A B] (x : Spectrum A)
    {e : H x ⊗[A] B} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → H x ⊗[A] B) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (IdempotentSummand.normForm (R := H x) he b) =
      ∏ y ∈ completedIdempotentFibrePiece x e,
        (Finset.univ.sup fun j => (fibrePoint y.2).1.val (b j) * r j) ^ fibreNormMult A y.1 := by
  exact (IdempotentSummand.wgaussValuation_normForm he b r (normPoint (H x))).trans
    (weightedProduct_completedIdempotentPiece x e
      (fun z => Finset.univ.sup fun j => z.val (b j) * r j))

end EnvelopeProperty.Berkovich.Spectrum
