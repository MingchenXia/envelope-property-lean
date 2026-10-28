import EnvelopeProperty.Berkovich.SpectrumIdempotentSummand
import EnvelopeProperty.Berkovich.SpectrumProjectiveNorm

/-!
# Actual scalar and polynomial norms on idempotent fibre pieces

The piece is the literal subset of the original finite analytic fibre where
the original idempotent has value one. Its weights are the original completed
local-ring length times residue degree. The actual quotient algebra and its
derived projectivity produce the scalar norm and entire norm polynomial.
No piece identification, norm identity, multiplicity, freeness, reducedness
or separability certificate is supplied.
-/

open scoped TensorProduct Classical NNReal
noncomputable section
namespace EnvelopeProperty
namespace Berkovich.Spectrum
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]
attribute [local instance] IdempotentSummand.finite

/-- The actual finite part of the original fibre cut out by `e=1`. -/
def idempotentFibrePiece [Module.Finite R E] (e : E) (x : Spectrum R) : Finset (Spectrum E) :=
  (finite_preimage_singleton (A := E) x).toFinset.filter (fun y => y.val e = 1)

/-- The zero idempotent cuts out exactly the empty actual fibre piece. -/
theorem idempotentFibrePiece_zero [Module.Finite R E] (x : Spectrum R) :
    idempotentFibrePiece (0 : E) x = ∅ := by
  simp [idempotentFibrePiece]

/-- The unit idempotent cuts out exactly the entire original fibre. -/
theorem idempotentFibrePiece_one [Module.Finite R E] (x : Spectrum R) :
    idempotentFibrePiece (1 : E) x = (finite_preimage_singleton (A := E) x).toFinset := by
  simp [idempotentFibrePiece]

/-- Every weighted sum over the summand is the same sum over the actual original piece. -/
theorem fibreWeightedSum_idempotentSummand [Module.Finite R E]
    {e : E} (he : IsIdempotentElem e) (x : Spectrum R)
    {M : Type*} [AddCommMonoid M] (u : Spectrum E → M) :
    (∑ y ∈ (finite_preimage_singleton (A := IdempotentSummand.Summand e) x).toFinset,
      fibreNormMult R y • u (idempotentSummandHomeomorph he y).1) =
      ∑ y ∈ idempotentFibrePiece e x, fibreNormMult R y • u y := by
  let q := idempotentSummandHomeomorph he
  refine Finset.sum_bij (fun y _ => (q y).1) ?_ ?_ ?_ ?_
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨(Set.Finite.mem_toFinset _).2 ?_, (q y).2⟩
    exact (idempotentSummandHomeomorph_base he y).trans
      ((Set.Finite.mem_toFinset
        (finite_preimage_singleton (A := IdempotentSummand.Summand e) x)).1 hy)
  · intro y₁ _ y₂ _ h
    exact q.injective (Subtype.ext h)
  · intro z hz
    obtain ⟨hz, hez⟩ := Finset.mem_filter.mp hz
    let y := q.symm ⟨z, hez⟩
    have hq : (q y).1 = z := congrArg Subtype.val (q.apply_symm_apply ⟨z, hez⟩)
    refine ⟨y, (Set.Finite.mem_toFinset _).2 ?_, hq⟩
    have h := idempotentSummandHomeomorph_base (R := R) he y
    change comap (algebraMap R E) (q y).1 = _ at h
    rw [hq] at h
    exact h.symm.trans
      ((Set.Finite.mem_toFinset (finite_preimage_singleton (A := E) x)).1 hz)
  · intro y _
    rw [← fibreNormMult_idempotentSummand he y]

/-- Every weighted product has the original actual piece and all its original weights. -/
theorem fibreWeightedProduct_idempotentSummand [Module.Finite R E]
    {e : E} (he : IsIdempotentElem e) (x : Spectrum R)
    {M : Type*} [CommMonoid M] (u : Spectrum E → M) :
    (∏ y ∈ (finite_preimage_singleton (A := IdempotentSummand.Summand e) x).toFinset,
      u (idempotentSummandHomeomorph he y).1 ^ fibreNormMult R y) =
      ∏ y ∈ idempotentFibrePiece e x, u y ^ fibreNormMult R y := by
  simpa using congrArg Additive.toMul
    (fibreWeightedSum_idempotentSummand he x (fun y => Additive.ofMul (u y)))

/-- The complete original piece weight is its actual completed summand dimension. -/
theorem sum_fibreNormMult_idempotentPiece [Module.Finite R E]
    {e : E} (he : IsIdempotentElem e) (x : Spectrum R) :
    (∑ y ∈ idempotentFibrePiece e x, fibreNormMult R y) =
      Module.finrank (H x) (H x ⊗[R] IdempotentSummand.Summand e) := by
  rw [← sum_fibreNormMult_eq_completedFinrank]
  simpa only [smul_eq_mul, mul_one] using
    (fibreWeightedSum_idempotentSummand he x (fun _ => (1 : ℕ))).symm

end Berkovich.Spectrum

namespace IdempotentSummand
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]
  [Module.Finite R E] [Module.Projective R E]
attribute [local instance] finite

/-- The scalar norm of the original function on the actual summand algebra. -/
def norm {e : E} (he : IsIdempotentElem e) : E →* R :=
  let := projective (R := R) he
  (projectiveNorm R (Summand e)).comp (quotient (R := R) e).toMonoidHom

/-- The entire intrinsic norm polynomial of the actual summand. -/
def normForm {e : E} (he : IsIdempotentElem e) {σ : Type*} [Fintype σ]
    (b : σ → E) : MvPolynomial σ R :=
  let := projective (R := R) he
  projectiveNormForm R (fun j => quotient (R := R) e (b j))

/-- The actual norm on the zero algebra is one, even for an arbitrary original function. -/
theorem norm_zero (b : E) : norm (R := R) (IsIdempotentElem.zero : IsIdempotentElem (0 : E)) b = 1 := by
  let := projective (R := R) (IsIdempotentElem.zero : IsIdempotentElem (0 : E))
  let := subsingleton_zero (E := E)
  change projectiveNorm R (Summand (0 : E)) (quotient (R := R) 0 b) = 1
  rw [Subsingleton.elim (quotient (R := R) 0 b) 1, map_one]

/-- The entire norm polynomial on the zero algebra is the constant polynomial one. -/
theorem normForm_zero {σ : Type*} [Fintype σ] (b : σ → E) :
    normForm (R := R) (IsIdempotentElem.zero : IsIdempotentElem (0 : E)) b = 1 := by
  let := projective (R := R) (IsIdempotentElem.zero : IsIdempotentElem (0 : E))
  let := subsingleton_zero (E := E)
  unfold normForm projectiveNormForm
  rw [Subsingleton.elim (∑ j, (MvPolynomial.X j : MvPolynomial σ R) ⊗ₜ[R]
    quotient (R := R) (0 : E) (b j)) 1, map_one]

/-- The actual scalar norm is the product over exactly the original idempotent piece. -/
theorem val_norm {e : E} (he : IsIdempotentElem e) (b : E) (x : Berkovich.Spectrum R) :
    x.val (norm (R := R) he b) =
      ∏ y ∈ Berkovich.Spectrum.idempotentFibrePiece e x,
        y.val b ^ Berkovich.Spectrum.fibreNormMult R y := by
  let := projective (R := R) he
  change x.val (projectiveNorm R (Summand e) (quotient (R := R) e b)) = _
  rw [Berkovich.Spectrum.val_projectiveNorm]
  exact Berkovich.Spectrum.fibreWeightedProduct_idempotentSummand he x (fun y => y.val b)

/-- The weighted Gauss coefficient norm is the full original weighted maximum product. -/
theorem wgaussValuation_normForm {e : E} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → E) (r : σ → ℝ≥0) (x : Berkovich.Spectrum R) :
    wgaussValuation x.val r (normForm (R := R) he b) =
      ∏ y ∈ Berkovich.Spectrum.idempotentFibrePiece e x,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^
          Berkovich.Spectrum.fibreNormMult R y := by
  let := projective (R := R) he
  change wgaussValuation x.val r
    (projectiveNormForm R (fun j => quotient (R := R) e (b j))) = _
  rw [Berkovich.Spectrum.wgaussValuation_projectiveNormForm]
  exact Berkovich.Spectrum.fibreWeightedProduct_idempotentSummand he x
    (fun y => Finset.univ.sup fun j => y.val (b j) * r j)

end IdempotentSummand
end EnvelopeProperty
