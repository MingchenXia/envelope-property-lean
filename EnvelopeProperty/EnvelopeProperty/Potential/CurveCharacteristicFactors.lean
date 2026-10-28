import EnvelopeProperty.Potential.CurveIdempotentNorm
import EnvelopeProperty.Berkovich.IdempotentCharacteristicFactors
import EnvelopeProperty.Potential.LineCoverUniqueness
import EnvelopeProperty.Berkovich.CompletedPieceRank

/-! # Actual analytic characteristic factors and their original coefficient bounds -/

open scoped TensorProduct NNReal Polynomial Classical Matrix
open Polynomial
noncomputable section

namespace EnvelopeProperty

/-- Literal polynomial evaluation is contractive for the actual weighted Gauss
valuation whenever the prescribed coefficient and variable maps are contractive. -/
theorem valuation_eval₂Hom_le_wgauss {R S σ : Type*} [CommRing R] [CommRing S]
    (v : Valuation R ℝ≥0) (q : Valuation S ℝ≥0) (f : R →+* S)
    (r : σ → ℝ≥0) (t : σ → S) (hf : ∀ a, q (f a) ≤ v a)
    (ht : ∀ i, q (t i) ≤ r i) (P : MvPolynomial σ R) :
    q (MvPolynomial.eval₂Hom f t P) ≤ wgaussValuation v r P := by
  classical
  change q (MvPolynomial.eval₂ f t P) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply q.map_sum_le
  intro d hd
  rw [q.map_mul, map_prod]
  calc
    q (f (P.coeff d)) * ∏ i ∈ d.support, q (t i ^ d i) ≤
        v (P.coeff d) * ∏ i ∈ d.support, r i ^ d i := by
      apply mul_le_mul' (hf _)
      apply Finset.prod_le_prod (fun _ _ => zero_le)
      intro i hi
      rw [q.map_pow]
      exact pow_le_pow_left' (ht i) _
    _ = v (P.coeff d) * monoWeight r d := rfl
    _ ≤ wgaussValuation v r P := le_wgaussValuation v r P d

/-- Every original coefficient after the binary substitution `(Z,1)` is
controlled by the actual original binary Gauss valuation with weights one. -/
theorem valuation_coeff_eval_one_le_wgauss {R : Type*} [CommRing R]
    (v : Valuation R ℝ≥0) (P : MvPolynomial (Fin 2) R) (n : ℕ) :
    v ((MvPolynomial.eval₂Hom (Polynomial.C : R →+* R[X]) ![Polynomial.X, 1] P).coeff n) ≤
      wgaussValuation v (fun _ : Fin 2 => 1) P := by
  have h := valuation_eval₂Hom_le_wgauss v (gaussValuation v 1)
    Polynomial.C (fun _ : Fin 2 => 1) ![Polynomial.X, 1]
    (fun a => (gaussFun_C v 1 a).le) (fun i => by
      fin_cases i
      · exact (gaussFun_X v 1).le
      · exact (map_one (gaussValuation v 1)).le) P
  have hc : v ((MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] P).coeff n) ≤
      gaussValuation v 1 (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] P) := by
    change _ ≤ gaussFun v 1 _
    simpa only [one_pow, mul_one] using
      le_gaussFun v 1 (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] P) n
  exact hc.trans h

/-- The entire binary substitution commutes with every original coefficient map. -/
theorem map_eval_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin 2) R) :
    Polynomial.map f (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] P) =
      MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] (MvPolynomial.map f P) := by
  have hc : (Polynomial.mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := by
    ext a
    simp
  have hx : (fun j : Fin 2 => (Polynomial.mapRingHom f)
      (![(Polynomial.X : R[X]), 1] j)) = ![(Polynomial.X : S[X]), 1] := by
    funext j
    fin_cases j <;> simp
  change (Polynomial.mapRingHom f) (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] P) = _
  rw [MvPolynomial.map_eval₂Hom, hc, hx, MvPolynomial.eval₂Hom_map_hom]

end EnvelopeProperty

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The literal analytic factor of original multiplication by `b`, defined by
the already constructed whole quotient norm polynomial. -/
def curveCharacteristicFactor (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    U.AnalyticFunctions[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]
    (U.curveIdempotentNormForm basis he ![(1 : B), -b])

/-- Specialization retains every coefficient of the actual factor in the same
original completed residue field. -/
theorem map_curveCharacteristicFactor (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    Polynomial.map (U.evaluationToH x) (U.curveCharacteristicFactor basis he b) =
      IdempotentSummand.characteristicFactor
        (U.curveIdempotentSpecialization_isIdempotent basis he x)
        ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b) := by
  let := Module.Finite.of_basis basis
  rw [curveCharacteristicFactor, map_eval_one, U.map_curveIdempotentNormForm basis he]
  unfold IdempotentSummand.characteristicFactor
  congr 2
  funext j
  fin_cases j
  · exact Algebra.TensorProduct.one_def.symm
  · exact TensorProduct.tmul_neg (1 : Spectrum.H x.1.1) b

/-- The coefficient bound is the literal product over selected original points,
retaining their original full fibre multiplicities. -/
theorem valuation_coeff_curveCharacteristicFactor_le (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B)
    (x : U.carrier) (n : ℕ) :
    let := Module.Finite.of_basis basis
    NormedField.valuation (U.evaluationToH x ((U.curveCharacteristicFactor basis he b).coeff n)) ≤
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        max 1 (y.1.val b) ^ Spectrum.fibreNormMult K[X] y.1 := by
  let := Module.Finite.of_basis basis
  have h := valuation_coeff_eval_one_le_wgauss NormedField.valuation
    (MvPolynomial.map (U.evaluationToH x) (U.curveIdempotentNormForm basis he ![(1 : B), -b])) n
  rw [← map_eval_one, Polynomial.coeff_map] at h
  rw [U.wgaussValuation_curveIdempotentNormForm basis he] at h
  have hs (y : Spectrum.Fibre (B := B) x.1.1) :
      (Finset.univ.sup fun j : Fin 2 => y.1.val (![(1 : B), -b] j) * (1 : ℝ≥0)) =
        max 1 (y.1.val b) := by
    simp [Finset.univ_fin2]
  simpa only [curveCharacteristicFactor, hs] using h

/-- A true bound on the original integral coordinate bounds every actual
analytic factor coefficient by the original whole curve rank. -/
theorem nnnorm_coeff_curveCharacteristicFactor_le (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B)
    (M : ℝ≥0) (hM : 1 ≤ M)
    (hb : ∀ (x : U.carrier) (y : Spectrum.Fibre (B := B) x.1.1), y.1.val b ≤ M)
    (n : ℕ) :
    ‖(U.curveCharacteristicFactor basis he b).coeff n‖₊ ≤ M ^ Fintype.card ι := by
  classical
  let := Module.Finite.of_basis basis
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  rw [U.nnnorm_eq_boundary_max]
  apply Finset.sup_le
  intro z hz
  let x : U.carrier := ⟨z.1, U.boundary_subset z.2⟩
  change NormedField.valuation (U.evaluationToH x _) ≤ _
  apply (U.valuation_coeff_curveCharacteristicFactor_le basis he b x n).trans
  calc
    (∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        max 1 (y.1.val b) ^ Spectrum.fibreNormMult K[X] y.1) ≤
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x), M ^ Spectrum.fibreNormMult K[X] y.1 := by
      exact Finset.prod_le_prod (fun _ _ => zero_le) (fun y _ =>
        pow_le_pow_left' (max_le hM (hb x y)) _)
    _ = M ^ (∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x), Spectrum.fibreNormMult K[X] y.1) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ M ^ Fintype.card ι := by
      apply pow_le_pow_right₀ hM
      rw [Spectrum.sum_completedIdempotentFibrePiece_eq_finrank x.1.1
        (U.curveIdempotentSpecialization_isIdempotent basis he x)]
      let q := IdempotentSummand.quotient (R := Spectrum.H x.1.1)
        (U.curveIdempotentSpecialization basis e x)
      let := IdempotentSummand.finite (R := Spectrum.H x.1.1)
        (U.curveIdempotentSpecialization basis e x)
      exact (q.toLinearMap.finrank_le_finrank_of_surjective
        (Ideal.Quotient.mk_surjective)).trans_eq (Module.finrank_eq_card_basis
          (basis.baseChange (Spectrum.H x.1.1)))

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
