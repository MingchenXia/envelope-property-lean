import EnvelopeProperty.Potential.CurveAnalyticFractions
import EnvelopeProperty.Berkovich.IdempotentSummandTransport
import EnvelopeProperty.Berkovich.CompletedFibrePieceNorm

/-!
# Actual neighbourhood summand norms specialize with original curve fibre weights

An actual idempotent in the entire finite free analytic curve algebra gives
an actual quotient norm polynomial with analytic coefficients. Specializing
those coefficients is the genuine norm polynomial of the literal completed
fibre summand. Its weighted Gauss norm is computed on exactly the original
curve points selected by that specialized idempotent, with the original full
curve multiplicities. No selected-piece, norm or multiplicity identity is an input.
-/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

private local instance completedEvaluationAlgebra (x : U.carrier) :
    Algebra U.AnalyticFunctions (Spectrum.H x.1.1) := (U.evaluationToH x).toAlgebra

private local instance completedEvaluationTower (x : U.carrier) :
    IsScalarTower K[X] U.AnalyticFunctions (Spectrum.H x.1.1) :=
  IsScalarTower.of_algebraMap_eq (fun p => ((U.polynomialAnalyticEvaluation x).commutes p).symm)

/-- The genuine whole analytic-coefficient tensor specialization comparison. -/
def curveAnalyticCompletedTensorEquiv (x : U.carrier) :
    Spectrum.H x.1.1 ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B ≃ₐ[Spectrum.H x.1.1]
      Spectrum.H x.1.1 ⊗[K[X]] B :=
  Algebra.TensorProduct.cancelBaseChange K[X] U.AnalyticFunctions
    (Spectrum.H x.1.1) (Spectrum.H x.1.1) B

/-- The tensor comparison retains every original analytic tensor, not just the curve basis. -/
theorem curveAnalyticCompletedTensorEquiv_one_tmul (x : U.carrier) (z : U.CurveAnalyticTensor B) :
    U.curveAnalyticCompletedTensorEquiv x ((1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions] z) =
      U.curveAnalyticSpecialization x z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b =>
    simp only [curveAnalyticCompletedTensorEquiv, Algebra.TensorProduct.cancelBaseChange_tmul,
      curveAnalyticSpecialization, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (U.evaluationToH x a * 1) ⊗ₜ[K[X]] b = U.evaluationToH x a ⊗ₜ[K[X]] b
    rw [mul_one]

/-- The actual specialized idempotent in the same original completed curve fibre. -/
def curveIdempotentSpecialization (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) : Spectrum.H x.1.1 ⊗[K[X]] B :=
  U.curveAnalyticSpecialization x (U.curveAnalyticOriginalEquiv basis e)

omit [Fintype ι] in
/-- Genuine idempotence survives the actual whole original specialization. -/
theorem curveIdempotentSpecialization_isIdempotent (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (x : U.carrier) :
    IsIdempotentElem (U.curveIdempotentSpecialization basis e x) :=
  (he.map (U.curveAnalyticOriginalEquiv basis)).map (U.curveAnalyticSpecialization x)

/-- The scalar norm in the actual analytic quotient summand, with genuine analytic coefficients. -/
def curveIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) : U.AnalyticFunctions :=
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  IdempotentSummand.norm (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis)) ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)

/-- The WHOLE actual analytic summand norm polynomial, before specialization. -/
def curveIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → B) : MvPolynomial σ U.AnalyticFunctions :=
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  IdempotentSummand.normForm (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis)) (fun j => (1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b j)

/-- Specialization is equality of the entire actual summand norm polynomials. -/
theorem map_curveIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → B) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    MvPolynomial.map (U.evaluationToH x) (U.curveIdempotentNormForm basis he b) =
      IdempotentSummand.normForm (R := Spectrum.H x.1.1)
        ((he.map (U.curveAnalyticOriginalEquiv basis)).map (U.curveAnalyticSpecialization x))
        (fun j => (1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b j) := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let h := he.map (U.curveAnalyticOriginalEquiv basis)
  let g := U.curveAnalyticCompletedTensorEquiv (B := B) x
  change MvPolynomial.map (algebraMap U.AnalyticFunctions (Spectrum.H x.1.1))
    (IdempotentSummand.normForm h _) = _
  rw [IdempotentSummand.map_normForm_baseChange]
  have hh := IdempotentSummand.normForm_algEquiv g
    (h.map (Algebra.TensorProduct.includeRight : U.CurveAnalyticTensor B →ₐ[U.AnalyticFunctions]
      Spectrum.H x.1.1 ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B))
    (fun j => (1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions]
      ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b j))
  simpa only [g, h, Algebra.TensorProduct.includeRight_apply,
    curveAnalyticCompletedTensorEquiv_one_tmul, curveAnalyticSpecialization,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using hh.symm

/-- The same whole specialization retains the actual scalar summand norm. -/
theorem evaluation_curveIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    U.evaluationToH x (U.curveIdempotentNorm basis he b) =
      IdempotentSummand.norm (R := Spectrum.H x.1.1)
        (U.curveIdempotentSpecialization_isIdempotent basis he x)
        ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b) := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let h := he.map (U.curveAnalyticOriginalEquiv basis)
  let g := U.curveAnalyticCompletedTensorEquiv (B := B) x
  have hb := IdempotentSummand.norm_baseChange (R := U.AnalyticFunctions)
    (S := Spectrum.H x.1.1) h
    ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)
  have hg := IdempotentSummand.norm_algEquiv (R := Spectrum.H x.1.1) g
    (h.map (Algebra.TensorProduct.includeRight : U.CurveAnalyticTensor B →ₐ[U.AnalyticFunctions]
      Spectrum.H x.1.1 ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B))
    ((1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions] ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b))
  exact hb.symm.trans (by
    simpa only [g, h, Algebra.TensorProduct.includeRight_apply,
      curveIdempotentSpecialization, curveAnalyticCompletedTensorEquiv_one_tmul, curveAnalyticSpecialization,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using hg.symm)

/-- The actual neighbourhood scalar norm specializes over precisely the selected ORIGINAL curve points. -/
theorem valuation_evaluation_curveIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    NormedField.valuation (U.evaluationToH x (U.curveIdempotentNorm basis he b)) =
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        y.1.val b ^ Spectrum.fibreNormMult K[X] y.1 := by
  let := Module.Finite.of_basis basis
  rw [U.evaluation_curveIdempotentNorm basis he b x]
  simpa only [curveIdempotentSpecialization, Spectrum.fibrePoint_val_tmul, nnnorm_one, one_mul] using
    Spectrum.val_completedIdempotentNorm x.1.1
      (U.curveIdempotentSpecialization_isIdempotent basis he x) ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b)

/-- The WHOLE actual neighbourhood norm polynomial gives the ORIGINAL finite curve-piece weighted FS identity. -/
theorem wgaussValuation_curveIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (b : σ → B) (r : σ → ℝ≥0) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    wgaussValuation NormedField.valuation r
      (MvPolynomial.map (U.evaluationToH x) (U.curveIdempotentNormForm basis he b)) =
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        (Finset.univ.sup fun j => y.1.val (b j) * r j) ^ Spectrum.fibreNormMult K[X] y.1 := by
  let := Module.Finite.of_basis basis
  rw [U.map_curveIdempotentNormForm basis he b x]
  simpa only [curveIdempotentSpecialization, Spectrum.fibrePoint_val_tmul, nnnorm_one, one_mul] using
    Spectrum.wgaussValuation_completedIdempotentNormForm x.1.1
      (U.curveIdempotentSpecialization_isIdempotent basis he x)
      (fun j => (1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b j) r

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
