import EnvelopeProperty.Potential.CurveIdempotentNorm

/-!
# Genuine summand norms of arbitrary whole analytic curve elements

The analytic elements may have arbitrary completed analytic coefficients.
The actual scalar norm and the entire norm polynomial specialize to the
same completed quotient summand. The original full nonreduced curve weights
compute their scalar and weighted Gauss values, without an original-B-only
restriction on the family.
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

/-- The genuine scalar quotient norm of an arbitrary WHOLE analytic curve element. -/
def curveAnalyticIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : U.CurveAnalyticAlgebra basis) : U.AnalyticFunctions :=
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  IdempotentSummand.norm (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis)) (U.curveAnalyticOriginalEquiv basis a)

/-- The ENTIRE genuine quotient norm polynomial for arbitrary whole analytic elements. -/
def curveAnalyticIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (a : σ → U.CurveAnalyticAlgebra basis) :
    MvPolynomial σ U.AnalyticFunctions :=
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  IdempotentSummand.normForm (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis)) (fun j => U.curveAnalyticOriginalEquiv basis (a j))

/-- Genuine whole-coefficient specialization of the entire arbitrary-analytic norm polynomial. -/
theorem map_curveAnalyticIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (a : σ → U.CurveAnalyticAlgebra basis) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    MvPolynomial.map (U.evaluationToH x) (U.curveAnalyticIdempotentNormForm basis he a) =
      IdempotentSummand.normForm (R := Spectrum.H x.1.1)
        (U.curveIdempotentSpecialization_isIdempotent basis he x)
        (fun j => U.curveIdempotentSpecialization basis (a j) x) := by
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
    (fun j => (1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions] U.curveAnalyticOriginalEquiv basis (a j))
  simpa only [g, h, Algebra.TensorProduct.includeRight_apply,
    curveAnalyticCompletedTensorEquiv_one_tmul, curveIdempotentSpecialization] using hh.symm

/-- The same entire coefficient specialization preserves the actual scalar norm. -/
theorem evaluation_curveAnalyticIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : U.CurveAnalyticAlgebra basis) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    U.evaluationToH x (U.curveAnalyticIdempotentNorm basis he a) =
      IdempotentSummand.norm (R := Spectrum.H x.1.1)
        (U.curveIdempotentSpecialization_isIdempotent basis he x)
        (U.curveIdempotentSpecialization basis a x) := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let h := he.map (U.curveAnalyticOriginalEquiv basis)
  let g := U.curveAnalyticCompletedTensorEquiv (B := B) x
  have hb := IdempotentSummand.norm_baseChange (R := U.AnalyticFunctions)
    (S := Spectrum.H x.1.1) h (U.curveAnalyticOriginalEquiv basis a)
  have hg := IdempotentSummand.norm_algEquiv (R := Spectrum.H x.1.1) g
    (h.map (Algebra.TensorProduct.includeRight : U.CurveAnalyticTensor B →ₐ[U.AnalyticFunctions]
      Spectrum.H x.1.1 ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B))
    ((1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions] U.curveAnalyticOriginalEquiv basis a)
  exact hb.symm.trans (by
    simpa only [g, h, Algebra.TensorProduct.includeRight_apply,
      curveIdempotentSpecialization, curveAnalyticCompletedTensorEquiv_one_tmul] using hg.symm)

/-- The arbitrary whole analytic norm has the ORIGINAL full-weight product formula. -/
theorem valuation_evaluation_curveAnalyticIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : U.CurveAnalyticAlgebra basis) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    NormedField.valuation (U.evaluationToH x (U.curveAnalyticIdempotentNorm basis he a)) =
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis a x) ^
          Spectrum.fibreNormMult K[X] y.1 := by
  let := Module.Finite.of_basis basis
  rw [U.evaluation_curveAnalyticIdempotentNorm basis he a x]
  exact Spectrum.val_completedIdempotentNorm x.1.1
    (U.curveIdempotentSpecialization_isIdempotent basis he x)
    (U.curveIdempotentSpecialization basis a x)

/-- Arbitrary analytic norm polynomials have the ORIGINAL weighted finite maximum product. -/
theorem wgaussValuation_curveAnalyticIdempotentNormForm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {σ : Type*} [Fintype σ] (a : σ → U.CurveAnalyticAlgebra basis) (r : σ → ℝ≥0)
    (x : U.carrier) :
    let := Module.Finite.of_basis basis
    wgaussValuation NormedField.valuation r
      (MvPolynomial.map (U.evaluationToH x) (U.curveAnalyticIdempotentNormForm basis he a)) =
      ∏ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
        (U.curveIdempotentSpecialization basis e x),
        (Finset.univ.sup fun j =>
          (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis (a j) x) * r j) ^
            Spectrum.fibreNormMult K[X] y.1 := by
  let := Module.Finite.of_basis basis
  rw [U.map_curveAnalyticIdempotentNormForm basis he a x]
  exact Spectrum.wgaussValuation_completedIdempotentNormForm x.1.1
    (U.curveIdempotentSpecialization_isIdempotent basis he x)
    (fun j => U.curveIdempotentSpecialization basis (a j) x) r

omit [IsAlgClosed K] in
/-- The zero analytic summand has actual scalar norm one for every whole element. -/
theorem curveAnalyticIdempotentNorm_zero (basis : Module.Basis ι K[X] B)
    (a : U.CurveAnalyticAlgebra basis) :
    U.curveAnalyticIdempotentNorm basis IsIdempotentElem.zero a = 1 := by
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  exact IdempotentSummand.norm_zero (U.curveAnalyticOriginalEquiv basis a)

omit [IsAlgClosed K] in
/-- Its entire arbitrary-analytic norm polynomial is the actual constant polynomial one. -/
theorem curveAnalyticIdempotentNormForm_zero (basis : Module.Basis ι K[X] B)
    {σ : Type*} [Fintype σ] (a : σ → U.CurveAnalyticAlgebra basis) :
    U.curveAnalyticIdempotentNormForm basis IsIdempotentElem.zero a = 1 := by
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  exact IdempotentSummand.normForm_zero (fun j => U.curveAnalyticOriginalEquiv basis (a j))

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
