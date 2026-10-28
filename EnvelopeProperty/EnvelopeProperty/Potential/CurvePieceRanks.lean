import EnvelopeProperty.Potential.CurveIdempotentNorm
import EnvelopeProperty.Berkovich.CompletedPieceRank
import EnvelopeProperty.Berkovich.SpectrumSupport

/-!
# Constant actual original piece weights on connected standard affinoids

The actual analytic quotient summand is finite projective, so its true prime
stalk rank is locally constant. The genuine analytic-spectrum homeomorphism
pulls this rank back to the original connected carrier. Actual quotient tensor
comparison identifies it with the total ORIGINAL curve-piece multiplicity.
No global free summand basis or rank/weight-constancy certificate is an input.
-/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

private local instance rankEvaluationAlgebra (x : U.carrier) :
    Algebra U.AnalyticFunctions (Spectrum.H x.1.1) := (U.evaluationToH x).toAlgebra

/-- The actual analytic quotient specializes to the actual quotient of the same original completed fibre. -/
def curveIdempotentCompletedSummandEquiv (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) :
    Spectrum.H x.1.1 ⊗[U.AnalyticFunctions]
      IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e) ≃ₐ[Spectrum.H x.1.1]
      IdempotentSummand.Summand (U.curveIdempotentSpecialization basis e x) :=
  (IdempotentSummand.baseChangeEquiv (Spectrum.H x.1.1)
    (U.curveAnalyticOriginalEquiv basis e)).trans
    ((IdempotentSummand.congr (U.curveAnalyticCompletedTensorEquiv x)
      ((1 : Spectrum.H x.1.1) ⊗ₜ[U.AnalyticFunctions] U.curveAnalyticOriginalEquiv basis e)).trans
      (Ideal.quotientEquivAlgOfEq (Spectrum.H x.1.1) (by
        rw [U.curveAnalyticCompletedTensorEquiv_one_tmul x]
        rfl)))

/-- The genuine original analytic evaluation support in the actual coefficient ring spectrum. -/
def analyticEvaluationSupport (x : U.carrier) : PrimeSpectrum U.AnalyticFunctions :=
  Spectrum.support (U.analyticSpectrumHomeomorph.symm x).1.1

/-- These actual supports vary continuously on the original carrier. -/
theorem continuous_analyticEvaluationSupport : Continuous U.analyticEvaluationSupport :=
  Spectrum.continuous_support.comp
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp U.analyticSpectrumHomeomorph.symm.continuous))

/-- The original analytic support is exactly the prime contracted by the same actual field evaluator. -/
theorem analyticEvaluationSupport_eq (x : U.carrier) :
    U.analyticEvaluationSupport x =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Spectrum.H x.1.1)).comap
        (U.evaluationToH x) := by
  apply PrimeSpectrum.ext
  ext f
  change (U.analyticSpectrumHomeomorph.symm x).1.1.val f = 0 ↔ U.evaluationToH x f = 0
  rw [U.analyticSpectrumHomeomorph_symm_val]
  exact nnnorm_eq_zero

/-- The actual prime-stalk rank of the genuine analytic quotient summand. -/
def curveIdempotentRank (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) : ℕ :=
  Module.rankAtStalk (IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e))
    (U.analyticEvaluationSupport x)

/-- Genuine finite projectivity makes this actual original rank locally constant. -/
theorem isLocallyConstant_curveIdempotentRank (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) :
    IsLocallyConstant (U.curveIdempotentRank basis e) := by
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let Q := IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e)
  let := IdempotentSummand.finite (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e)
  let := IdempotentSummand.projective (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis))
  let : Module.FinitePresentation U.AnalyticFunctions Q :=
    Module.finitePresentation_of_projective U.AnalyticFunctions Q
  exact (Module.isLocallyConstant_rankAtStalk (R := U.AnalyticFunctions) (M := Q)).comp_continuous
    U.continuous_analyticEvaluationSupport

/-- Connectedness of the actual original standard carrier makes the genuine quotient rank constant. -/
theorem curveIdempotentRank_eq (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (x y : U.carrier) :
    U.curveIdempotentRank basis e x = U.curveIdempotentRank basis e y := by
  let : ConnectedSpace U.carrier := isConnected_iff_connectedSpace.mp U.isConnected_carrier
  exact (U.isLocallyConstant_curveIdempotentRank basis he).apply_eq_of_preconnectedSpace x y

/-- The literal sum of ORIGINAL curve multiplicities on the actual specialized idempotent piece. -/
def curveIdempotentPieceWeight (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) : ℕ :=
  let := Module.Finite.of_basis basis
  ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
    (U.curveIdempotentSpecialization basis e x), Spectrum.fibreNormMult K[X] y.1

/-- The actual original total piece weight equals the genuine analytic quotient rank. -/
theorem curveIdempotentPieceWeight_eq_rank (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (x : U.carrier) :
    U.curveIdempotentPieceWeight basis e x = U.curveIdempotentRank basis e x := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let := IdempotentSummand.finite (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e)
  let := IdempotentSummand.projective (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis))
  change (∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
    (U.curveIdempotentSpecialization basis e x), Spectrum.fibreNormMult K[X] y.1) = _
  rw [Spectrum.sum_completedIdempotentFibrePiece_eq_finrank x.1.1
    (U.curveIdempotentSpecialization_isIdempotent basis he x),
    ← (U.curveIdempotentCompletedSummandEquiv basis e x).toLinearEquiv.finrank_eq,
    Spectrum.finiteFlat_finrank_field_eq_rankAtStalk]
  change Module.rankAtStalk _ _ = Module.rankAtStalk _ (U.analyticEvaluationSupport x)
  rw [U.analyticEvaluationSupport_eq x]
  rfl

/-- The total ORIGINAL nonreduced fibre-piece weight is constant on the entire actual connected carrier. -/
theorem curveIdempotentPieceWeight_eq (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (x y : U.carrier) :
    U.curveIdempotentPieceWeight basis e x = U.curveIdempotentPieceWeight basis e y := by
  rw [U.curveIdempotentPieceWeight_eq_rank basis he x,
    U.curveIdempotentPieceWeight_eq_rank basis he y, U.curveIdempotentRank_eq basis he x y]

/-- An actual selected original fibre point gives a positive total ORIGINAL piece weight. -/
theorem curveIdempotentPieceWeight_pos (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier)
    (y : Spectrum.Fibre (B := B) x.1.1)
    (hy : (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis e x) = 1) :
    0 < U.curveIdempotentPieceWeight basis e x := by
  let := Module.Finite.of_basis basis
  let := Spectrum.finite_fibre (B := B) x.1.1
  let := Fintype.ofFinite (Spectrum.Fibre (B := B) x.1.1)
  have hmem : y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
      (U.curveIdempotentSpecialization basis e x) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  have hle := Finset.single_le_sum (fun z _ => Nat.zero_le (Spectrum.fibreNormMult K[X] z.1)) hmem
  exact (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0)
    (Spectrum.one_le_fibreNormMult (B := K[X]) y.1)).trans_le hle

/-- One actual selected point makes this same constant ORIGINAL weight positive everywhere on the carrier. -/
theorem curveIdempotentPieceWeight_pos_everywhere (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (x : U.carrier)
    (y : Spectrum.Fibre (B := B) x.1.1)
    (hy : (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis e x) = 1)
    (z : U.carrier) : 0 < U.curveIdempotentPieceWeight basis e z := by
  rw [U.curveIdempotentPieceWeight_eq basis he z x]
  exact U.curveIdempotentPieceWeight_pos basis e x y hy

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
