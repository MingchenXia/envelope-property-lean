import EnvelopeProperty.Potential.CurvePieceNormRefinement

/-! # Actual original all-point nonvanishing supplies a genuine quotient unit -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m)

/-- Original nonvanishing on the ENTIRE actual selected original piece DERIVES an
actual inverse in the true analytic quotient, including the empty piece. -/
theorem isUnit_curveIdempotentQuotientMap_of_nonvanishing
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (g : B) (hg : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, y.1.val g ≠ 0) :
    IsUnit (U.curveIdempotentQuotientMap basis e g) := by
  let := Module.Finite.of_basis basis
  apply (U.isUnit_curveIdempotentQuotient_iff basis he g).mpr
  apply (U.analyticFunctions_isUnit_iff _).mpr
  intro x
  change NormedField.valuation (U.evaluationToH x (U.curveIdempotentNorm basis he g)) ≠ 0
  rw [U.valuation_evaluation_curveIdempotentNorm basis he g x]
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  have hyP := (U.mem_completedIdempotentFibrePiece_iff_ambient basis e x y).mp hy
  exact pow_ne_zero _ (hg (U.curveFibreRelativePoint x y).1 hyP)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
