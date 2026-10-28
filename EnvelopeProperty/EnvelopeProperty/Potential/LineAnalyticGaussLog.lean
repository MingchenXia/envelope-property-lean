import EnvelopeProperty.Potential.LineAnalyticFubiniStudy
import EnvelopeProperty.Local.FiniteFlatNorm

/-! # Genuine weighted Gauss logarithms of actual completed analytic polynomials -/

open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K σ : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The genuine WHOLE specialized polynomial weighted Gauss logarithm, with bottom outside
the actual original carrier. -/
def analyticGaussLog (P : MvPolynomial σ U.AnalyticFunctions) (weight : σ → ℝ) (N : ℝ)
    (x : RelativeSpectrum w K[X]) : EReal := by
  classical
  exact if hx : x ∈ U.carrier then ((N⁻¹ : ℝ) : EReal)*
    ENNReal.log ((wgaussValuation NormedField.valuation (expRadius weight)
      (MvPolynomial.map (U.evaluationToH ⟨x,hx⟩) P) : ℝ≥0) : ℝ≥0∞) else ⊥

/-- The whole specialized polynomial retains the actual ORIGINAL analytic support formula,
including coefficients that vanish after specialization. -/
theorem analyticGaussLog_eq_analyticFubiniStudy (P : MvPolynomial σ U.AnalyticFunctions)
    (weight : σ → ℝ) (N : ℝ) (x : U.carrier) :
    U.analyticGaussLog P weight N x.1 = U.analyticFubiniStudy P.support P.coeff
      (fun β => β.sum fun j n => (n : ℝ)*weight j) N x.1 := by
  classical
  have hgauss : wgaussValuation NormedField.valuation (expRadius weight)
      (MvPolynomial.map (U.evaluationToH x) P) =
      P.support.sup (fun β => U.analyticValue (P.coeff β) x*monoWeight (expRadius weight) β) := by
    rw [wgaussValuation_eq_sup_of_subset _ _ _ (MvPolynomial.support_map_subset _ P)]
    apply Finset.sup_congr rfl
    intro β _
    rw [MvPolynomial.coeff_map]
    rfl
  simp only [analyticGaussLog,dif_pos x.2,analyticFubiniStudy,hgauss]
  congr 1
  rw [log_coe_nnreal_finsetSup]
  apply Finset.sup_congr rfl
  intro β _
  rw [ENNReal.coe_mul,ENNReal.log_mul_add,
    log_coe_nnreal_of_coe_eq_exp (coe_monoWeight_expRadius weight β)]
  rw [U.analyticLog_apply]

/-- Actual completed analytic norm-polynomial logarithms are genuinely line subharmonic;
no norm identity or subharmonicity certificate is assumed. -/
theorem isLineSubharmonicOn_analyticGaussLog (P : MvPolynomial σ U.AnalyticFunctions)
    (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) :
    IsLineSubharmonicOn (U.analyticGaussLog P weight N) (interior U.carrier) := by
  apply (U.isLineSubharmonicOn_analyticFubiniStudy P.support P.coeff
    (fun β => β.sum fun j n => (n : ℝ)*weight j) N hN).congr
  intro x hx
  exact (U.analyticGaussLog_eq_analyticFubiniStudy P weight N ⟨x,interior_subset hx⟩).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
