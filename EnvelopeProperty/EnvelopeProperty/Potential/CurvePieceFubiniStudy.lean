import EnvelopeProperty.Potential.CurveIdempotentNorm
import EnvelopeProperty.Potential.LineAnalyticGaussLog
import EnvelopeProperty.Potential.CurveAnalyticIdempotentLocality

/-! # Actual original weighted curve-piece FS norm is genuinely line subharmonic -/

open scoped NNReal ENNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι σ : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Fintype ι] [Fintype σ]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- The literal finite FS sum on the ACTUAL original fibre piece, with its ORIGINAL full
local-length times residue-degree multiplicities. -/
def curvePieceFubiniStudyNorm {e : U.CurveAnalyticAlgebra basis} (_he : IsIdempotentElem e)
    (b : σ → B) (weight : σ → ℝ) (N : ℝ) (x : RelativeSpectrum w K[X]) : EReal := by
  classical
  let := Module.Finite.of_basis basis
  exact if hx : x ∈ U.carrier then
    ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1 (U.curveIdempotentSpecialization basis e ⟨x,hx⟩),
      ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*
        (((N⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun j => Spectrum.logAbs (b j) y.1+(weight j : EReal)))
    else ⊥

/-- The exact norm polynomial is constructed from the GENUINE summand and retains the
original curve fibre points and original multiplicities. -/
theorem curvePieceFubiniStudyNorm_eq_analyticGaussLog
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (b : σ → B) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) (x : U.carrier) :
    U.curvePieceFubiniStudyNorm basis he b weight N x.1 =
      U.analyticGaussLog (U.curveIdempotentNormForm basis he b) weight N x.1 := by
  classical
  let := Module.Finite.of_basis basis
  have hkey (y : Spectrum.Fibre (B := B) x.1.1) :
      (Finset.univ.sup fun j => Spectrum.logAbs (b j) y.1+(weight j : EReal)) =
      ENNReal.log ((Finset.univ.sup fun j => y.1.val (b j)*expRadius weight j : ℝ≥0) : ℝ≥0∞) := by
    rw [log_coe_nnreal_finsetSup]
    apply Finset.sup_congr rfl
    intro j _
    rw [ENNReal.coe_mul,ENNReal.log_mul_add,log_coe_nnreal_of_coe_eq_exp (coe_expRadius weight j)]
    rfl
  simp only [curvePieceFubiniStudyNorm,dif_pos x.2,analyticGaussLog,hkey]
  rw [Finset.sum_congr rfl (fun y _ => mul_left_comm _ _ _),
    ← ereal_coe_mul_finsetSum _ _ (inv_nonneg.mpr hN.le)]
  congr 1
  rw [Finset.sum_congr rfl (fun y _ => (log_coe_nnreal_pow _ _).symm),
    ← log_coe_nnreal_finsetProd,← U.wgaussValuation_curveIdempotentNormForm basis he b (expRadius weight) x]

/-- The ACTUAL weighted norm on the original curve point piece is comparison-subharmonic;
the genuine norm polynomial and subharmonicity are both derived. -/
theorem isLineSubharmonicOn_curvePieceFubiniStudyNorm
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (b : σ → B) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) :
    IsLineSubharmonicOn (U.curvePieceFubiniStudyNorm basis he b weight N) (interior U.carrier) := by
  apply (U.isLineSubharmonicOn_analyticGaussLog (U.curveIdempotentNormForm basis he b) weight N hN).congr
  intro x hx
  exact (U.curvePieceFubiniStudyNorm_eq_analyticGaussLog basis he b weight N hN
    ⟨x,interior_subset hx⟩).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K B ι σ : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Fintype ι] [Fintype σ]

/-- The actual original point-piece norm is subharmonic on an ACTUALLY constructed
neighbourhood inside any prescribed neighbourhood; no analytic idempotent is an input. -/
theorem fc_exists_standardAffinoid_point_fubiniStudyNorm_subharmonic
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) (y : Spectrum.Fibre (B := B) x.1)
    (Nset : Set (RelativeSpectrum w K[X])) (hNset : Nset ∈ 𝓝 x)
    (b : σ → B) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      U.carrier ⊆ Nset ∧ ∃ e : U.CurveAnalyticAlgebra basis, ∃ he : IsIdempotentElem e,
        (∀ z : Spectrum.Fibre (B := B) x.1,
          Spectrum.fibreHom z.2
            (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis e)) =
              if z = y then 1 else 0) ∧
        IsLineSubharmonicOn (U.curvePieceFubiniStudyNorm basis he b weight N) (interior U.carrier) := by
  obtain ⟨m,U,hx,hUN,e,he,hvalues⟩ :=
    fc_exists_standardAffinoid_analytic_point_idempotent_nhds x basis y Nset hNset
  exact ⟨m,U,hx,hUN,e,he,hvalues,U.isLineSubharmonicOn_curvePieceFubiniStudyNorm basis he b weight N hN⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum
