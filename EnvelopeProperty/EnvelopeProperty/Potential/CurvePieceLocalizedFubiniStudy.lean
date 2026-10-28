import EnvelopeProperty.Potential.CurvePieceLocalization
import EnvelopeProperty.Potential.CurveAnalyticPieces
import EnvelopeProperty.Potential.CurveAnalyticIdempotentNorm
import EnvelopeProperty.Potential.CurvePieceDecreasingLimits

/-! # Literal original localized finite FS norms are line subharmonic -/

open scoped NNReal ENNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι σ : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι] [Fintype σ]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

omit [Fintype ι] [Fintype σ] in
/-- The original evaluator retains its ENTIRE specified completed fibre. -/
theorem curveOriginalEvaluation_fibre (y : RelativeSpectrum w B) (x : U.carrier)
    (hy : comap (IsScalarTower.toAlgHom K K[X] B) y = x.1) (a : U.CurveAnalyticAlgebra basis) :
    ‖U.curveOriginalEvaluation basis ⟨y,hy ▸ x.2⟩ a‖₊ =
      (Spectrum.fibrePoint (congrArg Subtype.val hy)).1.val (U.curveIdempotentSpecialization basis a x) := by
  rcases x with ⟨x,hx⟩
  change comap (IsScalarTower.toAlgHom K K[X] B) y = x at hy
  subst x
  rw [U.curveOriginalEvaluation_specialization]
  rfl

/-- The literal original regular finite FS function on its true principal-open domain. -/
def localizedFubiniStudy (g : B) (b : σ → Localization.Away g) (weight : σ → ℝ) (N : ℝ)
    (y : Spectrum B) : EReal :=
  if hy : y.val g ≠ 0 then
    ((N⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun j =>
      Spectrum.logAbs (b j) (Spectrum.awayLift g y hy)+(weight j : EReal))
  else ⊥

omit [Fintype ι] [Fintype σ] in
/-- The whole representative has the exact original localized value at EVERY selected
original completed-fibre point, with denominator nonvanishing derived from the true unit. -/
theorem fibrePoint_curveIdempotentLocalizedLift_val
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (x : U.carrier) (y : Spectrum.Fibre (B := B) x.1.1)
    (hy : (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis e x) = 1)
    (b : Localization.Away g) :
    ∃ hgy : y.1.val g ≠ 0,
      (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis
        (U.curveIdempotentLocalizedLift basis e g hg b) x) =
          (Spectrum.awayLift g y.1 hgy).val b := by
  let yy := fcRelativeFibrePoint x.1 y
  have hbase : comap (IsScalarTower.toAlgHom K K[X] B) yy = x.1 := fcRelativeFibrePoint_base x.1 y
  let z : U.CurvePreimage (B := B) := ⟨yy,hbase ▸ x.2⟩
  have hz : z ∈ U.curveIdempotentOriginalPiece basis e := by
    have hn : ‖U.curveOriginalEvaluation basis z e‖₊ = 1 := by
      rw [U.curveOriginalEvaluation_fibre basis yy x hbase e]
      exact hy
    rw [U.curveOriginalEvaluation_specialization] at hn
    exact hn
  have hgy : y.1.val g ≠ 0 := U.curveIdempotentOriginalPiece_val_ne_zero basis he g hg z hz
  refine ⟨hgy,?_⟩
  exact (U.curveOriginalEvaluation_fibre basis yy x hbase
    (U.curveIdempotentLocalizedLift basis e g hg b)).symm.trans
      (U.nnnorm_curveIdempotentLocalizedLift_evaluation basis he g hg z hz b)

/-- The LITERAL original localized weighted norm is the genuine whole analytic Gauss log. -/
theorem curvePieceNorm_localizedFubiniStudy_eq_analyticGaussLog
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (b : σ → Localization.Away g) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) (x : U.carrier) :
    U.curvePieceNorm basis he (localizedFubiniStudy g b weight N) x.1 =
      U.analyticGaussLog (U.curveAnalyticIdempotentNormForm basis he
        (fun j => U.curveIdempotentLocalizedLift basis e g hg (b j))) weight N x.1 := by
  classical
  let := Module.Finite.of_basis basis
  let a := fun j => U.curveIdempotentLocalizedLift basis e g hg (b j)
  have hkey (y : Spectrum.Fibre (B := B) x.1.1)
      (hy : y ∈ Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x)) :
      localizedFubiniStudy g b weight N y.1 = ((N⁻¹ : ℝ) : EReal)*
        ENNReal.log ((Finset.univ.sup fun j =>
          (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis (a j) x)*expRadius weight j : ℝ≥0) : ℝ≥0∞) := by
    have hyval := (Finset.mem_filter.mp hy).2
    obtain ⟨hgy,_⟩ := U.fibrePoint_curveIdempotentLocalizedLift_val basis he g hg x y hyval 1
    simp only [localizedFubiniStudy,dif_pos hgy]
    congr 1
    rw [log_coe_nnreal_finsetSup]
    apply Finset.sup_congr rfl
    intro j _
    obtain ⟨_,hval⟩ := U.fibrePoint_curveIdempotentLocalizedLift_val basis he g hg x y hyval (b j)
    rw [ENNReal.coe_mul,ENNReal.log_mul_add,log_coe_nnreal_of_coe_eq_exp (coe_expRadius weight j)]
    change ENNReal.log (((Spectrum.awayLift g y.1 hgy).val (b j) : ℝ≥0∞))+(weight j : EReal) = _
    rw [← hval]
  rw [U.curvePieceNorm_apply]
  rw [Finset.sum_congr rfl (fun y hy => congrArg (fun q : EReal =>
    ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*q) (hkey y hy))]
  simp only [analyticGaussLog,dif_pos x.2]
  rw [Finset.sum_congr rfl (fun y _ => mul_left_comm _ _ _),
    ← ereal_coe_mul_finsetSum _ _ (inv_nonneg.mpr hN.le)]
  congr 1
  rw [Finset.sum_congr rfl (fun y _ => (log_coe_nnreal_pow _ _).symm),
    ← log_coe_nnreal_finsetProd,
    ← U.wgaussValuation_curveAnalyticIdempotentNormForm basis he a (expRadius weight) x]

/-- The actual original regular localized finite FS norm is comparison subharmonic. -/
theorem isLineSubharmonicOn_curvePieceNorm_localizedFubiniStudy
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (b : σ → Localization.Away g) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) :
    IsLineSubharmonicOn (U.curvePieceNorm basis he (localizedFubiniStudy g b weight N))
      (interior U.carrier) := by
  apply (U.isLineSubharmonicOn_analyticGaussLog (U.curveAnalyticIdempotentNormForm basis he
    (fun j => U.curveIdempotentLocalizedLift basis e g hg (b j))) weight N hN).congr
  intro x hx
  exact (U.curvePieceNorm_localizedFubiniStudy_eq_analyticGaussLog basis he g hg b weight N hN
    ⟨x,interior_subset hx⟩).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
