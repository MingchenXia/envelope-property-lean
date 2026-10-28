import EnvelopeProperty.Potential.CurvePieceFubiniStudy
import EnvelopeProperty.Potential.FiniteWeightedDecreasingLimits
import EnvelopeProperty.Potential.LineSubharmonicLimits

/-! # Genuine directed decreasing limits of actual original curve-piece weighted norms -/

open scoped NNReal ENNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- The literal finite norm with the original whole curve-fibre points and multiplicities. -/
def curvePieceNorm {e : U.CurveAnalyticAlgebra basis} (_he : IsIdempotentElem e)
    (u : Spectrum B → EReal) (x : RelativeSpectrum w K[X]) : EReal := by
  classical
  let := Module.Finite.of_basis basis
  exact if hx : x ∈ U.carrier then
    ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1 (U.curveIdempotentSpecialization basis e ⟨x,hx⟩),
      ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*u y.1
    else ⊥

theorem curvePieceNorm_apply {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : Spectrum B → EReal) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    U.curvePieceNorm basis he u x.1 =
      ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x),
        ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*u y.1 := by
  simp only [curvePieceNorm,dif_pos x.2]

theorem curvePieceNorm_mono {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {u v : Spectrum B → EReal} (huv : ∀ y, u y ≤ v y) (x : RelativeSpectrum w K[X]) :
    U.curvePieceNorm basis he u x ≤ U.curvePieceNorm basis he v x := by
  classical
  let := Module.Finite.of_basis basis
  by_cases hx : x ∈ U.carrier
  · simp only [curvePieceNorm,dif_pos hx]
    exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (huv y.1) (by positivity)
  · simp only [curvePieceNorm,dif_neg hx,le_refl]

variable {J : Type*} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]

/-- Actual finite original multiplicity-weighted piece norms commute with genuine decreasing
directed-net infima, including bottom values. -/
theorem curvePieceNorm_iInf_of_antitone_net {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : J → Spectrum B → EReal) (hanti : ∀ y, Antitone (fun j => u j y))
    (hut : ∀ j y, u j y ≠ ⊤) (x : RelativeSpectrum w K[X]) :
    U.curvePieceNorm basis he (fun y => ⨅ j, u j y) x = ⨅ j, U.curvePieceNorm basis he (u j) x := by
  classical
  let := Module.Finite.of_basis basis
  by_cases hx : x ∈ U.carrier
  · let xx : U.carrier := ⟨x,hx⟩
    have happly (v : Spectrum B → EReal) : U.curvePieceNorm basis he v x =
        ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1 (U.curveIdempotentSpecialization basis e xx),
          ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*v y.1 := U.curvePieceNorm_apply basis he v xx
    simp_rw [happly]
    let S := Spectrum.completedIdempotentFibrePiece x.1 (U.curveIdempotentSpecialization basis e xx)
    let c : Spectrum.Fibre (B := B) x.1 → ℝ := fun y => Spectrum.fibreNormMult K[X] y.1
    have hc : ∀ y ∈ S, 0 ≤ c y := fun y _ => by positivity
    have hs := iInf_finsetSum_coe_mul_of_antitone_net S c hc (fun y j => u j y.1)
      (fun y _ => hanti y.1) (fun y _ j => hut j y.1)
    exact hs.symm
  · have hbot (v : Spectrum B → EReal) : U.curvePieceNorm basis he v x = ⊥ := by
      simp only [curvePieceNorm,dif_neg hx]
    simp_rw [hbot]
    exact (iInf_const : (⨅ _ : J, (⊥ : EReal)) = ⊥).symm

/-- Source comparison subharmonicity of the norms is closed under actual decreasing limits,
using genuine original finite pieces and original multiplicities throughout. -/
theorem isLineSubharmonicOn_curvePieceNorm_iInf {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : J → Spectrum B → EReal) (hanti : ∀ y, Antitone (fun j => u j y))
    (hut : ∀ j y, u j y ≠ ⊤)
    (hsh : ∀ j, IsLineSubharmonicOn (U.curvePieceNorm basis he (u j)) (interior U.carrier)) :
    IsLineSubharmonicOn (U.curvePieceNorm basis he (fun y => ⨅ j, u j y)) (interior U.carrier) := by
  have hdir : Directed (· ≥ ·)
      (fun j (x : interior U.carrier) => U.curvePieceNorm basis he (u j) x.1) := by
    intro i j
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact ⟨k,fun x => U.curvePieceNorm_mono basis he (fun y => hanti y hik) x.1,
      fun x => U.curvePieceNorm_mono basis he (fun y => hanti y hjk) x.1⟩
  apply (IsLineSubharmonicOn.iInf_directed (fun j => U.curvePieceNorm basis he (u j)) hsh hdir).congr
  intro x _
  exact (U.curvePieceNorm_iInf_of_antitone_net basis he u hanti hut x).symm

/-- Actual finite FS expressions have finite-above values, even with zero or empty terms. -/
private theorem fc_original_finite_fs_ne_top {σ : Type*} [Fintype σ]
    (b : σ → B) (weight : σ → ℝ) (N : ℝ) (hN : 0 < N) (y : Spectrum B) :
    (((N⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun j => Spectrum.logAbs (b j) y+(weight j : EReal))) ≠ ⊤ := by
  apply ereal_coe_mul_ne_top (inv_nonneg.mpr hN.le)
  apply ne_of_lt
  apply (Finset.sup_lt_iff (show (⊥ : EReal) < ⊤ from bot_lt_top)).mpr
  intro j _
  exact lt_top_iff_ne_top.mpr (EReal.add_ne_top (Spectrum.logAbs_ne_top (b j) y) (EReal.coe_ne_top _))

/-- Every genuine decreasing net of ORIGINAL finite FS functions has a genuinely
subharmonic actual point-piece norm. Its finite term types may vary with the net index. -/
theorem isLineSubharmonicOn_curvePieceNorm_iInf_fubiniStudy
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (σ : J → Type*) [∀ j, Fintype (σ j)] (b : (j : J) → σ j → B)
    (weight : (j : J) → σ j → ℝ) (N : J → ℝ) (hN : ∀ j, 0 < N j)
    (hanti : ∀ y : Spectrum B, Antitone (fun j =>
      (((N j)⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun i => Spectrum.logAbs (b j i) y+(weight j i : EReal)))) :
    IsLineSubharmonicOn (U.curvePieceNorm basis he (fun y => ⨅ j,
      (((N j)⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun i => Spectrum.logAbs (b j i) y+(weight j i : EReal))))
      (interior U.carrier) := by
  apply U.isLineSubharmonicOn_curvePieceNorm_iInf basis he _ hanti
    (fun j y => fc_original_finite_fs_ne_top (b j) (weight j) (N j) (hN j) y)
  intro j
  have heq : U.curvePieceNorm basis he (fun y =>
      (((N j)⁻¹ : ℝ) : EReal)*(Finset.univ.sup fun i => Spectrum.logAbs (b j i) y+(weight j i : EReal))) =
      U.curvePieceFubiniStudyNorm basis he (b j) (weight j) (N j) := by
    funext x
    rfl
  rw [heq]
  exact U.isLineSubharmonicOn_curvePieceFubiniStudyNorm basis he (b j) (weight j) (N j) (hN j)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
