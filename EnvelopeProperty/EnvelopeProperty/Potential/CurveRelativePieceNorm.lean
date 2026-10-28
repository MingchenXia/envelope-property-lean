import EnvelopeProperty.Potential.CurvePieceNormRefinement

/-! # Literal original weighted traces of functions on the prescribed-base curve -/

open scoped NNReal ENNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

/-- The ORIGINAL relative function, extended by bottom away from its exact coefficient locus. -/
def extendRelativeFunction {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {v : Valuation R ℝ≥0} (u : RelativeSpectrum v A → EReal) (y : Spectrum A) : EReal :=
  if hy : y ∈ relativeLocus v A then u ⟨y,hy⟩ else ⊥

theorem extendRelativeFunction_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {v : Valuation R ℝ≥0} (u : RelativeSpectrum v A → EReal) (y : RelativeSpectrum v A) :
    extendRelativeFunction u y.1 = u y := by
  simp only [extendRelativeFunction,dif_pos y.2]

namespace FCStandardAffinoid
variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- The literal selected ORIGINAL relative point values with their ORIGINAL full weights. -/
def curveRelativePieceNorm {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) : RelativeSpectrum w K[X] → EReal :=
  U.curvePieceNorm basis he (extendRelativeFunction u)

theorem curveRelativePieceNorm_apply {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (x : U.carrier) :
    let := Module.Finite.of_basis basis
    U.curveRelativePieceNorm basis he u x.1 =
      ∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x),
        ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*u (U.curveFibreRelativePoint x y).1 := by
  let := Module.Finite.of_basis basis
  rw [curveRelativePieceNorm,U.curvePieceNorm_apply basis he _ x]
  apply Finset.sum_congr rfl
  intro y _
  exact congrArg (fun q : EReal => ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*q)
    (extendRelativeFunction_coe u (U.curveFibreRelativePoint x y).1)

/-- Equality is required ONLY on the actual selected original piece. -/
theorem curveRelativePieceNorm_eq_pieceNorm_of_eq_on_piece
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (v : Spectrum B → EReal)
    (huv : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, u y = v y.1) (x : U.carrier) :
    U.curveRelativePieceNorm basis he u x.1 = U.curvePieceNorm basis he v x.1 := by
  let := Module.Finite.of_basis basis
  rw [U.curveRelativePieceNorm_apply basis he u x,U.curvePieceNorm_apply basis he v x]
  apply Finset.sum_congr rfl
  intro y hy
  exact congrArg (fun q : EReal => ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*q)
    (huv (U.curveFibreRelativePoint x y).1
      ((U.mem_completedIdempotentFibrePiece_iff_ambient basis e x y).mp hy))

omit [IsScalarTower K K[X] B] in
theorem curveRelativePieceNorm_restriction (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (x : V.carrier) :
    V.curveRelativePieceNorm basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) u x.1 =
      U.curveRelativePieceNorm basis he u x.1 :=
  U.curvePieceNorm_restriction V hVU basis he (extendRelativeFunction u) x

theorem curveRelativePieceNorm_partition {J : Type*} [Fintype J]
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : J → U.CurveAnalyticAlgebra basis) (ha : ∀ j, IsIdempotentElem (a j))
    (hcover : U.curveIdempotentAmbientPiece basis e = ⋃ j, U.curveIdempotentAmbientPiece basis (a j))
    (hdisj : Pairwise (fun i j => Disjoint (U.curveIdempotentAmbientPiece basis (a i))
      (U.curveIdempotentAmbientPiece basis (a j))))
    (u : RelativeSpectrum w B → EReal) (x : U.carrier) :
    U.curveRelativePieceNorm basis he u x.1 = ∑ j, U.curveRelativePieceNorm basis (ha j) u x.1 :=
  U.curvePieceNorm_partition basis he a ha hcover hdisj (extendRelativeFunction u) x

/-- Equality only on the actual original piece preserves its entire literal trace. -/
theorem curveRelativePieceNorm_congr {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u v : RelativeSpectrum w B → EReal)
    (huv : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, u y = v y) (x : U.carrier) :
    U.curveRelativePieceNorm basis he u x.1 = U.curveRelativePieceNorm basis he v x.1 :=
  U.curveRelativePieceNorm_eq_pieceNorm_of_eq_on_piece basis he u (extendRelativeFunction v)
    (fun y hy => (huv y hy).trans (extendRelativeFunction_coe v y).symm) x

/-- Monotonicity only uses values on the ACTUAL entire selected original piece. -/
theorem curveRelativePieceNorm_mono {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u v : RelativeSpectrum w B → EReal)
    (huv : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, u y ≤ v y) (x : U.carrier) :
    U.curveRelativePieceNorm basis he u x.1 ≤ U.curveRelativePieceNorm basis he v x.1 := by
  let := Module.Finite.of_basis basis
  rw [U.curveRelativePieceNorm_apply basis he u x,U.curveRelativePieceNorm_apply basis he v x]
  apply Finset.sum_le_sum
  intro y hy
  exact mul_le_mul_of_nonneg_left
    (huv (U.curveFibreRelativePoint x y).1
      ((U.mem_completedIdempotentFibrePiece_iff_ambient basis e x y).mp hy)) (by positivity)

variable {J : Type*} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]

/-- Directed decreasing trace limits use hypotheses ONLY on the actual entire piece. -/
theorem curveRelativePieceNorm_iInf_of_antitone_net
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : J → RelativeSpectrum w B → EReal)
    (hanti : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, Antitone (fun j => u j y))
    (hut : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, ∀ j, u j y ≠ ⊤) (x : U.carrier) :
    U.curveRelativePieceNorm basis he (fun y => ⨅ j, u j y) x.1 =
      ⨅ j, U.curveRelativePieceNorm basis he (u j) x.1 := by
  let := Module.Finite.of_basis basis
  let S := Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x)
  have hmem (y) (hy : y ∈ S) :
      (U.curveFibreRelativePoint x y).1 ∈ U.curveIdempotentAmbientPiece basis e :=
    (U.mem_completedIdempotentFibrePiece_iff_ambient basis e x y).mp hy
  rw [U.curveRelativePieceNorm_apply basis he _ x]
  have hpoint (j : J) := U.curveRelativePieceNorm_apply basis he (u j) x
  simp_rw [hpoint]
  exact (iInf_finsetSum_coe_mul_of_antitone_net S
    (fun y => (Spectrum.fibreNormMult K[X] y.1 : ℝ)) (fun y _ => by positivity)
    (fun y j => u j (U.curveFibreRelativePoint x y).1)
    (fun y hy => hanti _ (hmem y hy)) (fun y hy j => hut _ (hmem y hy) j)).symm

/-- Actual comparison trace subharmonicity passes to decreasing directed limits;
all value hypotheses are restricted to the genuine selected original piece. -/
theorem isLineSubharmonicOn_curveRelativePieceNorm_iInf
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : J → RelativeSpectrum w B → EReal)
    (hanti : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, Antitone (fun j => u j y))
    (hut : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, ∀ j, u j y ≠ ⊤)
    (hsh : ∀ j, IsLineSubharmonicOn (U.curveRelativePieceNorm basis he (u j)) (interior U.carrier)) :
    IsLineSubharmonicOn (U.curveRelativePieceNorm basis he (fun y => ⨅ j, u j y))
      (interior U.carrier) := by
  have hdir : Directed (· ≥ ·)
      (fun j (x : interior U.carrier) => U.curveRelativePieceNorm basis he (u j) x.1) := by
    intro i j
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact ⟨k,fun x => U.curveRelativePieceNorm_mono basis he _ _
      (fun y hy => hanti y hy hik) ⟨x.1,interior_subset x.2⟩,
      fun x => U.curveRelativePieceNorm_mono basis he _ _
        (fun y hy => hanti y hy hjk) ⟨x.1,interior_subset x.2⟩⟩
  apply (IsLineSubharmonicOn.iInf_directed (fun j => U.curveRelativePieceNorm basis he (u j)) hsh hdir).congr
  intro x hx
  exact (U.curveRelativePieceNorm_iInf_of_antitone_net basis he u hanti hut
    ⟨x,interior_subset hx⟩).symm

end FCStandardAffinoid
end EnvelopeProperty.Berkovich.RelativeSpectrum
