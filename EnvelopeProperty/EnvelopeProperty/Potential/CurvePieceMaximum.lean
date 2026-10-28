import EnvelopeProperty.Potential.CurveRelativePieceNorm
import EnvelopeProperty.Potential.CurvePieceRanks
import EnvelopeProperty.Potential.FiniteWeightedMaximum

/-! # Actual whole piece neighbourhoods and literal positive weighted maximum saturation -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- The literal whole original piece is an ORIGINAL ambient neighbourhood above
the actual base interior. -/
theorem curveIdempotentAmbientPiece_mem_nhds {e : U.CurveAnalyticAlgebra basis}
    (he : IsIdempotentElem e) (y : RelativeSpectrum w B)
    (hy : y ∈ U.curveIdempotentAmbientPiece basis e)
    (hint : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ interior U.carrier) :
    U.curveIdempotentAmbientPiece basis e ∈ 𝓝 y := by
  let z : U.CurvePreimage (B := B) := ⟨y,interior_subset hint⟩
  have hn : ((Subtype.val : U.CurvePreimage (B := B) → RelativeSpectrum w B) ⁻¹'
      U.curveIdempotentAmbientPiece basis e) ∈ 𝓝 z :=
    (U.isClopen_preimage_curveIdempotentAmbientPiece basis he).isOpen.mem_nhds hy
  rw [nhds_subtype_eq_comap] at hn
  obtain ⟨N,hN,hsub⟩ := hn
  have hcarrier : comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier ∈ 𝓝 y := by
    apply Filter.mem_of_superset
      (((isOpen_interior.preimage (continuous_comap (IsScalarTower.toAlgHom K K[X] B))).mem_nhds hint))
    exact fun z hz => (interior_subset : interior U.carrier ⊆ U.carrier) hz
  filter_upwards [hN,hcarrier] with z hzN hzU
  exact hsub (show (⟨z,hzU⟩ : U.CurvePreimage (B := B)) ∈ Subtype.val ⁻¹' N from hzN)

private theorem fc_coe_real_finset_sum {J : Type*} (S : Finset J) (f : J → ℝ) :
    ((∑ j ∈ S, f j : ℝ) : EReal) = ∑ j ∈ S, (f j : EReal) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,EReal.coe_zero]
  | insert j S hj ih => rw [Finset.sum_insert hj,Finset.sum_insert hj,EReal.coe_add,ih]

/-- The real constant norm uses the EXACT total original full piece weight. -/
theorem curveRelativePieceNorm_const {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (R : ℝ) (x : U.carrier) :
    U.curveRelativePieceNorm basis he (fun _ => (R : EReal)) x.1 =
      (((U.curveIdempotentPieceWeight basis e x : ℝ)*R : ℝ) : EReal) := by
  let := Module.Finite.of_basis basis
  rw [U.curveRelativePieceNorm_apply basis he _ x]
  simp only [← EReal.coe_mul]
  rw [← fc_coe_real_finset_sum,← Finset.sum_mul]
  congr 2
  simp only [curveIdempotentPieceWeight,Nat.cast_sum]

/-- Upper bounds are needed only on the ACTUAL entire selected original piece. -/
theorem curveRelativePieceNorm_le_const {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (R : ℝ)
    (hu : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, u y ≤ (R : EReal)) (x : U.carrier) :
    U.curveRelativePieceNorm basis he u x.1 ≤
      (((U.curveIdempotentPieceWeight basis e x : ℝ)*R : ℝ) : EReal) := by
  rw [← U.curveRelativePieceNorm_const basis he R x]
  exact U.curveRelativePieceNorm_mono basis he u _ hu x

/-- Constant values on the actual CENTRAL selected fibre give its exact literal trace. -/
theorem curveRelativePieceNorm_eq_const_of_central_eq
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (R : ℝ) (x : U.carrier)
    (hu : ∀ y ∈ U.curveIdempotentAmbientPiece basis e,
      comap (IsScalarTower.toAlgHom K K[X] B) y = x.1 → u y = (R : EReal)) :
    U.curveRelativePieceNorm basis he u x.1 =
      (((U.curveIdempotentPieceWeight basis e x : ℝ)*R : ℝ) : EReal) := by
  let := Module.Finite.of_basis basis
  rw [← U.curveRelativePieceNorm_const basis he R x,
    U.curveRelativePieceNorm_apply basis he u x,U.curveRelativePieceNorm_apply basis he _ x]
  apply Finset.sum_congr rfl
  intro y hy
  apply congrArg (fun q : EReal => ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*q)
  exact hu (U.curveFibreRelativePoint x y).1
    ((U.mem_completedIdempotentFibrePiece_iff_ambient basis e x y).mp hy)
    (fcRelativeFibrePoint_base x.1 y)

/-- Equality of the LITERAL original weighted norm at a real upper bound forces
EVERY original selected value over that point to reach that bound. -/
theorem eq_of_curveRelativePieceNorm_eq_const
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : RelativeSpectrum w B → EReal) (R : ℝ)
    (hu : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, u y ≤ (R : EReal))
    (x : U.carrier)
    (hF : U.curveRelativePieceNorm basis he u x.1 =
      (((U.curveIdempotentPieceWeight basis e x : ℝ)*R : ℝ) : EReal))
    (y : RelativeSpectrum w B) (hy : y ∈ U.curveIdempotentAmbientPiece basis e)
    (hyx : comap (IsScalarTower.toAlgHom K K[X] B) y = x.1) : u y = (R : EReal) := by
  let := Module.Finite.of_basis basis
  let S := Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x)
  have hmem (z) (hz : z ∈ S) := (U.mem_completedIdempotentFibrePiece_iff_ambient basis e x z).mp hz
  rw [U.curveRelativePieceNorm_apply basis he u x] at hF
  have hsum : ∑ z ∈ S, ((Spectrum.fibreNormMult K[X] z.1 : ℝ) : EReal)*u (U.curveFibreRelativePoint x z).1 =
      ((((∑ z ∈ S, (Spectrum.fibreNormMult K[X] z.1 : ℝ))*R : ℝ)) : EReal) := by
    simpa only [curveIdempotentPieceWeight,Nat.cast_sum,S] using hF
  have hall := eq_of_finite_positive_weighted_sum_eq_max S
    (fun z => (Spectrum.fibreNormMult K[X] z.1 : ℝ))
    (fun z _ => Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (Spectrum.one_le_fibreNormMult (B := K[X]) z.1)))
    (fun z => u (U.curveFibreRelativePoint x z).1) R
    (fun z hz => hu _ (hmem z hz)) hsum
  let z : Spectrum.Fibre (B := B) x.1.1 := ⟨y.1,congrArg Subtype.val hyx⟩
  have hzy : (U.curveFibreRelativePoint x z).1 = y := Subtype.ext rfl
  have hz : z ∈ S := (U.mem_completedIdempotentFibrePiece_iff_ambient basis e x z).mpr (hzy.symm ▸ hy)
  simpa only [hzy] using hall z hz

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
