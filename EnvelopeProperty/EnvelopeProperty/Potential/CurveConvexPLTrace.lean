import EnvelopeProperty.Potential.CurveTropAffineFubiniStudy
import EnvelopeProperty.Potential.CurvePieceAllPointUnits
import EnvelopeProperty.Potential.CurveRelativePieceNorm
import EnvelopeProperty.Potential.LineSubharmonicSums
import EnvelopeProperty.Potential.LineSubharmonicLocality

/-! # Actual varying local convex PL presentations give genuine original piece traces -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

private theorem fc_subharmonic_finset_sum {J : Type*}
    (s : Finset J) (f : J → RelativeSpectrum w K[X] → EReal)
    (Ω : Set (RelativeSpectrum w K[X])) (hf : ∀ j ∈ s, IsLineSubharmonicOn (f j) Ω) :
    IsLineSubharmonicOn (fun x => ∑ j ∈ s, f j x) Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,EReal.coe_zero] using IsLineSubharmonicOn.const 0 Ω
  | insert j s hj ih =>
    have hfj := hf j (Finset.mem_insert_self j s)
    have hfs := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hj] using hfj.add hfs

namespace FCStandardAffinoid
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι] {m : ℕ}
variable (U : FCStandardAffinoid w m) (basis : Module.Basis ι K[X] B)

/-- The actual original varying local rational convex-PL class DERIVES every source
comparison of the literal trace over ANY genuine entire analytic piece in its domain. -/
theorem isLineSubharmonicOn_curveRelativePieceNorm_of_isConvexPLOn
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsConvexPLOn Ω u) (hnt : ∃ t : K, 1 < w t)
    (hU : U.curveIdempotentAmbientPiece basis e ⊆ Ω) :
    IsLineSubharmonicOn (U.curveRelativePieceNorm basis he u) (interior U.carrier) := by
  classical
  apply isLineSubharmonicOn_of_locally hnt
  intro x hx
  let I := U.CurveCentralPiece basis e x
  let : Finite I := U.finite_curveCentralPiece basis e x
  let : Fintype I := Fintype.ofFinite I
  have hdata (i : I) := hu i.1 (hU i.2.1)
  choose W hWo hiW hWΩ n coeff s hs hanz hform using hdata
  obtain ⟨l,V,hxV,hVU,part,hpart,hpartW,hcover,hdisj⟩ :=
    U.exists_standardAffinoid_piece_refinement basis he x hx W (fun i => (hWo i).mem_nhds (hiW i))
  choose N hN b weight hrepresentation using
    fun i : I => exists_tropAffine_localizedFubiniStudy (v := w) (coeff i) (s i) (hs i)
  have hg (i : I) : IsUnit (V.curveIdempotentQuotientMap basis (part i) (∏ j, coeff i j)) := by
    apply V.isUnit_curveIdempotentQuotientMap_of_nonvanishing basis (hpart i)
    intro y hy
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hanz i y ((hpartW i).1 hy) j)
  have hshi (i : I) : IsLineSubharmonicOn (V.curveRelativePieceNorm basis (hpart i) u)
      (interior V.carrier) := by
    have hNi : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
    apply (V.isLineSubharmonicOn_curvePieceNorm_localizedFubiniStudy basis (hpart i)
      (∏ j, coeff i j) (hg i) (b i) (weight i) (N i : ℝ) hNi).congr
    intro z hz
    apply Eq.symm
    apply V.curveRelativePieceNorm_eq_pieceNorm_of_eq_on_piece basis (hpart i) u _ _
      ⟨z,interior_subset hz⟩
    intro y hy
    have hyW := (hpartW i).1 hy
    have hyprod : y.1.val (∏ j, coeff i j) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => hanz i y hyW j)
    exact (hform i y hyW).trans (hrepresentation i y hyprod).symm
  have hsum : IsLineSubharmonicOn (fun z => ∑ i : I, V.curveRelativePieceNorm basis (hpart i) u z)
      (interior V.carrier) :=
    fc_subharmonic_finset_sum Finset.univ _ _ (fun i _ => hshi i)
  refine ⟨interior V.carrier,isOpen_interior,hxV,interior_mono hVU,?_⟩
  apply hsum.congr
  intro z hz
  calc
    (∑ i : I, V.curveRelativePieceNorm basis (hpart i) u z) =
        V.curveRelativePieceNorm basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) u z :=
      (V.curveRelativePieceNorm_partition basis _ part hpart hcover hdisj u
        ⟨z,interior_subset hz⟩).symm
    _ = U.curveRelativePieceNorm basis he u z :=
      U.curveRelativePieceNorm_restriction basis V hVU he u ⟨z,interior_subset hz⟩

end FCStandardAffinoid
end EnvelopeProperty.Berkovich.RelativeSpectrum
