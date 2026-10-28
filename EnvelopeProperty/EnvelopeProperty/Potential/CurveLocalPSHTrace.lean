import EnvelopeProperty.Potential.CurveConvexPLTrace

/-! # Genuine original local decreasing convex PL functions derive every actual piece trace -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

private theorem fc_trace_subharmonic_finset_sum {J : Type*}
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

/-- The ORIGINAL whole decreasing convex-PL sequence class derives actual source
comparison traces, with no uniform denominator or neighbourhood across terms. -/
theorem isLineSubharmonicOn_curveRelativePieceNorm_of_isDecrConvexPLLimitOn
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsDecrConvexPLLimitOn Ω u) (hnt : ∃ t : K, 1 < w t)
    (hU : U.curveIdempotentAmbientPiece basis e ⊆ Ω) :
    IsLineSubharmonicOn (U.curveRelativePieceNorm basis he u) (interior U.carrier) := by
  obtain ⟨v,hv,hanti,hlim⟩ := hu
  have hut : ∀ y ∈ U.curveIdempotentAmbientPiece basis e, ∀ j, v j y ≠ ⊤ := by
    intro y hy j
    obtain ⟨W,hW,hyW,hWΩ,n,a,s,hs,ha,hform⟩ := hv j y (hU hy)
    rw [hform y hyW]
    exact EReal.coe_ne_top _
  have hsh := U.isLineSubharmonicOn_curveRelativePieceNorm_iInf basis he v
    (fun y hy => hanti y (hU hy)) hut
    (fun j => U.isLineSubharmonicOn_curveRelativePieceNorm_of_isConvexPLOn basis he (hv j) hnt hU)
  apply hsh.congr
  intro x hx
  exact U.curveRelativePieceNorm_congr basis he _ u
    (fun y hy => (hlim y (hU hy)).symm) ⟨x,interior_subset hx⟩

/-- The repository's ORIGINAL intrinsic locally-psh class DERIVES every actual
piece trace comparison, by genuine finite refinement and source line locality. -/
theorem isLineSubharmonicOn_curveRelativePieceNorm_of_isLocallyPSHOn
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsLocallyPSHOn Ω u) (hnt : ∃ t : K, 1 < w t)
    (hU : U.curveIdempotentAmbientPiece basis e ⊆ Ω) :
    IsLineSubharmonicOn (U.curveRelativePieceNorm basis he u) (interior U.carrier) := by
  classical
  apply isLineSubharmonicOn_of_locally hnt
  intro x hx
  let I := U.CurveCentralPiece basis e x
  let : Finite I := U.finite_curveCentralPiece basis e x
  let : Fintype I := Fintype.ofFinite I
  have hdata (i : I) := hu i.1 (hU i.2.1)
  choose W hWo hiW hWΩ hw using hdata
  obtain ⟨l,V,hxV,hVU,part,hpart,hpartW,hcover,hdisj⟩ :=
    U.exists_standardAffinoid_piece_refinement basis he x hx W (fun i => (hWo i).mem_nhds (hiW i))
  have hshi (i : I) : IsLineSubharmonicOn (V.curveRelativePieceNorm basis (hpart i) u)
      (interior V.carrier) :=
    V.isLineSubharmonicOn_curveRelativePieceNorm_of_isDecrConvexPLLimitOn basis (hpart i)
      (hw i) hnt (hpartW i).1
  have hsum : IsLineSubharmonicOn (fun z => ∑ i : I, V.curveRelativePieceNorm basis (hpart i) u z)
      (interior V.carrier) :=
    fc_trace_subharmonic_finset_sum Finset.univ _ _ (fun i _ => hshi i)
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
