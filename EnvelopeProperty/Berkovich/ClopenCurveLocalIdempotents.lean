/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.CurveIdempotentFaithfulness
import EnvelopeProperty.Potential.CurvePieceRefinement

/-! # Actual clopen curve subsets have unique whole local analytic idempotents -/

open scoped NNReal Polynomial Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- Every ACTUAL original clopen subset is represented exactly by a UNIQUE whole analytic
idempotent over a constructed standard-affinoid neighbourhood inside ANY prescribed one. -/
theorem exists_standardAffinoid_unique_idempotent_of_isClopen
    (basis : Module.Basis ι K[X] B) (C : Set (RelativeSpectrum w B)) (hC : IsClopen C)
    (x : RelativeSpectrum w K[X]) (N : Set (RelativeSpectrum w K[X])) (hN : N ∈ 𝓝 x) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m,
      x ∈ interior U.carrier ∧ U.carrier ⊆ N ∧
        ∃! e : U.CurveAnalyticAlgebra basis,
          IsIdempotentElem e ∧ U.curveIdempotentAmbientPiece basis e =
            C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier := by
  let := Module.Finite.of_basis basis
  let φ := IsScalarTower.toAlgHom K K[X] B
  let P := C ∩ comap φ ⁻¹' {x}
  obtain ⟨m,V,hxV,a,ha,hcentral⟩ :=
    exists_standardAffinoid_analytic_central_piece x basis P Set.inter_subset_right
  let p : V.CurvePreimage (B := B) → RelativeSpectrum w K[X] := fun y => comap φ y.1
  have hp : IsClosedMap p :=
    (isClosedMap_comap_of_isIntegral φ (RingHom.finite_algebraMap.mpr inferInstance).to_isIntegral).domRestrict
      (V.isClosed_carrier.preimage (continuous_comap φ))
  let D := (Subtype.val : V.CurvePreimage (B := B) → RelativeSpectrum w B) ⁻¹' C
  have hD : IsClopen D := hC.preimage continuous_subtype_val
  have hnear := EnvelopeProperty.eventually_clopen_fibre_eq_of_central p hp
    (V.curveIdempotentOriginalPiece basis a) D
    (V.isClopen_curveIdempotentOriginalPiece basis ha) hD x (by
      intro y hy
      rw [← V.mem_curveIdempotentAmbientPiece_iff basis a y.1 y.2]
      change (y.1 ∈ V.curveIdempotentAmbientPiece basis a) ↔ y.1 ∈ C
      have hh := Set.ext_iff.mp hcentral y.1
      change (y.1 ∈ V.curveIdempotentAmbientPiece basis a ∧ p y = x) ↔
        (y.1 ∈ C ∧ p y = x) at hh
      simpa only [hy, and_true] using hh)
  obtain ⟨n,U,hxU,hU⟩ := fc_exists_standardAffinoid_nhds x
    (Filter.inter_mem hnear (Filter.inter_mem (isOpen_interior.mem_nhds hxV) hN))
  let hUV : U.carrier ⊆ V.carrier := fun y hy => interior_subset (hU hy).2.1
  let e := V.curveAnalyticNormedRestriction U hUV basis a
  have he : IsIdempotentElem e := ha.map _
  have heq : U.curveIdempotentAmbientPiece basis e = C ∩ comap φ ⁻¹' U.carrier := by
    rw [show e = V.curveAnalyticNormedRestriction U hUV basis a from rfl,
      V.curveIdempotentAmbientPiece_restriction U hUV basis a]
    ext y
    constructor
    · rintro ⟨hyV,hyU⟩
      have hyV' := (V.mem_curveIdempotentAmbientPiece_iff basis a y (hUV hyU)).mp hyV
      exact ⟨((hU hyU).1 ⟨y,hUV hyU⟩ rfl).mp hyV',hyU⟩
    · rintro ⟨hyC,hyU⟩
      exact ⟨(V.mem_curveIdempotentAmbientPiece_iff basis a y (hUV hyU)).mpr
        (((hU hyU).1 ⟨y,hUV hyU⟩ rfl).mpr hyC),hyU⟩
  refine ⟨n,U,hxU,fun y hy => (hU hy).2.2,e,⟨he,heq⟩,?_⟩
  intro f hf
  exact (U.curveIdempotentAmbientPiece_eq_iff basis hf.1 he).mpr (hf.2.trans heq.symm)

end EnvelopeProperty.Berkovich.RelativeSpectrum
