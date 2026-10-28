import EnvelopeProperty.Berkovich.ClopenCurveLocalIdempotents
import EnvelopeProperty.Berkovich.CurveFiniteCoverWholeGluing
import EnvelopeProperty.Potential.LineAffinoidIntersections

/-! # Unique whole analytic idempotents from original global curve clopens -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
  [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]

private theorem specialization_eq_of_same_clopen_piece
    {m n : ℕ} (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)
    (basis : Module.Basis ι K[X] B) (C : Set (RelativeSpectrum w B))
    {e : U.CurveAnalyticAlgebra basis} {f : V.CurveAnalyticAlgebra basis}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (heC : U.curveIdempotentAmbientPiece basis e =
      C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier)
    (hfC : V.curveIdempotentAmbientPiece basis f =
      C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' V.carrier)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    U.curveAnalyticNormedSpecialization basis ⟨x, hxU⟩ e =
      V.curveAnalyticNormedSpecialization basis ⟨x, hxV⟩ f := by
  obtain ⟨q, W, hW⟩ := U.exists_intersection_of_nonempty V ⟨x, hxU, hxV⟩
  have hWU : W.carrier ⊆ U.carrier := fun _ hz => (hW ▸ hz).1
  have hWV : W.carrier ⊆ V.carrier := fun _ hz => (hW ▸ hz).2
  have hxe : x ∈ W.carrier := hW.symm ▸ ⟨hxU, hxV⟩
  have hr : U.curveAnalyticNormedRestriction W hWU basis e =
      V.curveAnalyticNormedRestriction W hWV basis f := by
    apply (W.curveIdempotentAmbientPiece_eq_iff basis (he.map _) (hf.map _)).mpr
    rw [U.curveIdempotentAmbientPiece_restriction W hWU basis e,
      V.curveIdempotentAmbientPiece_restriction W hWV basis f, heC, hfC]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hyC, hyU⟩, hyW⟩
      exact ⟨⟨hyC, hWV hyW⟩, hyW⟩
    · rintro ⟨⟨hyC, hyV⟩, hyW⟩
      exact ⟨⟨hyC, hWU hyW⟩, hyW⟩
  have hh := congrArg (W.curveAnalyticNormedSpecialization basis ⟨x, hxe⟩) hr
  rw [U.curveAnalyticNormedRestriction_specialization W hWU basis,
    V.curveAnalyticNormedRestriction_specialization W hWV basis] at hh
  exact hh

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
  {m : ℕ} (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

/-- Every original global clopen produces a unique genuine idempotent on the
whole affinoid curve algebra, including the original base boundary. -/
theorem existsUnique_idempotent_of_global_isClopen (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    ∃! e : U.CurveAnalyticAlgebra basis, IsIdempotentElem e ∧
      U.curveIdempotentAmbientPiece basis e =
        C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier := by
  classical
  have hl (x : U.carrier) : ∃ (q : ℕ)
      (A : FCStandardAffinoid (NormedField.valuation (K := K)) q)
      (e : A.CurveAnalyticAlgebra basis),
      x.1 ∈ interior A.carrier ∧ IsIdempotentElem e ∧
        A.curveIdempotentAmbientPiece basis e =
          C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' A.carrier := by
    obtain ⟨q, A, hxA, _, e, he, _⟩ :=
      exists_standardAffinoid_unique_idempotent_of_isClopen basis C hC x.1
        Set.univ Filter.univ_mem
    exact ⟨q, A, e, hxA, he.1, he.2⟩
  choose q A e hxA he heC using hl
  obtain ⟨s, hs⟩ := U.isCompact_carrier.elim_finite_subcover
    (fun x : U.carrier => interior (A x).carrier) (fun _ => isOpen_interior) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩)
  let J := {x : U.carrier // x ∈ s}
  have hi (j : J) : (U.carrier ∩ (A j.1).carrier).Nonempty :=
    ⟨j.1.1, j.1.2, interior_subset (hxA j.1)⟩
  choose n V hV using fun j : J => U.exists_intersection_of_nonempty (A j.1) (hi j)
  have hVU (j : J) : (V j).carrier ⊆ U.carrier := fun _ hz => (hV j ▸ hz).1
  have hVA (j : J) : (V j).carrier ⊆ (A j.1).carrier := fun _ hz => (hV j ▸ hz).2
  have hcover : ∀ x ∈ U.carrier, ∃ j : J, x ∈ (V j).carrier := by
    intro x hx
    obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨⟨i, his⟩, ?_⟩
    rw [hV]
    exact ⟨hx, interior_subset hxi⟩
  let f (j : J) : (V j).CurveAnalyticAlgebra basis :=
    (A j.1).curveAnalyticNormedRestriction (V j) (hVA j) basis (e j.1)
  have hf (j : J) : IsIdempotentElem (f j) := (he j.1).map _
  have hfC (j : J) : (V j).curveIdempotentAmbientPiece basis (f j) =
      C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' (V j).carrier := by
    rw [(A j.1).curveIdempotentAmbientPiece_restriction (V j) (hVA j) basis (e j.1), heC]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hVA j h.2⟩, h.2⟩⟩
  have hcompat : ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
      (V i).curveAnalyticNormedSpecialization basis ⟨x, hi⟩ (f i) =
        (V j).curveAnalyticNormedSpecialization basis ⟨x, hj⟩ (f j) := by
    intro i j x hi hj
    exact specialization_eq_of_same_clopen_piece (V i) (V j) basis C
      (hf i) (hf j) (hfC i) (hfC j) x hi hj
  let F : curveAnalyticCompatibleFamilies V basis := ⟨f, hcompat⟩
  let E := U.curveAnalyticCoverRestrictionEquiv V hVU hcover basis
  let g := E.symm F
  have hg (j : J) : U.curveAnalyticNormedRestriction (V j) (hVU j) basis g = f j :=
    congrArg (fun t : curveAnalyticCompatibleFamilies V basis => t.1 j) (E.apply_symm_apply F)
  have hgid : IsIdempotentElem g := by
    change g * g = g
    apply E.injective
    rw [map_mul, E.apply_symm_apply]
    apply Subtype.ext
    funext j
    exact hf j
  have hgC : U.curveIdempotentAmbientPiece basis g =
      C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier := by
    ext y
    constructor
    · intro hy
      have hyU := U.curveIdempotentAmbientPiece_subset basis g hy
      obtain ⟨j, hyj⟩ := hcover _ hyU
      have hyr : y ∈ (V j).curveIdempotentAmbientPiece basis (f j) := by
        rw [← hg j, U.curveIdempotentAmbientPiece_restriction]
        exact ⟨hy, hyj⟩
      exact ⟨(hfC j ▸ hyr).1, hyU⟩
    · rintro ⟨hyC, hyU⟩
      obtain ⟨j, hyj⟩ := hcover _ hyU
      have hyr : y ∈ (V j).curveIdempotentAmbientPiece basis (f j) := hfC j ▸ ⟨hyC, hyj⟩
      rw [← hg j, U.curveIdempotentAmbientPiece_restriction] at hyr
      exact hyr.1
  refine ⟨g, ⟨hgid, hgC⟩, ?_⟩
  intro a ha
  exact (U.curveIdempotentAmbientPiece_eq_iff basis ha.1 hgid).mpr (ha.2.trans hgC.symm)

/-- The unique whole analytic idempotent belonging to an original global clopen. -/
def globalClopenIdempotent (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    U.CurveAnalyticAlgebra basis :=
  (U.existsUnique_idempotent_of_global_isClopen basis C hC).exists.choose

/-- Actual idempotence is derived from the constructed whole original glue. -/
theorem isIdempotent_globalClopenIdempotent (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    IsIdempotentElem (U.globalClopenIdempotent basis C hC) :=
  (U.existsUnique_idempotent_of_global_isClopen basis C hC).exists.choose_spec.1

/-- The constructed whole idempotent retains the exact original global clopen. -/
theorem ambientPiece_globalClopenIdempotent (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    U.curveIdempotentAmbientPiece basis (U.globalClopenIdempotent basis C hC) =
      C ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier :=
  (U.existsUnique_idempotent_of_global_isClopen basis C hC).exists.choose_spec.2

/-- The same constructed whole clopen idempotents agree under every actual
carrier restriction; boundary coincidences and radius-zero discs are included. -/
theorem restriction_globalClopenIdempotent {n : ℕ}
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (hVU : V.carrier ⊆ U.carrier) (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    U.curveAnalyticNormedRestriction V hVU basis (U.globalClopenIdempotent basis C hC) =
      V.globalClopenIdempotent basis C hC := by
  apply (U.curveAnalyticNormedRestriction_eq_iff_piece_eq V hVU basis
    (U.isIdempotent_globalClopenIdempotent basis C hC)
    (V.isIdempotent_globalClopenIdempotent basis C hC)).mpr
  rw [U.ambientPiece_globalClopenIdempotent, V.ambientPiece_globalClopenIdempotent]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hVU h.2⟩, h.2⟩⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
