import EnvelopeProperty.Potential.LineAffinoidUnions
import EnvelopeProperty.Potential.LineHoleRouting

/-! # Every active ORIGINAL union-hole index is retained exactly -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)

/-- All ORIGINAL missing union-hole sets are already pairwise disjoint, including inactive zero-radius entries. -/
theorem unionHole_family_disjoint : Pairwise fun i j : Fin n ⊕ (Fin m × Fin n) =>
    Disjoint (fcOpenLinearDisc (w := w) (U.unionHoleCenter V i) (U.unionHoleRadius V i))
      (fcOpenLinearDisc (U.unionHoleCenter V j) (U.unionHoleRadius V j)) := by
  classical
  have hout (j : Fin n) :
      Disjoint (fcOpenLinearDisc (w := w) (U.unionHoleCenter V (Sum.inl j)) (U.unionHoleRadius V (Sum.inl j)))
        U.outerClosedDisc := by
    by_cases hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc
    · rwa [U.unionHole_inl_eq_of_disjoint V j hd]
    · rw [U.unionHole_inl_eq_of_not_disjoint V j hd]
      simp
  have hsub (j : Fin n) :
      fcOpenLinearDisc (w := w) (U.unionHoleCenter V (Sum.inl j)) (U.unionHoleRadius V (Sum.inl j)) ⊆
        V.holeOpenDisc j := by
    by_cases hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc
    · rw [U.unionHole_inl_eq_of_disjoint V j hd]
    · rw [U.unionHole_inl_eq_of_not_disjoint V j hd]
      exact Set.empty_subset _
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact (V.holes_disjoint (fun he => hij (congrArg Sum.inl he))).mono (hsub i) (hsub j)
    | inr p =>
      rw [U.unionHole_inr_eq V p.1 p.2]
      exact (hout i).mono_right (Set.inter_subset_left.trans (U.holeOpenDisc_subset_outerClosedDisc p.1))
  | inr p =>
    cases j with
    | inl j =>
      rw [U.unionHole_inr_eq V p.1 p.2]
      exact ((hout j).mono_right (Set.inter_subset_left.trans (U.holeOpenDisc_subset_outerClosedDisc p.1))).symm
    | inr q =>
      rw [U.unionHole_inr_eq V p.1 p.2,U.unionHole_inr_eq V q.1 q.2]
      by_cases hU : p.1 = q.1
      · have hV : p.2 ≠ q.2 := fun he => hij (congrArg Sum.inr (Prod.ext hU he))
        exact (V.holes_disjoint hV).mono Set.inter_subset_right Set.inter_subset_right
      · exact (U.holes_disjoint hU).mono Set.inter_subset_left Set.inter_subset_left

/-- Exact union normalization retains EVERY active ORIGINAL outside/intersection index, uniquely. -/
theorem exists_union_with_all_active_holes (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (B : FCStandardAffinoid w q) (s : Fin q → Fin n ⊕ (Fin m × Fin n)),
      B.center = V.center ∧ B.radius = V.radius ∧ Function.Injective s ∧
      (∀ j, B.holeCenter j = U.unionHoleCenter V (s j) ∧ B.holeRadius j = U.unionHoleRadius V (s j)) ∧
      B.carrier = U.carrier ∪ V.carrier ∧
      ∀ i, 0 < U.unionHoleRadius V i → ∃! j, s j = i := by
  classical
  obtain ⟨q,B,s,hc,hr,hi,hh,hB⟩ := U.exists_union_of_radius_le V hR x hxU hxV
  refine ⟨q,B,s,hc,hr,hi,hh,hB,fun i hip => ?_⟩
  have hcenter : w (U.unionHoleCenter V i-B.center) ≤ B.radius := by
    rw [hc,hr]
    rcases U.unionHole_active_original V i hip with ⟨j,hj,_⟩ | ⟨j,hj,_⟩
    · rw [hj]
      have hUV : w (U.center-V.center) ≤ V.radius :=
        (fc_center_distance_bound x U.center V.center).trans (max_le (hxU.1.trans hR) hxV.1)
      have hsum : U.holeCenter j-V.center = (U.holeCenter j-U.center)+(U.center-V.center) := by ring
      rw [hsum]
      exact (w.map_add _ _).trans (max_le ((U.holeCenter_le j).trans hR) hUV)
    · rw [hj]
      exact V.holeCenter_le j
  have hbound : ∀ y ∈ B.carrier, U.unionHoleRadius V i ≤ val y (X-C (U.unionHoleCenter V i)) := by
    intro y hy
    have hdomain := U.union_hole_domain_eq V hR x hxU hxV
    have hy' : y ∈ {z | z ∈ V.outerClosedDisc ∧ ∀ k, z ∉ fcOpenLinearDisc (w := w)
        (U.unionHoleCenter V k) (U.unionHoleRadius V k)} := by
      rw [hdomain,← hB]
      exact hy
    exact le_of_not_gt (hy'.2 i)
  obtain ⟨j,_,_,hsub⟩ := B.exists_hole_containing_open_disc _ _ hip hcenter hbound
  have hji : s j = i := by
    by_contra hne
    have hd := U.unionHole_family_disjoint V hne
    let z := centeredGauss (self w) (U.unionHoleCenter V i) 0
    have hz : z ∈ fcOpenLinearDisc (w := w) (U.unionHoleCenter V i) (U.unionHoleRadius V i) := by
      simpa only [z,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self]
        using hip
    have hzj := hsub hz
    rw [(hh j).1,(hh j).2] at hzj
    exact Set.disjoint_left.mp hd hzj hz
  exact ⟨j,hji,fun k hk => hi (hk.trans hji.symm)⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
