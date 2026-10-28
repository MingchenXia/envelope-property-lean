import EnvelopeProperty.Potential.LineComponentGrouping
import EnvelopeProperty.Potential.LineOpenHoleContainment
import EnvelopeProperty.Potential.LineAffinoidUnions

/-! # Surviving ORIGINAL boundaries isolate WHOLE original completed components -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
section Geometry
variable {F : Type*} [Field F] {w : Valuation F ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (W : FCStandardAffinoid w n) (hWU : W.carrier ⊆ U.carrier)

/-- A surviving ORIGINAL source boundary derives a target ORIGINAL hole with the SAME actual open carrier and original radius. -/
theorem exists_same_open_hole_of_boundary_mem (i : Fin m)
    (hboundary : centeredGauss (self w) (U.holeCenter i) (U.holeRadius i) ∈ W.carrier) :
    ∃ k : Fin n, W.restrictionHoleIndex U hWU i = some k ∧
      W.holeRadius k = U.holeRadius i ∧ W.holeOpenDisc k = U.holeOpenDisc i := by
  have hout := hboundary.1
  rw [fc_centeredGauss_val_X_sub_C] at hout
  have hbound : ∀ y ∈ W.carrier, U.holeRadius i ≤ val y (X-C (U.holeCenter i)) :=
    fun y hy => (hWU hy).2 i
  obtain ⟨k,hr,hc,hsub⟩ := W.exists_hole_containing_open_disc _ _ (U.holeRadius_pos i)
    (max_le_iff.mp hout).1 hbound
  have hrad : W.holeRadius k = U.holeRadius i := by
    apply le_antisymm _ hr
    apply le_of_not_gt
    intro hlt
    have h := hboundary.2 k
    rw [fc_centeredGauss_val_X_sub_C] at h
    exact not_lt_of_ge h (max_lt hc hlt)
  have hrev : W.holeOpenDisc k ⊆ U.holeOpenDisc i := by
    apply (fc_openLinearDisc_subset_iff _ _ _ _ (W.holeRadius_pos k)).mpr
    have hs : w (W.holeCenter k-U.holeCenter i) = w (U.holeCenter i-W.holeCenter k) := by
      rw [show W.holeCenter k-U.holeCenter i = -(U.holeCenter i-W.holeCenter k) by ring,Valuation.map_neg]
    exact ⟨hrad.le,by rwa [hs,← hrad]⟩
  exact ⟨k,(W.restrictionHoleIndex_eq_some_iff U hWU i k).mpr hsub,hrad,Set.Subset.antisymm hrev hsub⟩
end Geometry

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n) (hWU : W.carrier ⊆ U.carrier)

/-- An ACTUAL surviving ORIGINAL boundary constructs the ORIGINAL target index that isolates that WHOLE source component for EVERY completed function. -/
theorem exists_restricted_principal_detector_of_boundary_mem (i : Fin m)
    (hboundary : U.holeBoundaryPoint i ∈ W.carrier) :
    ∃ k : Fin n, W.restrictionHoleIndex U hWU i = some k ∧
      W.holeOpenDisc k = U.holeOpenDisc i ∧ ∀ f : U.AnalyticFunctions,
      W.analyticComponent (some k) (U.analyticRestriction W hWU f) =
        U.analyticRestriction W hWU (U.analyticComponent (some i) f) := by
  classical
  obtain ⟨k,hki,_,he⟩ := U.exists_same_open_hole_of_boundary_mem W hWU i hboundary
  have honly (j : Fin m) (hj : W.restrictionHoleIndex U hWU j = some k) : j = i := by
    have hsub := (W.restrictionHoleIndex_eq_some_iff U hWU j k).mp hj
    change U.holeOpenDisc j ⊆ W.holeOpenDisc k at hsub
    rw [he] at hsub
    by_contra hne
    have hz : centeredGauss (self (NormedField.valuation (K := K))) (U.holeCenter j) 0 ∈ U.holeOpenDisc j := by
      simpa only [holeOpenDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self]
        using U.holeRadius_pos j
    exact Set.disjoint_left.mp (U.holes_disjoint hne) hz (hsub hz)
  refine ⟨k,hki,he,fun f => ?_⟩
  rw [U.analyticComponent_analyticRestriction_grouped W hWU]
  simp only [Option.some_ne_none,if_false,zero_add]
  rw [Finset.sum_eq_single i]
  · rw [if_pos hki.symm]
  · intro j _ hji
    exact if_neg (fun h => hji (honly j h.symm))
  · simp
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
