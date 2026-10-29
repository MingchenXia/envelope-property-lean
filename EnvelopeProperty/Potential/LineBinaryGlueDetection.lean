import EnvelopeProperty.Potential.LineComponentGrouping
import EnvelopeProperty.Potential.LineComponentLifts
import EnvelopeProperty.Potential.LinePrincipalBoundaryDetection
import EnvelopeProperty.Potential.LineAffinoidUnions
import EnvelopeProperty.Potential.LineCoverUniqueness
import EnvelopeProperty.Potential.LineRestrictionBoundaryComponents
import EnvelopeProperty.Potential.LineIntersectionBoundaries

/-! # Actual minimal union components detect a WHOLE compatible pair -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

private theorem hole_index_eq_of_subset {F : Type*} [Field F] {w : Valuation F ℝ≥0} {t : ℕ}
    (A : FCStandardAffinoid w t) (i j : Fin t) (hsub : A.holeOpenDisc i ⊆ A.holeOpenDisc j) : i = j := by
  by_contra hne
  have hz : centeredGauss (self w) (A.holeCenter i) 0 ∈ A.holeOpenDisc i := by
    simpa only [holeOpenDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self]
      using A.holeRadius_pos i
  exact Set.disjoint_left.mp (A.holes_disjoint hne) hz (hsub hz)

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n q : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
variable (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)

private theorem restricted_principal_single
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q) (hWU : W.carrier ⊆ U.carrier)
    (i : Fin m) (k : Fin q) (hki : W.restrictionHoleIndex U hWU i = some k)
    (honly : ∀ j, W.restrictionHoleIndex U hWU j = some k → j = i) (f : U.AnalyticFunctions) :
    W.analyticComponent (some k) (U.analyticRestriction W hWU f) =
      U.analyticRestriction W hWU (U.analyticComponent (some i) f) := by
  classical
  rw [U.analyticComponent_analyticRestriction_grouped W hWU]
  simp only [Option.some_ne_none,if_false,zero_add]
  rw [Finset.sum_eq_single i]
  · rw [if_pos hki.symm]
  · intro j _ hji
    exact if_neg (fun h => hji (honly j h.symm))
  · simp

private theorem restricted_principal_zero
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q) (hWU : W.carrier ⊆ U.carrier)
    (k : Fin q) (f : U.AnalyticFunctions)
    (hz : ∀ i, W.restrictionHoleIndex U hWU i = some k → U.analyticComponent (some i) f = 0) :
    W.analyticComponent (some k) (U.analyticRestriction W hWU f) = 0 := by
  classical
  rw [U.analyticComponent_analyticRestriction_grouped W hWU]
  simp only [Option.some_ne_none,if_false,zero_add]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · rw [hz i h.symm,map_zero]
  · rfl

/-- Actual original minimal union-component zero tests detect BOTH WHOLE compatible completed functions; no gluing certificate is assumed. -/
private theorem compatible_pair_eq_zero_of_all_union_components_zero (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum (NormedField.valuation (K := K)) K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier)
    (u : U.AnalyticFunctions) (v : V.AnalyticFunctions)
    (hcompat : ∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
      U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v)
    (hPv : V.analyticComponent none v = 0)
    (hUzero : ∀ i, (∃ j, U.holeOpenDisc i ⊆ V.holeOpenDisc j) → U.analyticComponent (some i) u = 0)
    (hVzero : ∀ j, (Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨
      ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i) → V.analyticComponent (some j) v = 0) :
    u = 0 ∧ v = 0 := by
  classical
  obtain ⟨q,W,s,hc,hr,_,hh,hW⟩ := U.exists_intersection_of_radius_le V hR x hxU hxV
  have hWU : W.carrier ⊆ U.carrier := by rw [hW]; exact Set.inter_subset_left
  have hWV : W.carrier ⊆ V.carrier := by rw [hW]; exact Set.inter_subset_right
  have hcomp : U.analyticRestriction W hWU u = V.analyticRestriction W hWV v := by
    apply W.analyticFunctions_eq_of_evaluation_eq
    intro z
    rw [U.analyticRestriction_evaluation,V.analyticRestriction_evaluation]
    exact hcompat z.1 (hWU z.2) (hWV z.2)
  have hUall (i : Fin m) : U.analyticComponent (some i) u = 0 := by
    by_cases hsmall : ∃ j, U.holeOpenDisc i ⊆ V.holeOpenDisc j
    · exact hUzero i hsmall
    have hcenter : NormedField.valuation (U.holeCenter i-W.center) ≤ W.radius := by
      rw [hc,hr]
      exact U.holeCenter_le i
    have hbound : ∀ y ∈ W.carrier, U.holeRadius i ≤ val y (X-C (U.holeCenter i)) :=
      fun y hy => (hWU hy).2 i
    obtain ⟨k,_,_,hsub⟩ := W.exists_hole_containing_open_disc _ _ (U.holeRadius_pos i) hcenter hbound
    have heq : W.holeCenter k = U.holeCenter i ∧ W.holeRadius k = U.holeRadius i := by
      have hh' := hh k
      cases hs : s k with
      | inl i' =>
        have hc' : W.holeCenter k = U.holeCenter i' := by simpa only [hs,combinedHoleCenter,Sum.elim_inl] using hh'.1
        have hr' : W.holeRadius k = U.holeRadius i' := by simpa only [hs,combinedHoleRadius,Sum.elim_inl] using hh'.2
        have hsub' : U.holeOpenDisc i ⊆ U.holeOpenDisc i' := by simpa only [hc',hr',holeOpenDisc] using hsub
        have hi := hole_index_eq_of_subset U i i' hsub'
        exact hi ▸ ⟨hc',hr'⟩
      | inr j =>
        have hc' : W.holeCenter k = V.holeCenter j := by simpa only [hs,combinedHoleCenter,Sum.elim_inr] using hh'.1
        have hr' : W.holeRadius k = V.holeRadius j := by simpa only [hs,combinedHoleRadius,Sum.elim_inr] using hh'.2
        exact (hsmall ⟨j,by simpa only [hc',hr',holeOpenDisc] using hsub⟩).elim
    have hki : W.restrictionHoleIndex U hWU i = some k :=
      (W.restrictionHoleIndex_eq_some_iff U hWU i k).mpr hsub
    have honly (i' : Fin m) (hi' : W.restrictionHoleIndex U hWU i' = some k) : i' = i := by
      have h := (W.restrictionHoleIndex_eq_some_iff U hWU i' k).mp hi'
      apply hole_index_eq_of_subset U i' i
      simpa only [heq.1,heq.2,holeOpenDisc] using h
    have hleft := U.restricted_principal_single W hWU i k hki honly u
    have hright : W.analyticComponent (some k) (V.analyticRestriction W hWV v) = 0 := by
      apply V.restricted_principal_zero W hWV k v
      intro j hj
      apply hVzero j
      apply Or.inr
      refine ⟨i,?_⟩
      have h := (W.restrictionHoleIndex_eq_some_iff V hWV j k).mp hj
      simpa only [heq.1,heq.2,holeOpenDisc] using h
    have hzero : U.analyticRestriction W hWU (U.analyticComponent (some i) u) = 0 :=
      hleft.symm.trans ((congrArg (W.analyticComponent (some k)) hcomp).trans hright)
    have hboundary : U.holeBoundaryPoint i ∈ W.carrier := by
      have h := W.holeGauss_mem k
      simpa only [heq.1,heq.2,holeBoundaryPoint] using h
    exact U.principal_eq_zero_of_restriction_eq_zero W hWU i hboundary _
      (U.analyticComponent_mem_closure (some i) u) hzero
  have hVall (j : Fin n) : V.analyticComponent (some j) v = 0 := by
    by_cases hsmall : Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨ ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i
    · exact hVzero j hsmall
    have hinside : V.holeRadius j ≤ U.radius ∧ NormedField.valuation (V.holeCenter j-U.center) ≤ U.radius := by
      rcases fc_openLinearDisc_inside_or_disjoint U.center (V.holeCenter j) U.radius (V.holeRadius j)
        x hxU.1 (hxV.2 j) with h | h
      · exact ⟨h.1,h.2.1⟩
      · exact (hsmall (Or.inl h)).elim
    have hcenter : NormedField.valuation (V.holeCenter j-W.center) ≤ W.radius := by rw [hc,hr]; exact hinside.2
    have hbound : ∀ y ∈ W.carrier, V.holeRadius j ≤ val y (X-C (V.holeCenter j)) :=
      fun y hy => (hWV hy).2 j
    obtain ⟨k,_,_,hsub⟩ := W.exists_hole_containing_open_disc _ _ (V.holeRadius_pos j) hcenter hbound
    have heq : W.holeCenter k = V.holeCenter j ∧ W.holeRadius k = V.holeRadius j := by
      have hh' := hh k
      cases hs : s k with
      | inl i =>
        have hc' : W.holeCenter k = U.holeCenter i := by simpa only [hs,combinedHoleCenter,Sum.elim_inl] using hh'.1
        have hr' : W.holeRadius k = U.holeRadius i := by simpa only [hs,combinedHoleRadius,Sum.elim_inl] using hh'.2
        exact (hsmall (Or.inr ⟨i,by simpa only [hc',hr',holeOpenDisc] using hsub⟩)).elim
      | inr j' =>
        have hc' : W.holeCenter k = V.holeCenter j' := by simpa only [hs,combinedHoleCenter,Sum.elim_inr] using hh'.1
        have hr' : W.holeRadius k = V.holeRadius j' := by simpa only [hs,combinedHoleRadius,Sum.elim_inr] using hh'.2
        have hsub' : V.holeOpenDisc j ⊆ V.holeOpenDisc j' := by simpa only [hc',hr',holeOpenDisc] using hsub
        have hj := hole_index_eq_of_subset V j j' hsub'
        exact hj ▸ ⟨hc',hr'⟩
    have hkj : W.restrictionHoleIndex V hWV j = some k :=
      (W.restrictionHoleIndex_eq_some_iff V hWV j k).mpr hsub
    have honly (j' : Fin n) (hj' : W.restrictionHoleIndex V hWV j' = some k) : j' = j := by
      have h := (W.restrictionHoleIndex_eq_some_iff V hWV j' k).mp hj'
      apply hole_index_eq_of_subset V j' j
      simpa only [heq.1,heq.2,holeOpenDisc] using h
    have hright := V.restricted_principal_single W hWV j k hkj honly v
    have hleft : W.analyticComponent (some k) (U.analyticRestriction W hWU u) = 0 :=
      U.restricted_principal_zero W hWU k u (fun i _ => hUall i)
    have hzero : V.analyticRestriction W hWV (V.analyticComponent (some j) v) = 0 :=
      hright.symm.trans ((congrArg (W.analyticComponent (some k)) hcomp.symm).trans hleft)
    have hboundary : V.holeBoundaryPoint j ∈ W.carrier := by
      have h := W.holeGauss_mem k
      simpa only [heq.1,heq.2,holeBoundaryPoint] using h
    exact V.principal_eq_zero_of_restriction_eq_zero W hWV j hboundary _
      (V.analyticComponent_mem_closure (some j) v) hzero
  have hv : v = 0 := by simpa only [hPv,hVall,Finset.sum_const_zero,zero_add] using V.analyticComponent_sum v
  have huP : u = U.analyticComponent none u := by simpa only [hUall,Finset.sum_const_zero,add_zero] using U.analyticComponent_sum u
  have huclosure : u ∈ closure (U.rationalComponentSet none) := by
    rw [huP]
    exact U.analyticComponent_mem_closure none u
  have hnorm := U.nnnorm_restriction_polynomial_closure W hWU hc.symm hr.symm u huclosure
  rw [hv,map_zero] at hcomp
  rw [hcomp,nnnorm_zero] at hnorm
  exact ⟨nnnorm_eq_zero.mp hnorm.symm,hv⟩
/-- Actual ASYMMETRIC original union-component zero tests detect BOTH WHOLE compatible functions; equal-radius overlaps use the ORIGINAL U owner. -/
theorem compatible_pair_eq_zero_of_union_components_zero (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum (NormedField.valuation (K := K)) K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier)
    (u : U.AnalyticFunctions) (v : V.AnalyticFunctions)
    (hcompat : ∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
      U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v)
    (hPv : V.analyticComponent none v = 0)
    (hUzero : ∀ i, (∃ j, U.holeOpenDisc i ⊆ V.holeOpenDisc j) → U.analyticComponent (some i) u = 0)
    (hVzero : ∀ j, (Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨
      ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i ∧ V.holeRadius j < U.holeRadius i) →
        V.analyticComponent (some j) v = 0) :
    u = 0 ∧ v = 0 := by
  classical
  obtain ⟨q,W,hW⟩ := U.exists_intersection_of_nonempty V ⟨x,hxU,hxV⟩
  have hWU : W.carrier ⊆ U.carrier := by rw [hW]; exact Set.inter_subset_left
  have hWV : W.carrier ⊆ V.carrier := by rw [hW]; exact Set.inter_subset_right
  have hcomp : U.analyticRestriction W hWU u = V.analyticRestriction W hWV v := by
    apply W.analyticFunctions_eq_of_evaluation_eq
    intro z
    rw [U.analyticRestriction_evaluation,V.analyticRestriction_evaluation]
    exact hcompat z.1 (hWU z.2) (hWV z.2)
  apply U.compatible_pair_eq_zero_of_all_union_components_zero V hR x hxU hxV u v hcompat hPv hUzero
  intro j hj
  rcases hj with hd | ⟨i,hsub⟩
  · exact hVzero j (Or.inl hd)
  by_cases hlt : V.holeRadius j < U.holeRadius i
  · exact hVzero j (Or.inr ⟨i,hsub,hlt⟩)
  have htests := (fc_openLinearDisc_subset_iff (V.holeCenter j) (U.holeCenter i)
    (V.holeRadius j) (U.holeRadius i) (V.holeRadius_pos j)).mp hsub
  have hrad : V.holeRadius j = U.holeRadius i := le_antisymm htests.1 (le_of_not_gt hlt)
  have hrev : U.holeOpenDisc i ⊆ V.holeOpenDisc j := by
    apply (fc_openLinearDisc_subset_iff _ _ _ _ (U.holeRadius_pos i)).mpr
    have hs : NormedField.valuation (U.holeCenter i-V.holeCenter j) =
        NormedField.valuation (V.holeCenter j-U.holeCenter i) := by
      rw [show U.holeCenter i-V.holeCenter j = -(V.holeCenter j-U.holeCenter i) by ring,Valuation.map_neg]
    exact ⟨hrad.symm.le,by rw [hrad,hs]; exact htests.2⟩
  have hpoint : V.holeBoundaryPoint j = U.holeBoundaryPoint i := by
    simp only [holeBoundaryPoint]
    rw [hrad]
    exact fc_centeredGauss_eq_of_center_dist_le _ _ _ htests.2.le
  have hboundary : V.holeBoundaryPoint j ∈ W.carrier := by
    rw [hW]
    exact ⟨hpoint ▸ U.holeGauss_mem i,V.holeGauss_mem j⟩
  obtain ⟨k,_,hkhole,hdet⟩ := V.exists_restricted_principal_detector_of_boundary_mem W hWV j hboundary
  have hki : W.restrictionHoleIndex U hWU i = some k := by
    apply (W.restrictionHoleIndex_eq_some_iff U hWU i k).mpr
    change U.holeOpenDisc i ⊆ W.holeOpenDisc k
    rw [hkhole]
    exact hrev
  have honly (i' : Fin m) (hi' : W.restrictionHoleIndex U hWU i' = some k) : i' = i := by
    have h := (W.restrictionHoleIndex_eq_some_iff U hWU i' k).mp hi'
    change U.holeOpenDisc i' ⊆ W.holeOpenDisc k at h
    rw [hkhole] at h
    exact hole_index_eq_of_subset U i' i (h.trans hsub)
  have hleft := U.restricted_principal_single W hWU i k hki honly u
  rw [hUzero i ⟨j,hrev⟩,map_zero] at hleft
  have hzero : V.analyticRestriction W hWV (V.analyticComponent (some j) v) = 0 :=
    (hdet v).symm.trans ((congrArg (W.analyticComponent (some k)) hcomp.symm).trans hleft)
  exact V.principal_eq_zero_of_restriction_eq_zero W hWV j hboundary _
    (V.analyticComponent_mem_closure (some j) v) hzero

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
