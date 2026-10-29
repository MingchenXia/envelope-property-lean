/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Potential.LineUnionHoleOwners
import EnvelopeProperty.Potential.LineBinaryGlueDetection

/-! # Actual whole compatible-pair gluing on original standard-affinoid unions -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  {m n q : ℕ}

omit [IsAlgClosed K] in
private theorem binaryGlue_hole_center_mem
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m) (i : Fin m) :
    centeredGauss (self (NormedField.valuation (K := K))) (U.holeCenter i) 0 ∈ U.holeOpenDisc i := by
  simpa only [holeOpenDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,
    fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using U.holeRadius_pos i

omit [IsAlgClosed K] in
private theorem binaryGlue_retained_route
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (hUW : U.carrier ⊆ W.carrier) (k : Fin q) (i : Fin m)
    (hh : W.holeOpenDisc k = U.holeOpenDisc i) :
    U.restrictionHoleIndex W hUW k = some i ∧
      ∀ j, U.restrictionHoleIndex W hUW j = some i → j = k := by
  constructor
  · apply (U.restrictionHoleIndex_eq_some_iff W hUW k i).mpr
    change W.holeOpenDisc k ⊆ U.holeOpenDisc i
    rw [hh]
  · intro j hj
    by_contra hne
    have hsub := (U.restrictionHoleIndex_eq_some_iff W hUW j i).mp hj
    change W.holeOpenDisc j ⊆ U.holeOpenDisc i at hsub
    have hz := binaryGlue_hole_center_mem W j
    have hzk : centeredGauss (self (NormedField.valuation (K := K)))
        (W.holeCenter j) 0 ∈ W.holeOpenDisc k := by
      rw [hh]
      exact hsub hz
    exact Set.disjoint_left.mp (W.holes_disjoint hne) hz hzk

private theorem binaryGlue_restriction_component
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (hUW : U.carrier ⊆ W.carrier) (j : Fin q) (k : Option (Fin m))
    (g : W.AnalyticFunctions) (hg : g ∈ closure (W.rationalComponentSet (some j))) :
    U.analyticComponent k (W.analyticRestriction U hUW g) =
      if k = U.restrictionHoleIndex W hUW j then W.analyticRestriction U hUW g else 0 := by
  exact U.analyticComponent_of_mem_closure k _ _
    (W.analyticRestriction_principal_closure_routed U hUW j g hg)

private theorem binaryGlue_nnnorm_sum_le {A ι : Type*} [NormedAddCommGroup A]
    [IsUltrametricDist A] (s : Finset ι) (f : ι → A) (B : ℝ≥0)
    (h : ∀ i ∈ s, ‖f i‖₊ ≤ B) : ‖∑ i ∈ s, f i‖₊ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hn : ‖f i + ∑ j ∈ s, f j‖₊ ≤ max ‖f i‖₊ ‖∑ j ∈ s, f j‖₊ := by
      exact_mod_cast IsUltrametricDist.norm_add_le_max (f i) (∑ j ∈ s, f j)
    exact hn.trans (max_le (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem binaryGlue_retained_component_sum
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (hUW : U.carrier ⊆ W.carrier)
    (P : W.AnalyticFunctions) (hP : P ∈ closure (W.rationalComponentSet none))
    (G : Fin q → W.AnalyticFunctions)
    (hG : ∀ j, G j ∈ closure (W.rationalComponentSet (some j)))
    (k : Fin q) (i : Fin m) (hh : W.holeOpenDisc k = U.holeOpenDisc i) :
    U.analyticComponent (some i) (W.analyticRestriction U hUW (P+∑ j, G j)) =
      W.analyticRestriction U hUW (G k) := by
  classical
  obtain ⟨hki,honly⟩ := binaryGlue_retained_route W U hUW k i hh
  have hpzero : U.analyticComponent (some i) (W.analyticRestriction U hUW P) = 0 := by
    simpa only [Option.some_ne_none,if_false] using
      U.analyticComponent_of_mem_closure (some i) none _
        (W.analyticRestriction_polynomial_closure U hUW P hP)
  simp only [map_add,map_sum,hpzero,zero_add]
  rw [Finset.sum_eq_single k]
  · rw [binaryGlue_restriction_component W U hUW k (some i) (G k) (hG k),hki,if_pos rfl]
  · intro j _ hjk
    rw [binaryGlue_restriction_component W U hUW j (some i) (G j) (hG j)]
    exact if_neg (fun h => hjk (honly j h.symm))
  · simp

omit [IsAlgClosed K] in
private theorem binaryGlue_principal_route_ne_none
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (hVW : V.carrier ⊆ W.carrier) (hc : W.center = V.center) (hr : W.radius = V.radius)
    (j : Fin q) : V.restrictionHoleIndex W hVW j ≠ none := by
  intro hn
  have hd := (V.restrictionHoleIndex_eq_none_iff W hVW j).mp hn
  have hz := binaryGlue_hole_center_mem W j
  have houter : centeredGauss (self (NormedField.valuation (K := K)))
      (W.holeCenter j) 0 ∈ V.outerClosedDisc := by
    change val (centeredGauss (self (NormedField.valuation (K := K)))
      (W.holeCenter j) 0) (X-C V.center) ≤ V.radius
    rw [fc_centeredGauss_val_X_sub_C,max_zero]
    rw [← hc,← hr]
    exact W.holeCenter_le j
  exact Set.disjoint_left.mp hd hz houter

private theorem binaryGlue_polynomial_component_sum
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (hVW : V.carrier ⊆ W.carrier) (hc : W.center = V.center) (hr : W.radius = V.radius)
    (P : W.AnalyticFunctions) (hP : P ∈ closure (W.rationalComponentSet none))
    (G : Fin q → W.AnalyticFunctions)
    (hG : ∀ j, G j ∈ closure (W.rationalComponentSet (some j))) :
    V.analyticComponent none (W.analyticRestriction V hVW (P+∑ j, G j)) =
      W.analyticRestriction V hVW P := by
  classical
  have hpfix : V.analyticComponent none (W.analyticRestriction V hVW P) =
      W.analyticRestriction V hVW P := by
    simpa using
      V.analyticComponent_of_mem_closure none none _
        (W.analyticRestriction_polynomial_closure V hVW P hP)
  simp only [map_add,map_sum,hpfix]
  have hz : ∑ j, V.analyticComponent none (W.analyticRestriction V hVW (G j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [binaryGlue_restriction_component W V hVW j none (G j) (hG j)]
    exact if_neg (Ne.symm (binaryGlue_principal_route_ne_none W V hVW hc hr j))
  rw [hz,add_zero]

private theorem binaryGlue_exists_retained
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum (NormedField.valuation (K := K)) K[X])
    (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier)
    (hUW : U.carrier ⊆ W.carrier) (hVW : V.carrier ⊆ W.carrier)
    (hc : W.center = V.center) (hr : W.radius = V.radius)
    (o : Fin q → Fin m ⊕ Fin n)
    (hh : ∀ j, W.holeCenter j = U.combinedHoleCenter V (o j) ∧
      W.holeRadius j = U.combinedHoleRadius V (o j))
    (hUimage : ∀ i, (∃ j, o j = Sum.inl i) ↔ ∃ k, U.holeOpenDisc i ⊆ V.holeOpenDisc k)
    (hVimage : ∀ j, (∃ k, o k = Sum.inr j) ↔
      Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨
        ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i ∧ V.holeRadius j < U.holeRadius i)
    (u : U.AnalyticFunctions) (v : V.AnalyticFunctions)
    (hcompat : ∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
      U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v) :
    ∃ f : W.AnalyticFunctions,
      W.analyticRestriction U hUW f = u ∧ W.analyticRestriction V hVW f = v ∧
      ‖f‖₊ ≤ max ‖u‖₊ ‖v‖₊ := by
  classical
  obtain ⟨P,hP,hPv,hnP⟩ := W.exists_polynomial_component_lift V hVW hc hr v
  have hparts (j : Fin q) : ∃ g : W.AnalyticFunctions,
      g ∈ closure (W.rationalComponentSet (some j)) ∧ ‖g‖₊ ≤ max ‖u‖₊ ‖v‖₊ ∧
      (∀ i, o j = Sum.inl i → W.analyticRestriction U hUW g = U.analyticComponent (some i) u) ∧
      (∀ i, o j = Sum.inr i → W.analyticRestriction V hVW g = V.analyticComponent (some i) v) := by
    have hhj := hh j
    cases ho : o j with
    | inl i =>
      have hci : W.holeCenter j = U.holeCenter i := by
        simpa only [ho,combinedHoleCenter,Sum.elim_inl] using hhj.1
      have hri : W.holeRadius j = U.holeRadius i := by
        simpa only [ho,combinedHoleRadius,Sum.elim_inl] using hhj.2
      obtain ⟨g,hg,hval,hng⟩ := W.exists_principal_component_lift U hUW j i hci hri u
      refine ⟨g,hg,hng.le.trans ((U.nnnorm_analyticComponent_le (some i) u).trans (le_max_left _ _)),?_,?_⟩
      · intro i' he
        cases Sum.inl.inj he
        exact hval
      · intro i' he
        exact (Sum.inl_ne_inr he).elim
    | inr i =>
      have hci : W.holeCenter j = V.holeCenter i := by
        simpa only [ho,combinedHoleCenter,Sum.elim_inr] using hhj.1
      have hri : W.holeRadius j = V.holeRadius i := by
        simpa only [ho,combinedHoleRadius,Sum.elim_inr] using hhj.2
      obtain ⟨g,hg,hval,hng⟩ := W.exists_principal_component_lift V hVW j i hci hri v
      refine ⟨g,hg,hng.le.trans ((V.nnnorm_analyticComponent_le (some i) v).trans (le_max_right _ _)),?_,?_⟩
      · intro i' he
        exact (Sum.inr_ne_inl he).elim
      · intro i' he
        cases Sum.inr.inj he
        exact hval
  choose G hG hnG hGU hGV using hparts
  let f : W.AnalyticFunctions := P+∑ j, G j
  have hUzero (i : Fin m) (hi : ∃ j, U.holeOpenDisc i ⊆ V.holeOpenDisc j) :
      U.analyticComponent (some i) (W.analyticRestriction U hUW f-u) = 0 := by
    obtain ⟨j,hj⟩ := (hUimage i).mpr hi
    have hhj := hh j
    have hhole : W.holeOpenDisc j = U.holeOpenDisc i := by
      simp only [hj,combinedHoleCenter,Sum.elim_inl,combinedHoleRadius] at hhj
      simp only [holeOpenDisc,hhj.1,hhj.2]
    have he := binaryGlue_retained_component_sum W U hUW P hP G hG j i hhole
    rw [hGU j i hj] at he
    change U.analyticComponent (some i) (W.analyticRestriction U hUW (P+∑ j, G j)-u) = 0
    rw [map_sub,he,sub_self]
  have hVzero (i : Fin n) (hi : Disjoint (V.holeOpenDisc i) U.outerClosedDisc ∨
      ∃ j, V.holeOpenDisc i ⊆ U.holeOpenDisc j ∧ V.holeRadius i < U.holeRadius j) :
      V.analyticComponent (some i) (W.analyticRestriction V hVW f-v) = 0 := by
    obtain ⟨j,hj⟩ := (hVimage i).mpr hi
    have hhj := hh j
    have hhole : W.holeOpenDisc j = V.holeOpenDisc i := by
      simp only [hj,combinedHoleCenter,Sum.elim_inr,combinedHoleRadius] at hhj
      simp only [holeOpenDisc,hhj.1,hhj.2]
    have he := binaryGlue_retained_component_sum W V hVW P hP G hG j i hhole
    rw [hGV j i hj] at he
    change V.analyticComponent (some i) (W.analyticRestriction V hVW (P+∑ j, G j)-v) = 0
    rw [map_sub,he,sub_self]
  have hPvzero : V.analyticComponent none (W.analyticRestriction V hVW f-v) = 0 := by
    have he := binaryGlue_polynomial_component_sum W V hVW hc hr P hP G hG
    rw [hPv] at he
    change V.analyticComponent none (W.analyticRestriction V hVW (P+∑ j, G j)-v) = 0
    rw [map_sub,he,sub_self]
  have hrescompat : ∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
      U.evaluationToH ⟨y,hyU⟩ (W.analyticRestriction U hUW f-u) =
        V.evaluationToH ⟨y,hyV⟩ (W.analyticRestriction V hVW f-v) := by
    intro y hyU hyV
    rw [map_sub,map_sub,W.analyticRestriction_evaluation,W.analyticRestriction_evaluation,hcompat y hyU hyV]
  obtain ⟨hu,hv⟩ := U.compatible_pair_eq_zero_of_union_components_zero V hR x hxU hxV
    _ _ hrescompat hPvzero hUzero hVzero
  refine ⟨f,sub_eq_zero.mp hu,sub_eq_zero.mp hv,?_⟩
  have hnadd : ‖P+∑ j, G j‖₊ ≤ max ‖P‖₊ ‖∑ j, G j‖₊ := by
    exact_mod_cast IsUltrametricDist.norm_add_le_max P (∑ j, G j)
  exact hnadd.trans (max_le
    (hnP.le.trans ((V.nnnorm_analyticComponent_le none v).trans (le_max_right _ _)))
    (binaryGlue_nnnorm_sum_le Finset.univ G _ (fun j _ => hnG j)))

private theorem binaryGlue_exists_ordered
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (hR : U.radius ≤ V.radius) (hne : (U.carrier ∩ V.carrier).Nonempty) :
    ∃ (q : ℕ) (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
      (hW : W.carrier = U.carrier ∪ V.carrier),
      ∀ (u : U.AnalyticFunctions) (v : V.AnalyticFunctions),
      (∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
        U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v) →
      ∃ f : W.AnalyticFunctions,
        W.analyticRestriction U (by rw [hW]; exact Set.subset_union_left) f = u ∧
        W.analyticRestriction V (by rw [hW]; exact Set.subset_union_right) f = v ∧
        ‖f‖₊ ≤ max ‖u‖₊ ‖v‖₊ := by
  obtain ⟨x,hxU,hxV⟩ := hne
  obtain ⟨q,W,o,hc,hr,hW,_,hh,hUimage,hVimage⟩ :=
    U.exists_union_with_original_owners V hR x hxU hxV
  refine ⟨q,W,hW,fun u v hcompat => ?_⟩
  exact binaryGlue_exists_retained U V W hR x hxU hxV
    (by rw [hW]; exact Set.subset_union_left)
    (by rw [hW]; exact Set.subset_union_right) hc hr o hh hUimage hVimage u v hcompat

private theorem binaryGlue_functions_unique
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (hW : W.carrier = U.carrier ∪ V.carrier)
    (hUW : U.carrier ⊆ W.carrier) (hVW : V.carrier ⊆ W.carrier)
    (f g : W.AnalyticFunctions)
    (hU : W.analyticRestriction U hUW f = W.analyticRestriction U hUW g)
    (hV : W.analyticRestriction V hVW f = W.analyticRestriction V hVW g) : f = g := by
  apply W.analyticFunctions_eq_of_evaluation_eq
  intro y
  have hy : y.1 ∈ U.carrier ∪ V.carrier := hW ▸ y.2
  rcases hy with hyU | hyV
  · have he := congrArg (U.evaluationToH ⟨y.1,hyU⟩) hU
    simpa only [W.analyticRestriction_evaluation] using he
  · have he := congrArg (V.evaluationToH ⟨y.1,hyV⟩) hV
    simpa only [W.analyticRestriction_evaluation] using he

/-- Every actual overlapping pair has a constructed original union on which EVERY whole compatible pair glues uniquely with the exact original maximum norm. -/
theorem exists_unique_binary_glue
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (hne : (U.carrier ∩ V.carrier).Nonempty) :
    ∃ (q : ℕ) (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
      (hW : W.carrier = U.carrier ∪ V.carrier),
      ∀ (u : U.AnalyticFunctions) (v : V.AnalyticFunctions),
      (∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
        U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v) →
      ∃! f : W.AnalyticFunctions,
        W.analyticRestriction U (by rw [hW]; exact Set.subset_union_left) f = u ∧
        W.analyticRestriction V (by rw [hW]; exact Set.subset_union_right) f = v ∧
        ‖f‖₊ = max ‖u‖₊ ‖v‖₊ := by
  have hraw : ∃ (q : ℕ) (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
      (hW : W.carrier = U.carrier ∪ V.carrier),
      ∀ (u : U.AnalyticFunctions) (v : V.AnalyticFunctions),
      (∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
        U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v) →
      ∃ f : W.AnalyticFunctions,
        W.analyticRestriction U (by rw [hW]; exact Set.subset_union_left) f = u ∧
        W.analyticRestriction V (by rw [hW]; exact Set.subset_union_right) f = v ∧
        ‖f‖₊ ≤ max ‖u‖₊ ‖v‖₊ := by
    rcases le_total U.radius V.radius with hR | hR
    · exact binaryGlue_exists_ordered U V hR hne
    · obtain ⟨q,W,hW,hglue⟩ := binaryGlue_exists_ordered V U hR
        (by simpa only [Set.inter_comm] using hne)
      have hW' : W.carrier = U.carrier ∪ V.carrier := hW.trans (Set.union_comm _ _)
      refine ⟨q,W,hW',fun u v hcompat => ?_⟩
      obtain ⟨f,hv,hu,hn⟩ := hglue v u (fun y hyV hyU => (hcompat y hyU hyV).symm)
      exact ⟨f,hu,hv,by simpa only [max_comm] using hn⟩
  obtain ⟨q,W,hW,hglue⟩ := hraw
  refine ⟨q,W,hW,fun u v hcompat => ?_⟩
  obtain ⟨f,hu,hv,hn⟩ := hglue u v hcompat
  have hnexact : ‖f‖₊ = max ‖u‖₊ ‖v‖₊ := by
    apply le_antisymm hn
    apply max_le
    · rw [← hu]
      exact W.nnnorm_analyticRestriction_le U _ f
    · rw [← hv]
      exact W.nnnorm_analyticRestriction_le V _ f
  refine ⟨f,⟨hu,hv,hnexact⟩,fun g hg => ?_⟩
  exact binaryGlue_functions_unique U V W hW _ _ g f (hg.1.trans hu.symm) (hg.2.1.trans hv.symm)

/-- An already specified ORIGINAL affinoid union has the same genuine unique whole glue; no completed algebra is replaced by an equal-carrier copy. -/
theorem exists_unique_binary_glue_on
    (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
    (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
    (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (hW : W.carrier = U.carrier ∪ V.carrier)
    (hne : (U.carrier ∩ V.carrier).Nonempty)
    (u : U.AnalyticFunctions) (v : V.AnalyticFunctions)
    (hcompat : ∀ y (hyU : y ∈ U.carrier) (hyV : y ∈ V.carrier),
      U.evaluationToH ⟨y,hyU⟩ u = V.evaluationToH ⟨y,hyV⟩ v) :
    ∃! f : W.AnalyticFunctions,
      W.analyticRestriction U (by rw [hW]; exact Set.subset_union_left) f = u ∧
      W.analyticRestriction V (by rw [hW]; exact Set.subset_union_right) f = v ∧
      ‖f‖₊ = max ‖u‖₊ ‖v‖₊ := by
  obtain ⟨l,A,hA,hglue⟩ := U.exists_unique_binary_glue V hne
  obtain ⟨f,hf,_⟩ := hglue u v hcompat
  have hWA : W.carrier ⊆ A.carrier := (hW.trans hA.symm).subset
  have hAW : A.carrier ⊆ W.carrier := (hA.trans hW.symm).subset
  let g := A.analyticRestriction W hWA f
  have hu : W.analyticRestriction U (by rw [hW]; exact Set.subset_union_left) g = u := by
    change ((W.analyticRestriction U _).comp (A.analyticRestriction W hWA)) f = u
    rw [A.analyticRestriction_comp W hWA U]
    exact hf.1
  have hv : W.analyticRestriction V (by rw [hW]; exact Set.subset_union_right) g = v := by
    change ((W.analyticRestriction V _).comp (A.analyticRestriction W hWA)) f = v
    rw [A.analyticRestriction_comp W hWA V]
    exact hf.2.1
  have hn : ‖g‖₊ = max ‖u‖₊ ‖v‖₊ := by
    apply le_antisymm ((A.nnnorm_analyticRestriction_le W hWA f).trans_eq hf.2.2)
    apply max_le
    · rw [← hu]
      exact W.nnnorm_analyticRestriction_le U _ g
    · rw [← hv]
      exact W.nnnorm_analyticRestriction_le V _ g
  refine ⟨g,⟨hu,hv,hn⟩,fun z hz => ?_⟩
  exact binaryGlue_functions_unique U V W hW _ _ z g (hz.1.trans hu.symm) (hz.2.1.trans hv.symm)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
