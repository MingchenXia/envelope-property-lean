import EnvelopeProperty.Potential.LineFiniteHoleDomains

/-! # Nonempty actual intersections with retained original hole data -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)

/-- The finite family consists of precisely the ORIGINAL two hole-center families. -/
def combinedHoleCenter : Fin m ⊕ Fin n → K := Sum.elim U.holeCenter V.holeCenter

/-- The same original indices retain their ORIGINAL hole radii. -/
def combinedHoleRadius : Fin m ⊕ Fin n → ℝ≥0 := Sum.elim U.holeRadius V.holeRadius

/-- The ACTUAL common point and ordered radii construct the exact intersection with injectively retained ORIGINAL holes. -/
theorem exists_intersection_of_radius_le (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q) (sourceIndex : Fin q → Fin m ⊕ Fin n),
      W.center = U.center ∧ W.radius = U.radius ∧ Function.Injective sourceIndex ∧
      (∀ j, W.holeCenter j = U.combinedHoleCenter V (sourceIndex j) ∧
        W.holeRadius j = U.combinedHoleRadius V (sourceIndex j)) ∧
      W.carrier = U.carrier ∩ V.carrier := by
  have hl (i : Fin m ⊕ Fin n) : U.combinedHoleRadius V i ≤ val x (X-C (U.combinedHoleCenter V i)) := by
    cases i with
    | inl i => exact hxU.2 i
    | inr i => exact hxV.2 i
  obtain ⟨q,W,sourceIndex,hc,hr,hi,hh,hW⟩ := fc_exists_standardAffinoid_exact_finite_bounds
    x U.center U.radius (U.combinedHoleCenter V) (U.combinedHoleRadius V) hxU.1 hl
  refine ⟨q,W,sourceIndex,hc,hr,hi,hh,?_⟩
  rw [hW]
  have hd := fc_closedLinearDisc_subset_of_common U.center V.center U.radius V.radius x hxU.1 hxV.1 hR
  ext y
  constructor
  · intro hy
    exact ⟨⟨hy.1,fun j => hy.2 (Sum.inl j)⟩,⟨hd hy.1,fun j => hy.2 (Sum.inr j)⟩⟩
  · rintro ⟨hyU,hyV⟩
    refine ⟨hyU.1,fun i => ?_⟩
    cases i with
    | inl j => exact hyU.2 j
    | inr j => exact hyV.2 j

/-- Every ACTUAL nonempty intersection has exact carrier equality, original minimum outer radius, and ORIGINAL hole data. -/
theorem exists_intersection (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q) (sourceIndex : Fin q → Fin m ⊕ Fin n),
      (W.center = U.center ∨ W.center = V.center) ∧ W.radius = min U.radius V.radius ∧
      Function.Injective sourceIndex ∧
      (∀ j, W.holeCenter j = U.combinedHoleCenter V (sourceIndex j) ∧
        W.holeRadius j = U.combinedHoleRadius V (sourceIndex j)) ∧
      W.carrier = U.carrier ∩ V.carrier := by
  rcases le_total U.radius V.radius with hR | hR
  · obtain ⟨q,W,s,hc,hr,hi,hh,hW⟩ := U.exists_intersection_of_radius_le V hR x hxU hxV
    exact ⟨q,W,s,Or.inl hc,hr.trans (min_eq_left hR).symm,hi,hh,hW⟩
  · obtain ⟨q,W,s,hc,hr,hi,hh,hW⟩ := V.exists_intersection_of_radius_le U hR x hxV hxU
    refine ⟨q,W,fun j => (Equiv.sumComm (Fin n) (Fin m)) (s j),Or.inr hc,
      hr.trans (min_eq_right hR).symm,(Equiv.sumComm _ _).injective.comp hi,?_,?_⟩
    · intro j
      have h := hh j
      cases hs : s j with
      | inl i => simpa only [hs,combinedHoleCenter,combinedHoleRadius,Equiv.sumComm_apply,Sum.swap_inl,Sum.elim_inl,Sum.elim_inr] using h
      | inr i => simpa only [hs,combinedHoleCenter,combinedHoleRadius,Equiv.sumComm_apply,Sum.swap_inr,Sum.elim_inl,Sum.elim_inr] using h
    · exact hW.trans (Set.inter_comm _ _)

/-- The actual nonempty set witness suffices; no supplied affinoid presentation is an input. -/
theorem exists_intersection_of_nonempty (hne : (U.carrier ∩ V.carrier).Nonempty) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q), W.carrier = U.carrier ∩ V.carrier := by
  obtain ⟨x,hxU,hxV⟩ := hne
  obtain ⟨q,W,_,_,_,_,_,hW⟩ := U.exists_intersection V x hxU hxV
  exact ⟨q,W,hW⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
