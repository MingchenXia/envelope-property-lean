import EnvelopeProperty.Potential.LineFiniteHoleDomains

/-! # Actual original hole routing derived from whole carrier inequalities -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (W : FCStandardAffinoid w m)

/-- An actual excluded original open disc inside the outer disc is contained in an ORIGINAL retained hole, with derived exact radius/strict-centre bounds. -/
theorem exists_hole_containing_open_disc (a : K) (r : ℝ≥0) (hr : 0 < r)
    (hc : w (a-W.center) ≤ W.radius)
    (hbound : ∀ x ∈ W.carrier, r ≤ val x (X-C a)) :
    ∃ j : Fin m, r ≤ W.holeRadius j ∧ w (a-W.holeCenter j) < W.holeRadius j ∧
      fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j) := by
  let x := centeredGauss (self w) a 0
  have hsym (b : K) : w (b-a) = w (a-b) := by
    rw [show b-a = -(a-b) by ring,Valuation.map_neg]
  have hxouter : val x (X-C W.center) ≤ W.radius := by
    simpa only [x,fc_centeredGauss_val_X_sub_C,max_zero,hsym] using hc
  have hxnot : x ∉ W.carrier := by
    intro hx
    have h := hbound x hx
    have hz : val x (X-C a) = 0 := by simp only [x,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self]
    rw [hz] at h
    exact not_lt_of_ge h hr
  have hex : ∃ j, val x (X-C (W.holeCenter j)) < W.holeRadius j := by
    by_contra! h
    exact hxnot ⟨hxouter,h⟩
  obtain ⟨j,hj⟩ := hex
  have hdist : w (a-W.holeCenter j) < W.holeRadius j := by
    simpa only [x,fc_centeredGauss_val_X_sub_C,max_zero,hsym] using hj
  have hrad : r ≤ W.holeRadius j := by
    have h := hbound (centeredGauss (self w) (W.holeCenter j) (W.holeRadius j)) (W.holeGauss_mem j)
    change r ≤ val (centeredGauss (self w) (W.holeCenter j) (W.holeRadius j)) (X-C a) at h
    simpa only [fc_centeredGauss_val_X_sub_C,hsym,max_eq_right hdist.le] using h
  refine ⟨j,hrad,hdist,?_⟩
  intro y hy
  exact (fc_linear_bound y a (W.holeCenter j)).trans_lt (max_lt (hy.trans_le hrad) hdist)

/-- Every actual excluded positive inside disc has a UNIQUE ORIGINAL containing hole. -/
theorem exists_unique_hole_containing_open_disc (a : K) (r : ℝ≥0) (hr : 0 < r)
    (hc : w (a-W.center) ≤ W.radius)
    (hbound : ∀ x ∈ W.carrier, r ≤ val x (X-C a)) :
    ∃! j : Fin m, fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j) := by
  obtain ⟨j,_,_,hj⟩ := W.exists_hole_containing_open_disc a r hr hc hbound
  refine ⟨j,hj,fun k hk => ?_⟩
  by_contra hne
  have hx : centeredGauss (self w) a 0 ∈ fcOpenLinearDisc a r := by
    simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using hr
  exact Set.disjoint_left.mp (W.holes_disjoint hne) (hk hx) (hj hx)
variable {l : ℕ} (U : FCStandardAffinoid w l) (hWU : W.carrier ⊆ U.carrier)

include hWU in
/-- EVERY original source hole has an ACTUAL disjoint or unique contained target-hole route. -/
theorem exists_restriction_hole_route (i : Fin l) :
    Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i))
      (fcClosedLinearDisc W.center W.radius) ∨
    ∃! j : Fin m, fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i) ⊆
      fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j) := by
  have hlow : ∀ x ∈ W.carrier, U.holeRadius i ≤ val x (X-C (U.holeCenter i)) :=
    fun x hx => (hWU hx).2 i
  rcases fc_openLinearDisc_inside_or_disjoint W.center (U.holeCenter i) W.radius (U.holeRadius i)
    W.outerGauss W.outerGauss_mem.1 (hlow _ W.outerGauss_mem) with h | h
  · exact Or.inr (W.exists_unique_hole_containing_open_disc _ _ (U.holeRadius_pos i) h.2.1 hlow)
  · exact Or.inl h

private theorem hole_subset_not_disjoint_outer (i : Fin l) (j : Fin m)
    (hsub : fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i) ⊆
      fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j)) :
    ¬Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i))
      (fcClosedLinearDisc W.center W.radius) := by
  let x := centeredGauss (self w) (U.holeCenter i) 0
  have hx : x ∈ fcOpenLinearDisc (U.holeCenter i) (U.holeRadius i) := by
    simpa only [x,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self]
      using U.holeRadius_pos i
  have hxH := hsub hx
  have hcent : w (W.holeCenter j-W.center) ≤ W.radius := W.holeCenter_le j
  have hxD : x ∈ fcClosedLinearDisc W.center W.radius :=
    (fc_linear_bound x (W.holeCenter j) W.center).trans
      (max_le (hxH.le.trans (W.holeRadius_le j)) hcent)
  exact fun h => Set.disjoint_left.mp h hx hxD

/-- The actual OPTIONAL ORIGINAL target index is chosen only from the proved geometric alternatives. -/
def restrictionHoleIndex (i : Fin l) : Option (Fin m) := by
  classical
  exact if h : Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i))
      (fcClosedLinearDisc W.center W.radius) then none
    else some (Classical.choose ((W.exists_restriction_hole_route U hWU i).resolve_left h))

theorem restrictionHoleIndex_eq_none_iff (i : Fin l) :
    W.restrictionHoleIndex U hWU i = none ↔
      Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i))
        (fcClosedLinearDisc W.center W.radius) := by
  classical
  unfold restrictionHoleIndex
  split_ifs <;> simp_all

theorem restrictionHoleIndex_eq_some_iff (i : Fin l) (j : Fin m) :
    W.restrictionHoleIndex U hWU i = some j ↔
      fcOpenLinearDisc (w := w) (U.holeCenter i) (U.holeRadius i) ⊆
        fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j) := by
  classical
  unfold restrictionHoleIndex
  split_ifs with hd
  · constructor
    · simp
    · intro hsub
      exact (W.hole_subset_not_disjoint_outer U i j hsub hd).elim
  · have h := Classical.choose_spec ((W.exists_restriction_hole_route U hWU i).resolve_left hd)
    constructor
    · intro he
      exact (Option.some.inj he) ▸ h.1
    · intro hsub
      exact congrArg some (h.2 j hsub).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
