import EnvelopeProperty.Potential.LineAffinoidIntersections

/-! # Actual overlapping unions from original laminar OPEN holes -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The ORIGINAL center of the smaller original open hole. -/
def fcOpenIntersectionCenter (a b : K) (r s : ℝ≥0) : K := if r ≤ s then a else b

/-- Inactive actual intersections use radius zero; every active radius is an ORIGINAL input radius. -/
def fcOpenIntersectionRadius (a b : K) (r s : ℝ≥0) : ℝ≥0 := by
  classical
  exact if Disjoint (fcOpenLinearDisc (w := w) a r) (fcOpenLinearDisc b s) then 0 else min r s

/-- The actual intersection of original OPEN holes is the smaller ORIGINAL hole, or empty. -/
theorem fc_openLinearDisc_intersection_eq (a b : K) (r s : ℝ≥0) :
    fcOpenLinearDisc (w := w) (fcOpenIntersectionCenter a b r s) (fcOpenIntersectionRadius (w := w) a b r s) =
      fcOpenLinearDisc (w := w) a r ∩ fcOpenLinearDisc b s := by
  classical
  by_cases hd : Disjoint (fcOpenLinearDisc (w := w) a r) (fcOpenLinearDisc b s)
  · rw [Set.disjoint_iff_inter_eq_empty.mp hd]
    have hr : fcOpenIntersectionRadius (w := w) a b r s = 0 := if_pos hd
    rw [hr]
    ext x
    simp [fcOpenLinearDisc]
  · obtain ⟨z,hza,hzb⟩ := Set.not_disjoint_iff.mp hd
    by_cases hrs : r ≤ s
    · have hab : w (a-b) < s := (fc_center_distance_bound z a b).trans_lt (max_lt (hza.trans_le hrs) hzb)
      have hsub : fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc b s := fun y hy =>
        (fc_linear_bound y a b).trans_lt (max_lt (hy.trans_le hrs) hab)
      simp only [fcOpenIntersectionCenter,if_pos hrs,fcOpenIntersectionRadius,if_neg hd,min_eq_left hrs]
      exact Set.Subset.antisymm (fun _ hy => ⟨hy,hsub hy⟩) (fun _ hy => hy.1)
    · have hsr : s ≤ r := le_of_not_ge hrs
      have hba : w (b-a) < r := (fc_center_distance_bound z b a).trans_lt (max_lt (hzb.trans_le hsr) hza)
      have hsub : fcOpenLinearDisc (w := w) b s ⊆ fcOpenLinearDisc a r := fun y hy =>
        (fc_linear_bound y b a).trans_lt (max_lt (hy.trans_le hsr) hba)
      simp only [fcOpenIntersectionCenter,if_neg hrs,fcOpenIntersectionRadius,if_neg hd,min_eq_right hsr]
      exact Set.Subset.antisymm (fun _ hy => ⟨hsub hy,hy⟩) (fun _ hy => hy.2)

namespace FCStandardAffinoid
variable {m n : ℕ} (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)

/-- The actual original outer closed disc, before its original open holes are removed. -/
def outerClosedDisc : Set (RelativeSpectrum w K[X]) := fcClosedLinearDisc U.center U.radius

/-- A literal ORIGINAL OPEN hole. -/
def holeOpenDisc (j : Fin m) : Set (RelativeSpectrum w K[X]) := fcOpenLinearDisc (U.holeCenter j) (U.holeRadius j)

theorem mem_carrier_iff_not_open_holes (y : RelativeSpectrum w K[X]) :
    y ∈ U.carrier ↔ y ∈ U.outerClosedDisc ∧ ∀ j, y ∉ U.holeOpenDisc j := by
  simp only [carrier,outerClosedDisc,holeOpenDisc,fcClosedLinearDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,not_lt]

theorem holeOpenDisc_subset_outerClosedDisc (j : Fin m) : U.holeOpenDisc j ⊆ U.outerClosedDisc := by
  intro y hy
  exact (fc_linear_bound y (U.holeCenter j) U.center).trans
    (max_le (hy.le.trans (U.holeRadius_le j)) (U.holeCenter_le j))

/-- Original centers of outside V-holes and original smaller pairwise open-hole intersections. -/
def unionHoleCenter : Fin n ⊕ (Fin m × Fin n) → K := fun i => match i with
  | Sum.inl j => V.holeCenter j
  | Sum.inr p => fcOpenIntersectionCenter (U.holeCenter p.1) (V.holeCenter p.2)
      (U.holeRadius p.1) (V.holeRadius p.2)

/-- Actual missing open holes; radius zero is only an inactive placeholder and is pruned by exact normalization. -/
def unionHoleRadius : Fin n ⊕ (Fin m × Fin n) → ℝ≥0 := by
  classical
  exact fun i => match i with
  | Sum.inl j => if Disjoint (V.holeOpenDisc j) U.outerClosedDisc then V.holeRadius j else 0
  | Sum.inr p => fcOpenIntersectionRadius (w := w) (U.holeCenter p.1) (V.holeCenter p.2)
      (U.holeRadius p.1) (V.holeRadius p.2)

theorem unionHole_inl_eq_of_disjoint (j : Fin n)
    (hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc) :
    fcOpenLinearDisc (w := w) (U.unionHoleCenter V (Sum.inl j)) (U.unionHoleRadius V (Sum.inl j)) =
      V.holeOpenDisc j := by
  classical
  simp only [unionHoleCenter,unionHoleRadius,if_pos hd]
  rfl

theorem unionHole_inl_eq_of_not_disjoint (j : Fin n)
    (hd : ¬Disjoint (V.holeOpenDisc j) U.outerClosedDisc) :
    fcOpenLinearDisc (w := w) (U.unionHoleCenter V (Sum.inl j)) (U.unionHoleRadius V (Sum.inl j)) = ∅ := by
  classical
  simp only [unionHoleCenter,unionHoleRadius,if_neg hd]
  ext y
  simp [fcOpenLinearDisc]

theorem unionHole_inr_eq (i : Fin m) (j : Fin n) :
    fcOpenLinearDisc (w := w) (U.unionHoleCenter V (Sum.inr (i,j))) (U.unionHoleRadius V (Sum.inr (i,j))) =
      U.holeOpenDisc i ∩ V.holeOpenDisc j :=
  fc_openLinearDisc_intersection_eq _ _ _ _

/-- The actual missing-hole formula for overlapping affinoids; OPEN-hole strictness is unchanged. -/
theorem union_hole_domain_eq (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    {y | y ∈ V.outerClosedDisc ∧ ∀ i, y ∉ fcOpenLinearDisc (w := w)
      (U.unionHoleCenter V i) (U.unionHoleRadius V i)} = U.carrier ∪ V.carrier := by
  classical
  have houter : U.outerClosedDisc ⊆ V.outerClosedDisc :=
    fc_closedLinearDisc_subset_of_common _ _ _ _ x hxU.1 hxV.1 hR
  ext y
  constructor
  · rintro ⟨hyD,hyholes⟩
    by_cases hyV : y ∈ V.carrier
    · exact Or.inr hyV
    have hyj : ∃ j, y ∈ V.holeOpenDisc j := by
      by_contra hbad
      apply hyV
      exact (V.mem_carrier_iff_not_open_holes y).mpr ⟨hyD,by simpa only [not_exists] using hbad⟩
    obtain ⟨j,hyj⟩ := hyj
    have hclass := fc_openLinearDisc_inside_or_disjoint U.center (V.holeCenter j) U.radius
      (V.holeRadius j) x hxU.1 (hxV.2 j)
    rcases hclass with hinside | hdisj
    · have hyOU : y ∈ U.outerClosedDisc := hinside.2.2 hyj
      apply Or.inl
      apply (U.mem_carrier_iff_not_open_holes y).mpr
      refine ⟨hyOU,fun i hyi => ?_⟩
      apply hyholes (Sum.inr (i,j))
      rw [U.unionHole_inr_eq V i j]
      exact ⟨hyi,hyj⟩
    · apply False.elim
      apply hyholes (Sum.inl j)
      rw [U.unionHole_inl_eq_of_disjoint V j hdisj]
      exact hyj
  · intro hy
    have hyD : y ∈ V.outerClosedDisc := by
      rcases hy with hyU | hyV
      · exact houter hyU.1
      · exact hyV.1
    refine ⟨hyD,fun i => ?_⟩
    cases i with
    | inl j =>
      by_cases hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc
      · rw [U.unionHole_inl_eq_of_disjoint V j hd]
        intro hyh
        rcases hy with hyU | hyV
        · exact (Set.disjoint_left.mp hd) hyh hyU.1
        · exact not_lt_of_ge (hyV.2 j) hyh
      · rw [U.unionHole_inl_eq_of_not_disjoint V j hd]
        exact Set.notMem_empty _
    | inr p =>
      rw [U.unionHole_inr_eq V p.1 p.2]
      rintro ⟨hyi,hyj⟩
      rcases hy with hyU | hyV
      · exact not_lt_of_ge (hyU.2 p.1) hyi
      · exact not_lt_of_ge (hyV.2 p.2) hyj

/-- EVERY positive actual missing hole retains an ORIGINAL input center and radius. -/
theorem unionHole_active_original (i : Fin n ⊕ (Fin m × Fin n)) (hp : 0 < U.unionHoleRadius V i) :
    (∃ j, U.unionHoleCenter V i = U.holeCenter j ∧ U.unionHoleRadius V i = U.holeRadius j) ∨
      (∃ j, U.unionHoleCenter V i = V.holeCenter j ∧ U.unionHoleRadius V i = V.holeRadius j) := by
  classical
  cases i with
  | inl j =>
    by_cases hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc
    · exact Or.inr ⟨j,rfl,by simp only [unionHoleRadius,if_pos hd]⟩
    · have hz : U.unionHoleRadius V (Sum.inl j) = 0 := by simp only [unionHoleRadius,if_neg hd]
      exact False.elim (hp.ne' hz)
  | inr p =>
    by_cases hd : Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter p.1) (U.holeRadius p.1))
      (fcOpenLinearDisc (V.holeCenter p.2) (V.holeRadius p.2))
    · have hz : U.unionHoleRadius V (Sum.inr p) = 0 := by
        simp only [unionHoleRadius,fcOpenIntersectionRadius,if_pos hd]
      exact False.elim (hp.ne' hz)
    · by_cases hrs : U.holeRadius p.1 ≤ V.holeRadius p.2
      · exact Or.inl ⟨p.1,by simp only [unionHoleCenter,fcOpenIntersectionCenter,if_pos hrs],by
          simp only [unionHoleRadius,fcOpenIntersectionRadius,if_neg hd,min_eq_left hrs]⟩
      · exact Or.inr ⟨p.2,by simp only [unionHoleCenter,fcOpenIntersectionCenter,if_neg hrs],by
          simp only [unionHoleRadius,fcOpenIntersectionRadius,if_neg hd,min_eq_right (le_of_not_ge hrs)]⟩

/-- The original actual union is CONSTRUCTED, with exact carrier equality and retained original finite missing-hole indices. -/
theorem exists_union_of_radius_le (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q) (sourceIndex : Fin q → Fin n ⊕ (Fin m × Fin n)),
      W.center = V.center ∧ W.radius = V.radius ∧ Function.Injective sourceIndex ∧
      (∀ j, W.holeCenter j = U.unionHoleCenter V (sourceIndex j) ∧
        W.holeRadius j = U.unionHoleRadius V (sourceIndex j)) ∧
      W.carrier = U.carrier ∪ V.carrier := by
  have hdomain := U.union_hole_domain_eq V hR x hxU hxV
  have hxD : x ∈ {y | y ∈ V.outerClosedDisc ∧ ∀ i, y ∉ fcOpenLinearDisc (w := w)
      (U.unionHoleCenter V i) (U.unionHoleRadius V i)} := by
    rw [hdomain]
    exact Or.inl hxU
  have hl (i) : U.unionHoleRadius V i ≤ val x (X-C (U.unionHoleCenter V i)) :=
    le_of_not_gt (hxD.2 i)
  obtain ⟨q,W,sourceIndex,hc,hr,hi,hh,hW⟩ := fc_exists_standardAffinoid_exact_finite_bounds
    x V.center V.radius (U.unionHoleCenter V) (U.unionHoleRadius V) hxV.1 hl
  refine ⟨q,W,sourceIndex,hc,hr,hi,hh,hW.trans (?_ : _ = U.carrier ∪ V.carrier)⟩
  convert hdomain using 1
  ext y
  simp only [outerClosedDisc,fcClosedLinearDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,not_lt]

/-- The exact union producer has ONLY ORIGINAL active holes; zero placeholders cannot survive its positive-radius output. -/
theorem exists_union_original_of_radius_le (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q), W.center = V.center ∧ W.radius = V.radius ∧
      W.carrier = U.carrier ∪ V.carrier ∧ ∀ j,
        (∃ i, W.holeCenter j = U.holeCenter i ∧ W.holeRadius j = U.holeRadius i) ∨
          (∃ i, W.holeCenter j = V.holeCenter i ∧ W.holeRadius j = V.holeRadius i) := by
  obtain ⟨q,W,s,hc,hr,_,hh,hW⟩ := U.exists_union_of_radius_le V hR x hxU hxV
  refine ⟨q,W,hc,hr,hW,fun j => ?_⟩
  have hp : 0 < U.unionHoleRadius V (s j) := (W.holeRadius_pos j).trans_eq (hh j).2
  have hs := U.unionHole_active_original V (s j) hp
  rw [(hh j).1,(hh j).2]
  exact hs

/-- ANY actual overlapping union is a literal original standard affinoid with its ORIGINAL maximum outer radius and holes. -/
theorem exists_union_of_nonempty (hne : (U.carrier ∩ V.carrier).Nonempty) :
    ∃ (q : ℕ) (W : FCStandardAffinoid w q),
      (W.center = U.center ∨ W.center = V.center) ∧ W.radius = max U.radius V.radius ∧
      W.carrier = U.carrier ∪ V.carrier ∧ ∀ j,
        (∃ i, W.holeCenter j = U.holeCenter i ∧ W.holeRadius j = U.holeRadius i) ∨
          (∃ i, W.holeCenter j = V.holeCenter i ∧ W.holeRadius j = V.holeRadius i) := by
  obtain ⟨x,hxU,hxV⟩ := hne
  rcases le_total U.radius V.radius with hR | hR
  · obtain ⟨q,W,hc,hr,hW,hh⟩ := U.exists_union_original_of_radius_le V hR x hxU hxV
    exact ⟨q,W,Or.inr hc,hr.trans (max_eq_right hR).symm,hW,hh⟩
  · obtain ⟨q,W,hc,hr,hW,hh⟩ := V.exists_union_original_of_radius_le U hR x hxV hxU
    exact ⟨q,W,Or.inl hc,hr.trans (max_eq_left hR).symm,hW.trans (Set.union_comm _ _),fun j => (hh j).symm⟩
end FCStandardAffinoid
end EnvelopeProperty.Berkovich.RelativeSpectrum
