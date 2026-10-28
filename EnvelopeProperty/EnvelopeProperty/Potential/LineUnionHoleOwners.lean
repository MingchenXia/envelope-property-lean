import EnvelopeProperty.Potential.LineUnionHoleIncidence
import EnvelopeProperty.Potential.LineOpenHoleContainment

/-! # Computed ORIGINAL ownership and exact actual image of union holes -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)

/-- The smaller ORIGINAL hole owns an intersection; equality consistently uses the ORIGINAL U index. -/
def unionHoleOwner : Fin n ⊕ (Fin m × Fin n) → Fin m ⊕ Fin n
  | Sum.inl j => Sum.inr j
  | Sum.inr p => if U.holeRadius p.1 ≤ V.holeRadius p.2 then Sum.inl p.1 else Sum.inr p.2

theorem unionHole_inl_pos_iff (j : Fin n) :
    0 < U.unionHoleRadius V (Sum.inl j) ↔ Disjoint (V.holeOpenDisc j) U.outerClosedDisc := by
  classical
  by_cases hd : Disjoint (V.holeOpenDisc j) U.outerClosedDisc
  · simp only [unionHoleRadius,if_pos hd,V.holeRadius_pos j,true_iff]
    exact hd
  · simp only [unionHoleRadius,if_neg hd,lt_self_iff_false,false_iff]
    exact hd

theorem unionHole_inr_pos_iff (i : Fin m) (j : Fin n) :
    0 < U.unionHoleRadius V (Sum.inr (i,j)) ↔ ¬Disjoint (U.holeOpenDisc i) (V.holeOpenDisc j) := by
  classical
  change 0 < (if Disjoint (U.holeOpenDisc i) (V.holeOpenDisc j) then 0 else
    min (U.holeRadius i) (V.holeRadius j)) ↔ _
  split_ifs with hd
  · simp only [lt_self_iff_false,false_iff,not_not]
    exact hd
  · simp only [lt_min_iff,U.holeRadius_pos i,V.holeRadius_pos j,and_self, true_iff]
    exact hd

/-- Every active computed owner retains the EXACT ORIGINAL centre and radius. -/
theorem unionHoleOwner_active_data (i : Fin n ⊕ (Fin m × Fin n)) (hp : 0 < U.unionHoleRadius V i) :
    U.unionHoleCenter V i = U.combinedHoleCenter V (U.unionHoleOwner V i) ∧
      U.unionHoleRadius V i = U.combinedHoleRadius V (U.unionHoleOwner V i) := by
  classical
  cases i with
  | inl j =>
    have hd := (U.unionHole_inl_pos_iff V j).mp hp
    simp only [unionHoleCenter,unionHoleOwner,combinedHoleCenter,combinedHoleRadius,Sum.elim_inr,
      unionHoleRadius,if_pos hd,and_self]
  | inr p =>
    have hd := (U.unionHole_inr_pos_iff V p.1 p.2).mp hp
    change ¬Disjoint (fcOpenLinearDisc (w := w) (U.holeCenter p.1) (U.holeRadius p.1))
      (fcOpenLinearDisc (V.holeCenter p.2) (V.holeRadius p.2)) at hd
    by_cases hrs : U.holeRadius p.1 ≤ V.holeRadius p.2
    · simp only [unionHoleCenter,unionHoleRadius,unionHoleOwner,fcOpenIntersectionCenter,fcOpenIntersectionRadius,
        if_pos hrs,if_neg hd,min_eq_left hrs,combinedHoleCenter,combinedHoleRadius,Sum.elim_inl,and_self]
    · simp only [unionHoleCenter,unionHoleRadius,unionHoleOwner,fcOpenIntersectionCenter,fcOpenIntersectionRadius,
        if_neg hrs,if_neg hd,min_eq_right (le_of_not_ge hrs),combinedHoleCenter,combinedHoleRadius,Sum.elim_inr,and_self]

/-- DIFFERENT active missing-hole entries have DIFFERENT computed ORIGINAL owners. -/
theorem unionHoleOwner_injOn_active : Set.InjOn (U.unionHoleOwner V) {i | 0 < U.unionHoleRadius V i} := by
  intro i hi j hj he
  by_contra hne
  have hdi := U.unionHoleOwner_active_data V i hi
  have hdj := U.unionHoleOwner_active_data V j hj
  have hc : U.unionHoleCenter V i = U.unionHoleCenter V j := by rw [hdi.1,hdj.1,he]
  have hr : U.unionHoleRadius V i = U.unionHoleRadius V j := by rw [hdi.2,hdj.2,he]
  have hz : centeredGauss (self w) (U.unionHoleCenter V i) 0 ∈
      fcOpenLinearDisc (w := w) (U.unionHoleCenter V i) (U.unionHoleRadius V i) := by
    simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using hi
  have hzj : centeredGauss (self w) (U.unionHoleCenter V i) 0 ∈
      fcOpenLinearDisc (w := w) (U.unionHoleCenter V j) (U.unionHoleRadius V j) := by simpa only [← hc,← hr] using hz
  exact Set.disjoint_left.mp (U.unionHole_family_disjoint V hne) hz hzj

/-- The exact ORIGINAL U-owner image is actual open-hole containment in an ORIGINAL V-hole. -/
theorem exists_active_union_owner_inl_iff (i : Fin m) :
    (∃ k, 0 < U.unionHoleRadius V k ∧ U.unionHoleOwner V k = Sum.inl i) ↔
      ∃ j, U.holeOpenDisc i ⊆ V.holeOpenDisc j := by
  constructor
  · rintro ⟨k,hk,ho⟩
    cases k with
    | inl j => simp only [unionHoleOwner,Sum.inr_ne_inl] at ho
    | inr p =>
      by_cases hrs : U.holeRadius p.1 ≤ V.holeRadius p.2
      · have hi : p.1 = i := Sum.inl.inj (by simpa only [unionHoleOwner,if_pos hrs] using ho)
        obtain ⟨z,hzU,hzV⟩ := Set.not_disjoint_iff.mp ((U.unionHole_inr_pos_iff V p.1 p.2).mp hk)
        exact ⟨p.2,hi ▸ fc_openLinearDisc_subset_of_common _ _ _ _ z hzU hzV hrs⟩
      · simp only [unionHoleOwner,if_neg hrs,Sum.inr_ne_inl] at ho
  · rintro ⟨j,hsub⟩
    have hrs := fc_openLinearDisc_radius_le_of_subset _ _ _ _ hsub
    have hz : centeredGauss (self w) (U.holeCenter i) 0 ∈ U.holeOpenDisc i := by
      simpa only [holeOpenDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using U.holeRadius_pos i
    have hd : ¬Disjoint (U.holeOpenDisc i) (V.holeOpenDisc j) := fun h => Set.disjoint_left.mp h hz (hsub hz)
    exact ⟨Sum.inr (i,j),(U.unionHole_inr_pos_iff V i j).mpr hd,by simp only [unionHoleOwner,if_pos hrs]⟩

/-- The exact ORIGINAL V-owner image uses outside holes or STRICTLY smaller original V-holes; equal radii belong to U. -/
theorem exists_active_union_owner_inr_iff (j : Fin n) :
    (∃ k, 0 < U.unionHoleRadius V k ∧ U.unionHoleOwner V k = Sum.inr j) ↔
      Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨
        ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i ∧ V.holeRadius j < U.holeRadius i := by
  constructor
  · rintro ⟨k,hk,ho⟩
    cases k with
    | inl j' =>
      have hj : j' = j := Sum.inr.inj ho
      exact Or.inl (hj ▸ (U.unionHole_inl_pos_iff V j').mp hk)
    | inr p =>
      by_cases hrs : U.holeRadius p.1 ≤ V.holeRadius p.2
      · simp only [unionHoleOwner,if_pos hrs,Sum.inl_ne_inr] at ho
      · have hj : p.2 = j := Sum.inr.inj (by simpa only [unionHoleOwner,if_neg hrs] using ho)
        obtain ⟨z,hzU,hzV⟩ := Set.not_disjoint_iff.mp ((U.unionHole_inr_pos_iff V p.1 p.2).mp hk)
        have hlt := lt_of_not_ge hrs
        exact Or.inr ⟨p.1,hj ▸ fc_openLinearDisc_subset_of_common _ _ _ _ z hzV hzU hlt.le,hj ▸ hlt⟩
  · rintro (hd | ⟨i,hsub,hlt⟩)
    · exact ⟨Sum.inl j,(U.unionHole_inl_pos_iff V j).mpr hd,rfl⟩
    · have hz : centeredGauss (self w) (V.holeCenter j) 0 ∈ V.holeOpenDisc j := by
        simpa only [holeOpenDisc,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using V.holeRadius_pos j
      have hd : ¬Disjoint (U.holeOpenDisc i) (V.holeOpenDisc j) := fun h => Set.disjoint_left.mp h (hsub hz) hz
      exact ⟨Sum.inr (i,j),(U.unionHole_inr_pos_iff V i j).mpr hd,by simp only [unionHoleOwner,if_neg (not_le_of_gt hlt)]⟩

/-- EVERY actual ordered overlapping union is produced with INJECTIVE ORIGINAL hole owners and their EXACT actual minimal-hole image. -/
theorem exists_union_with_original_owners (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) :
    ∃ (q : ℕ) (B : FCStandardAffinoid w q) (o : Fin q → Fin m ⊕ Fin n),
      B.center = V.center ∧ B.radius = V.radius ∧ B.carrier = U.carrier ∪ V.carrier ∧ Function.Injective o ∧
      (∀ j, B.holeCenter j = U.combinedHoleCenter V (o j) ∧ B.holeRadius j = U.combinedHoleRadius V (o j)) ∧
      (∀ i, (∃ j, o j = Sum.inl i) ↔ ∃ k, U.holeOpenDisc i ⊆ V.holeOpenDisc k) ∧
      (∀ j, (∃ k, o k = Sum.inr j) ↔ Disjoint (V.holeOpenDisc j) U.outerClosedDisc ∨
        ∃ i, V.holeOpenDisc j ⊆ U.holeOpenDisc i ∧ V.holeRadius j < U.holeRadius i) := by
  obtain ⟨q,B,s,hc,hr,hi,hh,hB,hs⟩ := U.exists_union_with_all_active_holes V hR x hxU hxV
  have hpos (j : Fin q) : 0 < U.unionHoleRadius V (s j) := (B.holeRadius_pos j).trans_eq (hh j).2
  have himage (a : Fin m ⊕ Fin n) :
      (∃ j, U.unionHoleOwner V (s j) = a) ↔ ∃ i, 0 < U.unionHoleRadius V i ∧ U.unionHoleOwner V i = a := by
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨s j,hpos j,hj⟩
    · rintro ⟨i,hpi,hoi⟩
      obtain ⟨j,hj,_⟩ := hs i hpi
      exact ⟨j,by rw [hj,hoi]⟩
  refine ⟨q,B,fun j => U.unionHoleOwner V (s j),hc,hr,hB,?_,?_,?_,?_⟩
  · intro j k hjk
    exact hi (U.unionHoleOwner_injOn_active V (hpos j) (hpos k) hjk)
  · intro j
    have hd := U.unionHoleOwner_active_data V (s j) (hpos j)
    exact ⟨(hh j).1.trans hd.1,(hh j).2.trans hd.2⟩
  · intro i
    exact (himage (Sum.inl i)).trans (U.exists_active_union_owner_inl_iff V i)
  · intro j
    exact (himage (Sum.inr j)).trans (U.exists_active_union_owner_inr_iff V j)
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
