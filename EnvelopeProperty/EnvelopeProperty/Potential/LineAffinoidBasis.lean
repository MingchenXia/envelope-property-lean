import EnvelopeProperty.Potential.LineBranchEnds
import EnvelopeProperty.Potential.LineStandardAffinoid
import Mathlib.Order.Preorder.Finite

/-! # Actual standard-affinoid neighbourhoods of every original line point -/
open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

/-- The full original line topology is induced by its actual linear values. -/
theorem fc_isInducing_linearCoordinates :
    IsInducing (fun x : RelativeSpectrum w K[X] => fun a : K => val x (X-C a)) := by
  apply isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm
  · rw [← tendsto_iff_comap]
    exact (continuous_pi fun a => continuous_val_apply (X-C a)).tendsto x
  · have h := (fc_tendsto_iff_linear (w := w) (g := id) (x := x)).mpr
      (tendsto_pi_nhds.mp tendsto_comap)
    simpa only [id_eq] using (tendsto_id'.mp h)

private theorem fc_exists_coordinate_interval (q : ℝ≥0) {V : Set ℝ≥0} (hV : V ∈ 𝓝 q) :
    ∃ l r : ℝ≥0, q < r ∧ (l = 0 ∨ l < q) ∧
      ∀ t : ℝ≥0, l ≤ t → t ≤ r → t ∈ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let δ : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hδ : 0 < δ := by change (0 : ℝ) < ε / 2; positivity
  refine ⟨q-δ,q+δ,lt_add_of_pos_right _ hδ,?_,?_⟩
  · by_cases hq : q = 0
    · simp [hq]
    · exact Or.inr (tsub_lt_self (pos_iff_ne_zero.mpr hq) hδ)
  · intro t hl hr
    apply hball
    rw [Metric.mem_ball,NNReal.dist_eq,abs_lt]
    have hu : (t : ℝ) ≤ (q : ℝ) + ε / 2 := by exact_mod_cast hr
    have hlo : (q : ℝ) - ε / 2 ≤ (t : ℝ) := by
      by_cases h : δ ≤ q
      · have hh : ((q-δ : ℝ≥0) : ℝ) = (q : ℝ) - ε / 2 := by
          rw [NNReal.coe_sub h]; rfl
        rw [← hh]
        exact_mod_cast hl
      · have hh : (q : ℝ) < ε / 2 := by exact_mod_cast lt_of_not_ge h
        linarith [t.2]
    constructor <;> linarith

/-- Every actual neighbourhood contains a finite closed box in original linear values. -/
theorem fc_exists_finite_linear_box (x : RelativeSpectrum w K[X])
    {N : Set (RelativeSpectrum w K[X])} (hN : N ∈ 𝓝 x) :
    ∃ (s : Finset K) (l r : K → ℝ≥0), s.Nonempty ∧
      (∀ a ∈ s, val x (X-C a) < r a ∧ (l a = 0 ∨ l a < val x (X-C a))) ∧
      {y : RelativeSpectrum w K[X] | ∀ a ∈ s, l a ≤ val y (X-C a) ∧ val y (X-C a) ≤ r a} ⊆ N := by
  classical
  rw [(fc_isInducing_linearCoordinates (w := w)).nhds_eq_comap x] at hN
  obtain ⟨V,hV,hVN⟩ := mem_comap.mp hN
  rw [nhds_pi,Filter.mem_pi'] at hV
  obtain ⟨s,t,ht,htV⟩ := hV
  choose l r hq using fun a : K => fc_exists_coordinate_interval (val x (X-C a)) (ht a)
  let l' : K → ℝ≥0 := fun a => if a ∈ s then l a else 0
  let r' : K → ℝ≥0 := fun a => if a ∈ s then r a else val x (X-C a)+1
  refine ⟨insert 0 s,l',r',Finset.insert_nonempty _ _,?_,?_⟩
  · intro a _
    by_cases ha : a ∈ s
    · simpa only [l',r',if_pos ha] using And.intro (hq a).1 (hq a).2.1
    · simp [l',r',ha]
  · intro y hy
    apply hVN
    apply htV
    intro a ha
    have ha' : a ∈ s := ha
    have hb := hy a (Finset.mem_insert_of_mem ha')
    simp only [l',r',if_pos ha'] at hb
    exact (hq a).2.2 _ hb.1 hb.2

omit [IsAlgClosed K] in
/-- Intersecting actual open discs are nested, including arbitrary real radii. -/
theorem fc_openDiscs_laminar (a b : K) (r s : ℝ≥0) :
    ({y : RelativeSpectrum w K[X] | val y (X-C a) < r} ⊆
      {y | val y (X-C b) < s}) ∨
    ({y : RelativeSpectrum w K[X] | val y (X-C b) < s} ⊆
      {y | val y (X-C a) < r}) ∨
    Disjoint {y : RelativeSpectrum w K[X] | val y (X-C a) < r}
      {y | val y (X-C b) < s} := by
  by_cases hd : Disjoint {y : RelativeSpectrum w K[X] | val y (X-C a) < r}
      {y | val y (X-C b) < s}
  · exact Or.inr (Or.inr hd)
  obtain ⟨z,hza,hzb⟩ := Set.not_disjoint_iff.mp hd
  rcases le_total r s with hrs | hsr
  · apply Or.inl
    have hab : w (a-b) < s :=
      (fc_center_distance_bound z a b).trans_lt (max_lt (hza.trans_le hrs) hzb)
    intro y hy
    exact (fc_linear_bound y a b).trans_lt (max_lt (hy.trans_le hrs) hab)
  · apply Or.inr ∘ Or.inl
    have hba : w (b-a) < r :=
      (fc_center_distance_bound z b a).trans_lt (max_lt (hzb.trans_le hsr) hza)
    intro y hy
    exact (fc_linear_bound y b a).trans_lt (max_lt (hy.trans_le hsr) hba)

/-- Maximal members of a finite laminar family form a disjoint subfamily with the same union. -/
theorem fc_disjoint_maximal_subfamily {X : Type*} (s : Finset (Set X))
    (hlam : ∀ A ∈ s, ∀ B ∈ s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) :
    ∃ t : Finset (Set X), t ⊆ s ∧
      (∀ A ∈ s, ∃ B ∈ t, A ⊆ B) ∧ (↑t : Set (Set X)).Pairwise Disjoint := by
  classical
  let t := s.filter (Maximal (· ∈ s))
  refine ⟨t,Finset.filter_subset _ _,?_,?_⟩
  · intro A hA
    obtain ⟨B,hAB,hB⟩ := s.exists_le_maximal hA
    exact ⟨B,Finset.mem_filter.mpr ⟨hB.1,hB⟩,hAB⟩
  · intro A hA B hB hne
    have hAm := (Finset.mem_filter.mp hA).2
    have hBm := (Finset.mem_filter.mp hB).2
    rcases hlam A hAm.1 B hBm.1 with h | h | h
    · exact False.elim (hne (Set.Subset.antisymm h (hAm.2 hBm.1 h)))
    · exact False.elim (hne (Set.Subset.antisymm (hBm.2 hAm.1 h) h))
    · exact h

omit [IsAlgClosed K] in
/-- Strict inequalities give an actual open neighbourhood inside the affinoid. -/
theorem FCStandardAffinoid.mem_interior_of_strict {m : ℕ} (U : FCStandardAffinoid w m)
    (x : RelativeSpectrum w K[X]) (ho : val x (X-C U.center) < U.radius)
    (hh : ∀ j, U.holeRadius j < val x (X-C (U.holeCenter j))) :
    x ∈ interior U.carrier := by
  let O : Set (RelativeSpectrum w K[X]) :=
    {y | val y (X-C U.center) < U.radius} ∩
      ⋂ j, {y | U.holeRadius j < val y (X-C (U.holeCenter j))}
  have hO : IsOpen O := (isOpen_lt (continuous_val_apply _) continuous_const).inter
    (isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_val_apply _))
  apply interior_maximal (t := O) (fun y hy => ?_) hO
  · exact ⟨ho,Set.mem_iInter.mpr hh⟩
  · exact ⟨hy.1.le,fun j => (Set.mem_iInter.mp hy.2 j).le⟩

omit [IsAlgClosed K] in
/-- An outer disc and finitely many strict lower bounds construct actual disjoint holes. -/
theorem fc_exists_standardAffinoid_for_finite_lower_bounds
    (x : RelativeSpectrum w K[X]) (a₀ : K) (R : ℝ≥0)
    (ho : val x (X-C a₀) < R) (s : Finset K) (l : K → ℝ≥0)
    (hl : ∀ a ∈ s, l a = 0 ∨ l a < val x (X-C a)) :
    ∃ (m : ℕ) (U : FCStandardAffinoid w m), x ∈ interior U.carrier ∧
      U.carrier ⊆ {y | val y (X-C a₀) ≤ R ∧ ∀ a ∈ s, l a ≤ val y (X-C a)} := by
  classical
  let H : K → Set (RelativeSpectrum w K[X]) := fun a => {y | val y (X-C a) < l a}
  let s' := s.filter fun a => 0 < l a ∧ w (a-a₀) ≤ R
  let S := s'.image H
  have hlam : ∀ A ∈ S, ∀ B ∈ S, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    intro A hA B hB
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
    exact fc_openDiscs_laminar a b (l a) (l b)
  obtain ⟨T,hTS,hcover,hdisj⟩ := fc_disjoint_maximal_subfamily S hlam
  let I := {B : Set (RelativeSpectrum w K[X]) // B ∈ T}
  let : Fintype I := (T.finite_toSet).fintype
  choose c hc hceq using fun B : I => Finset.mem_image.mp (hTS B.2)
  have hcp (B : I) : 0 < l (c B) ∧ w (c B-a₀) ≤ R := (Finset.mem_filter.mp (hc B)).2
  have hcl (B : I) : l (c B) < val x (X-C (c B)) := by
    rcases hl (c B) (Finset.mem_filter.mp (hc B)).1 with h | h
    · exact False.elim ((hcp B).1.ne' h)
    · exact h
  have hsym (a : K) : w (a₀-a) = w (a-a₀) := by
    rw [show a₀-a = -(a-a₀) by ring,Valuation.map_neg]
  have hcr (B : I) : l (c B) ≤ R := (hcl B).le.trans
    ((fc_linear_bound x a₀ (c B)).trans (max_le ho.le (by rw [hsym]; exact (hcp B).2)))
  let e := (Fintype.equivFin I).symm
  let U : FCStandardAffinoid w (Fintype.card I) := {
    center := a₀
    radius := R
    holeCenter := fun j => c (e j)
    holeRadius := fun j => l (c (e j))
    holeRadius_pos := fun j => (hcp (e j)).1
    holeRadius_le := fun j => hcr (e j)
    holeCenter_le := fun j => (hcp (e j)).2
    holes_disjoint := by
      intro j k hjk
      have hne : (e j).1 ≠ (e k).1 := fun heq => hjk (e.injective (Subtype.ext heq))
      have hd := hdisj (e j).2 (e k).2 hne
      simpa only [← hceq (e j),← hceq (e k)] using hd }
  refine ⟨Fintype.card I,U,U.mem_interior_of_strict x ho (fun j => hcl (e j)),?_⟩
  intro y hy
  refine ⟨hy.1,?_⟩
  intro a ha
  by_cases hl0 : l a = 0
  · rw [hl0]
    exact zero_le
  have hla : l a < val x (X-C a) := (hl a ha).resolve_left hl0
  by_cases hcen : w (a-a₀) ≤ R
  · have has' : a ∈ s' := Finset.mem_filter.mpr ⟨ha,pos_iff_ne_zero.mpr hl0,hcen⟩
    obtain ⟨B,hB,hAB⟩ := hcover (H a) (Finset.mem_image_of_mem H has')
    let i : I := ⟨B,hB⟩
    obtain ⟨j,hj⟩ := e.surjective i
    apply le_of_not_gt
    intro hbad
    have hBy : y ∈ B := hAB hbad
    have hcj : H (c (e j)) = B := (hceq (e j)).trans (congrArg Subtype.val hj)
    rw [← hcj] at hBy
    exact not_lt_of_ge (hy.2 j) hBy
  · have hdist : R < w (a₀-a) := by rw [hsym]; exact lt_of_not_ge hcen
    have hxeq : val x (X-C a) = w (a₀-a) := by
      rw [fc_linear_value_eq_max x a₀ a (ne_of_lt (ho.trans hdist)),
        max_eq_right (ho.le.trans hdist.le)]
    have hyeq : val y (X-C a) = w (a₀-a) := by
      rw [fc_linear_value_eq_max y a₀ a (ne_of_lt (hy.1.trans_lt hdist)),
        max_eq_right (hy.1.trans hdist.le)]
    rw [hyeq,← hxeq]
    exact hla.le

/-- The actual closed carrier can be chosen inside every neighbourhood of every point. -/
theorem fc_exists_standardAffinoid_nhds (x : RelativeSpectrum w K[X])
    {N : Set (RelativeSpectrum w K[X])} (hN : N ∈ 𝓝 x) :
    ∃ (m : ℕ) (U : FCStandardAffinoid w m), x ∈ interior U.carrier ∧ U.carrier ⊆ N := by
  obtain ⟨s,l,r,hs,hbounds,hbox⟩ := fc_exists_finite_linear_box x hN
  obtain ⟨a₀,ha₀,hmin⟩ := s.exists_min_image r hs
  obtain ⟨m,U,hx,hU⟩ := fc_exists_standardAffinoid_for_finite_lower_bounds
    x a₀ (r a₀) (hbounds a₀ ha₀).1 s l (fun a ha => (hbounds a ha).2)
  refine ⟨m,U,hx,fun y hy => hbox ?_⟩
  intro a ha
  have hyv := hU hy
  refine ⟨hyv.2 a ha,?_⟩
  have hcent : w (a₀-a) ≤ r a := (fc_center_distance_bound x a₀ a).trans
    (max_le (((hbounds a₀ ha₀).1.le).trans (hmin a ha)) (hbounds a ha).1.le)
  exact (fc_linear_bound y a₀ a).trans
    (max_le (hyv.1.trans (hmin a ha)) hcent)

/-- Actual standard-affinoid interiors give the entire neighbourhood filter. -/
theorem fc_nhds_hasBasis_standardAffinoid (x : RelativeSpectrum w K[X]) :
    (𝓝 x).HasBasis
      (fun p : Σ m, FCStandardAffinoid w m => x ∈ interior p.2.carrier)
      (fun p => interior p.2.carrier) := by
  constructor
  intro N
  constructor
  · intro hN
    obtain ⟨m,U,hx,hU⟩ := fc_exists_standardAffinoid_nhds x hN
    exact ⟨⟨m,U⟩,hx,interior_subset.trans hU⟩
  · rintro ⟨⟨m,U⟩,hx,hU⟩
    exact mem_of_superset (isOpen_interior.mem_nhds hx) hU
end EnvelopeProperty.Berkovich.RelativeSpectrum
