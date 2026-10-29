import EnvelopeProperty.Potential.LineAffinoidBasis
import EnvelopeProperty.Potential.LineDirichlet
import Mathlib.Order.Interval.Set.Infinite

/-! # Constructed separated standard affinoids and their strict core -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- A geometric property of a chosen presentation, never imposed on all standard affinoids. -/
structure IsSeparated : Prop where
  holeCenter_lt : ∀ j, w (U.holeCenter j-U.center) < U.radius
  holeRadius_lt_distance : ∀ i j, i ≠ j →
    U.holeRadius i < w (U.holeCenter i-U.holeCenter j)

/-- The actual points satisfying the original outer and hole inequalities strictly. -/
def strictCore : Set (RelativeSpectrum w K[X]) :=
  {x | val x (X-C U.center) < U.radius ∧
    ∀ j, U.holeRadius j < val x (X-C (U.holeCenter j))}

theorem strictCore_subset_interior : U.strictCore ⊆ interior U.carrier :=
  fun x hx => U.mem_interior_of_strict x hx.1 hx.2

theorem isOpen_strictCore : IsOpen U.strictCore := by
  have he : U.strictCore = {x | val x (X-C U.center) < U.radius} ∩
      ⋂ j, {x | U.holeRadius j < val x (X-C (U.holeCenter j))} := by
    ext x
    simp only [strictCore,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  rw [he]
  exact (isOpen_lt (continuous_val_apply _) continuous_const).inter
    (isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_val_apply _))

end FCStandardAffinoid

private theorem fc_exists_between_avoiding (l r : ℝ≥0) (hlr : l < r) (s : Finset ℝ≥0) :
    ∃ t, l < t ∧ t < r ∧ t ∉ s := by
  obtain ⟨t,ht,hts⟩ := (Set.Ioo_infinite hlr).exists_notMem_finset s
  exact ⟨t,ht.1,ht.2,hts⟩

private theorem fc_exists_separated_for_lower_bounds
    (x : RelativeSpectrum w K[X]) (a₀ : K) (R : ℝ≥0)
    (ho : val x (X-C a₀) < R) (s : Finset K) (l : K → ℝ≥0)
    (hl : ∀ a ∈ s, l a = 0 ∨ l a < val x (X-C a))
    (hR : ∀ a ∈ s, w (a-a₀) ≠ R)
    (hd : ∀ a ∈ s, 0 < l a → ∀ b ∈ s, l a ≠ w (a-b)) :
    ∃ (m : ℕ) (U : FCStandardAffinoid w m), U.IsSeparated ∧ x ∈ U.strictCore ∧
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
  have hcs (B : I) : c B ∈ s := (Finset.mem_filter.mp (hc B)).1
  have hcp (B : I) : 0 < l (c B) ∧ w (c B-a₀) ≤ R := (Finset.mem_filter.mp (hc B)).2
  have hcl (B : I) : l (c B) < val x (X-C (c B)) := by
    rcases hl (c B) (hcs B) with h | h
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
      have he := hdisj (e j).2 (e k).2 hne
      simpa only [← hceq (e j),← hceq (e k)] using he }
  have hsep : U.IsSeparated := by
    constructor
    · intro j
      exact lt_of_le_of_ne (hcp (e j)).2 (hR _ (hcs (e j)))
    · intro i j hij
      have hle : U.holeRadius i ≤ w (U.holeCenter i-U.holeCenter j) := by
        have h := U.holeRadius_le_center_distance j i hij.symm
        rwa [show U.holeCenter j-U.holeCenter i = -(U.holeCenter i-U.holeCenter j) by ring,
          Valuation.map_neg] at h
      exact lt_of_le_of_ne hle (hd _ (hcs (e i)) (hcp (e i)).1 _ (hcs (e j)))
  refine ⟨Fintype.card I,U,hsep,⟨ho,fun j => hcl (e j)⟩,?_⟩
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

variable [IsAlgClosed K]

/-- Separated presentations with a strict-core base point are derived from every actual neighbourhood. -/
theorem fc_exists_separated_standardAffinoid_nhds (x : RelativeSpectrum w K[X])
    {N : Set (RelativeSpectrum w K[X])} (hN : N ∈ 𝓝 x) :
    ∃ (m : ℕ) (U : FCStandardAffinoid w m), U.IsSeparated ∧ x ∈ U.strictCore ∧ U.carrier ⊆ N := by
  classical
  obtain ⟨s,l,r,hs,hbounds,hbox⟩ := fc_exists_finite_linear_box x hN
  obtain ⟨a₀,ha₀,hmin⟩ := s.exists_min_image r hs
  obtain ⟨R,hxR,hRr,hRavoid⟩ := fc_exists_between_avoiding
    (val x (X-C a₀)) (r a₀) (hbounds a₀ ha₀).1 (s.image fun a => w (a-a₀))
  let D (a : K) := s.image fun b => w (a-b)
  have hex : ∀ a ∈ s, ∃ L : ℝ≥0, l a ≤ L ∧ (L = 0 ∨ L < val x (X-C a)) ∧
      (0 < L → ∀ b ∈ s, L ≠ w (a-b)) := by
    intro a ha
    by_cases hl0 : l a = 0
    · exact ⟨0,by rw [hl0],Or.inl rfl,by simp⟩
    · obtain ⟨L,hlL,hLx,hLD⟩ := fc_exists_between_avoiding (l a)
        (val x (X-C a)) ((hbounds a ha).2.resolve_left hl0) (D a)
      exact ⟨L,hlL.le,Or.inr hLx,fun _ b hb he => hLD (Finset.mem_image.mpr ⟨b,hb,he.symm⟩)⟩
  choose L hL using hex
  obtain ⟨m,U,hsep,hx,hU⟩ := fc_exists_separated_for_lower_bounds x a₀ R hxR s
    (fun a => if ha : a ∈ s then L a ha else 0)
    (by intro a ha; simpa only [dif_pos ha] using (hL a ha).2.1)
    (by intro a ha he; exact hRavoid (Finset.mem_image.mpr ⟨a,ha,he⟩))
    (by intro a ha hpos b hb
        have hpos' : 0 < L a ha := by simpa only [dif_pos ha] using hpos
        simpa only [dif_pos ha] using (hL a ha).2.2 hpos' b hb)
  refine ⟨m,U,hsep,hx,fun y hy => hbox ?_⟩
  intro a ha
  have hyv := hU hy
  have hlower := hyv.2 a ha
  simp only [dif_pos ha] at hlower
  refine ⟨(hL a ha).1.trans hlower,?_⟩
  have hcent : w (a₀-a) ≤ r a := (fc_center_distance_bound x a₀ a).trans
    (max_le (((hbounds a₀ ha₀).1.le).trans (hmin a ha)) (hbounds a ha).1.le)
  exact (fc_linear_bound y a₀ a).trans
    (max_le ((hyv.1.trans hRr.le).trans (hmin a ha)) hcent)

end EnvelopeProperty.Berkovich.RelativeSpectrum
