import EnvelopeProperty.Potential.LineAffinoidBasis

/-! # Exact original finite-hole domains and laminar disc geometry -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The actual original closed linear disc. -/
def fcClosedLinearDisc (a : K) (R : ℝ≥0) : Set (RelativeSpectrum w K[X]) :=
  {x | val x (X-C a) ≤ R}

/-- The actual original OPEN linear disc; strictness is retained in every pruning argument. -/
def fcOpenLinearDisc (a : K) (r : ℝ≥0) : Set (RelativeSpectrum w K[X]) :=
  {x | val x (X-C a) < r}

theorem fc_closedLinearDisc_subset (a b : K) (R S : ℝ≥0)
    (hR : R ≤ S) (hab : w (a-b) ≤ S) : fcClosedLinearDisc (w := w) a R ⊆ fcClosedLinearDisc b S := by
  intro x hx
  exact (fc_linear_bound x a b).trans (max_le (hx.trans hR) hab)

/-- An ACTUAL common point orders the whole original outer discs by their original radii. -/
theorem fc_closedLinearDisc_subset_of_common (a b : K) (R S : ℝ≥0)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ fcClosedLinearDisc a R) (hy : x ∈ fcClosedLinearDisc b S)
    (hR : R ≤ S) : fcClosedLinearDisc (w := w) a R ⊆ fcClosedLinearDisc b S := by
  exact fc_closedLinearDisc_subset a b R S hR
    ((fc_center_distance_bound x a b).trans (max_le (hx.trans hR) hy))

/-- Every original lower bound with center outside the outer disc is constant on that WHOLE actual disc. -/
theorem fc_linear_value_on_disc_of_center_outside (a b : K) (R : ℝ≥0)
    (hab : R < w (a-b)) (x : RelativeSpectrum w K[X]) (hx : x ∈ fcClosedLinearDisc a R) :
    val x (X-C b) = w (a-b) := by
  rw [fc_linear_value_eq_max x a b (ne_of_lt (hx.trans_lt hab)),max_eq_right (hx.trans hab.le)]

/-- An actual point outside the OPEN hole rules out an enclosing hole, leaving only inside or disjoint. -/
theorem fc_openLinearDisc_inside_or_disjoint (a₀ a : K) (R r : ℝ≥0)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ fcClosedLinearDisc a₀ R)
    (hl : r ≤ val x (X-C a)) :
    (r ≤ R ∧ w (a-a₀) ≤ R ∧ fcOpenLinearDisc (w := w) a r ⊆ fcClosedLinearDisc a₀ R) ∨
      Disjoint (fcOpenLinearDisc (w := w) a r) (fcClosedLinearDisc a₀ R) := by
  have hsym : w (a₀-a) = w (a-a₀) := by rw [show a₀-a = -(a-a₀) by ring,Valuation.map_neg]
  by_cases hc : w (a-a₀) ≤ R
  · have hr : r ≤ R := hl.trans ((fc_linear_bound x a₀ a).trans (max_le hx (by rwa [hsym])))
    refine Or.inl ⟨hr,hc,?_⟩
    intro y hy
    exact (fc_linear_bound y a a₀).trans (max_le (hy.le.trans hr) hc)
  · apply Or.inr
    have hdist : R < w (a₀-a) := by rw [hsym]; exact lt_of_not_ge hc
    apply Set.disjoint_left.mpr
    intro y hy hyD
    have hxeq := fc_linear_value_on_disc_of_center_outside a₀ a R hdist x hx
    have hyeq := fc_linear_value_on_disc_of_center_outside a₀ a R hdist y hyD
    exact not_lt_of_ge (hyeq.symm ▸ hxeq ▸ hl) hy

/-- NONSTRICT actual finite lower bounds construct an EXACT original carrier, retaining injectively chosen ORIGINAL holes. -/
theorem fc_exists_standardAffinoid_exact_finite_bounds {ι : Type*} [Fintype ι]
    (x : RelativeSpectrum w K[X]) (a₀ : K) (R : ℝ≥0) (a : ι → K) (r : ι → ℝ≥0)
    (hx : val x (X-C a₀) ≤ R) (hl : ∀ i, r i ≤ val x (X-C (a i))) :
    ∃ (q : ℕ) (U : FCStandardAffinoid w q) (sourceIndex : Fin q → ι),
      U.center = a₀ ∧ U.radius = R ∧ Function.Injective sourceIndex ∧
      (∀ j, U.holeCenter j = a (sourceIndex j) ∧ U.holeRadius j = r (sourceIndex j)) ∧
      U.carrier = {y | val y (X-C a₀) ≤ R ∧ ∀ i, r i ≤ val y (X-C (a i))} := by
  classical
  let H : ι → Set (RelativeSpectrum w K[X]) := fun i => fcOpenLinearDisc (a i) (r i)
  let s := Finset.univ.filter fun i => 0 < r i ∧ w (a i-a₀) ≤ R
  let S := s.image H
  have hlam : ∀ A ∈ S, ∀ B ∈ S, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    intro A hA B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    exact fc_openDiscs_laminar _ _ _ _
  obtain ⟨T,hTS,hcover,hdisj⟩ := fc_disjoint_maximal_subfamily S hlam
  let I := {B : Set (RelativeSpectrum w K[X]) // B ∈ T}
  let : Fintype I := T.finite_toSet.fintype
  choose c hc hceq using fun B : I => Finset.mem_image.mp (hTS B.2)
  have hcp (B : I) : 0 < r (c B) ∧ w (a (c B)-a₀) ≤ R := (Finset.mem_filter.mp (hc B)).2
  have hsym (i : ι) : w (a₀-a i) = w (a i-a₀) := by
    rw [show a₀-a i = -(a i-a₀) by ring,Valuation.map_neg]
  have hcr (B : I) : r (c B) ≤ R := (hl (c B)).trans
    ((fc_linear_bound x a₀ (a (c B))).trans (max_le hx (by rw [hsym]; exact (hcp B).2)))
  let e := (Fintype.equivFin I).symm
  let U : FCStandardAffinoid w (Fintype.card I) := {
    center := a₀
    radius := R
    holeCenter := fun j => a (c (e j))
    holeRadius := fun j => r (c (e j))
    holeRadius_pos := fun j => (hcp (e j)).1
    holeRadius_le := fun j => hcr (e j)
    holeCenter_le := fun j => (hcp (e j)).2
    holes_disjoint := by
      intro j k hjk
      have hne : (e j).1 ≠ (e k).1 := fun heq => hjk (e.injective (Subtype.ext heq))
      have hd := hdisj (e j).2 (e k).2 hne
      change Disjoint (H (c (e j))) (H (c (e k)))
      rw [hceq,hceq]
      exact hd }
  refine ⟨Fintype.card I,U,fun j => c (e j),rfl,rfl,?_,fun _ => ⟨rfl,rfl⟩,?_⟩
  · intro j k hjk
    apply e.injective
    apply Subtype.ext
    exact (hceq (e j)).symm.trans ((congrArg H hjk).trans (hceq (e k)))
  · ext y
    constructor
    · intro hy
      refine ⟨hy.1,fun i => ?_⟩
      by_cases hr0 : r i = 0
      · rw [hr0]
        exact zero_le
      by_cases hcen : w (a i-a₀) ≤ R
      · have his : i ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,pos_iff_ne_zero.mpr hr0,hcen⟩
        obtain ⟨B,hB,hAB⟩ := hcover (H i) (Finset.mem_image_of_mem H his)
        let b : I := ⟨B,hB⟩
        obtain ⟨j,hj⟩ := e.surjective b
        apply le_of_not_gt
        intro hbad
        have hBy : y ∈ B := hAB hbad
        have hcj : H (c (e j)) = B := (hceq (e j)).trans (congrArg Subtype.val hj)
        rw [← hcj] at hBy
        exact not_lt_of_ge (hy.2 j) hBy
      · have hd : R < w (a₀-a i) := by rw [hsym]; exact lt_of_not_ge hcen
        have hxeq := fc_linear_value_on_disc_of_center_outside a₀ (a i) R hd x hx
        have hyeq := fc_linear_value_on_disc_of_center_outside a₀ (a i) R hd y hy.1
        rw [hyeq,← hxeq]
        exact hl i
    · intro hy
      exact ⟨hy.1,fun j => hy.2 (c (e j))⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum
