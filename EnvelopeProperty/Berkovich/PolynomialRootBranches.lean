/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumDiscComponents

/-! # Original polynomial root multiplicities in genuinely constructed Gauss-disc branches -/
open scoped NNReal Polynomial
open Polynomial Set
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] (v : Valuation K ℝ≥0)

/-- The LITERAL original root multiset inside the original closed coordinate disc. -/
def insideRoots (r : ℝ≥0) (p : K[X]) : Multiset K := p.roots.filter (fun b => v b ≤ r)

/-- Each ORIGINAL retained root, with its multiplicity, maps to its actual branch SET. -/
def rootBranchMultiset (r : ℝ≥0) (p : K[X]) : Multiset (Set (CoordinateDisc (A := K) v r)) :=
  (insideRoots v r p).map (discBranch v r)

/-- The actual finite image branch SETS, without erasing root multiplicities from the multiset. -/
def rootBranches (r : ℝ≥0) (p : K[X]) : Finset (Set (CoordinateDisc (A := K) v r)) := by
  classical
  exact (rootBranchMultiset v r p).toFinset

/-- The true original root multiplicity on an actual branch set. -/
def branchRootCount (r : ℝ≥0) (p : K[X]) (B : Set (CoordinateDisc (A := K) v r)) : ℕ := by
  classical
  exact (rootBranchMultiset v r p).count B

/-- This counts the original filtered ROOT MULTISET, including every repeated root. -/
theorem branchRootCount_eq_card_filter (r : ℝ≥0) (p : K[X]) (B : Set (CoordinateDisc (A := K) v r)) :
    branchRootCount v r p B = (p.roots.filter (fun b => v b ≤ r ∧ discBranch v r b = B)).card := by
  classical
  rw [branchRootCount, rootBranchMultiset, Multiset.count_map, insideRoots, Multiset.filter_filter]
  congr 1
  apply Multiset.filter_congr
  intro b _
  simp only [and_comm, eq_comm]

/-- Every original root contributes to exactly one actual finite-image branch fibre. -/
theorem sum_branchRootCount (r : ℝ≥0) (p : K[X]) (S : Finset (Set (CoordinateDisc (A := K) v r)))
    (hS : rootBranches v r p ⊆ S) :
    ∑ B ∈ S, branchRootCount v r p B = (insideRoots v r p).card := by
  classical
  change ∑ B ∈ S, (rootBranchMultiset v r p).count B = _
  rw [Multiset.sum_count_eq_card (fun B hB => hS (by simpa only [rootBranches, Multiset.mem_toFinset] using hB))]
  exact Multiset.card_map _ _

/-- Outside the actual original image the WHOLE root multiplicity vanishes. -/
theorem branchRootCount_eq_zero_of_not_mem (r : ℝ≥0) (p : K[X])
    {B : Set (CoordinateDisc (A := K) v r)} (hB : B ∉ rootBranches v r p) :
    branchRootCount v r p B = 0 := by
  classical
  exact Multiset.count_eq_zero.mpr (by simpa only [rootBranches, Multiset.mem_toFinset] using hB)

/-- The actual branch-law identifies the original fibre count with genuine strict root distances. -/
theorem branchRootCount_eq_card_filter_sub (r : ℝ≥0) (hr : 0 < r) (p : K[X])
    (a : K) (ha : v a ≤ r) :
    branchRootCount v r p (discBranch v r a) = (p.roots.filter (fun b => v (a-b) < r)).card := by
  classical
  rw [branchRootCount_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro b _
  constructor
  · intro hb
    exact (discBranch_eq_iff v r hr ha).mp hb.2.symm
  · intro hab
    have hb : v b ≤ r := by
      have he : b = a - (a-b) := by ring
      rw [he]
      exact (v.map_sub _ _).trans (max_le ha hab.le)
    exact ⟨hb, (discBranch_eq_of_val_sub_lt v r hab).symm⟩

/-- The actual finite branch family for the original rational unit; it can contain zero-slope branches. -/
def rationalRootBranches (r : ℝ≥0) (p q : K[X]) : Finset (Set (CoordinateDisc (A := K) v r)) := by
  classical
  exact rootBranches v r p ∪ rootBranches v r q

/-- The true inward orientation gives poles minus zeros in the original branch. -/
def inwardRootSlope (r : ℝ≥0) (p q : K[X]) (B : Set (CoordinateDisc (A := K) v r)) : ℤ :=
  (branchRootCount v r q B : ℤ) - (branchRootCount v r p B : ℤ)

/-- The true outer Gauss orientation gives original zeros-inside minus poles-inside. -/
def outwardRootSlope (r : ℝ≥0) (p q : K[X]) : ℤ :=
  ((insideRoots v r p).card : ℤ) - ((insideRoots v r q).card : ℤ)

/-- The ACTUAL finite original root partition derives the integer balancing sum. The following
ray/unit producers identify these same constructed integers with the original function slopes. -/
theorem outward_add_sum_inwardRootSlope_eq_zero (r : ℝ≥0) (p q : K[X]) :
    outwardRootSlope v r p q + ∑ B ∈ rationalRootBranches v r p q, inwardRootSlope v r p q B = 0 := by
  classical
  have hp := sum_branchRootCount v r p (rationalRootBranches v r p q) (by
    intro B hB
    exact Finset.mem_union_left _ hB)
  have hq := sum_branchRootCount v r q (rationalRootBranches v r p q) (by
    intro B hB
    exact Finset.mem_union_right _ hB)
  simp only [inwardRootSlope, Finset.sum_sub_distrib, ← Nat.cast_sum, hp, hq, outwardRootSlope]
  ring

/-- Every unlisted ACTUAL original branch has genuinely zero multiplicity slope. -/
theorem inwardRootSlope_eq_zero_of_not_mem (r : ℝ≥0) (p q : K[X])
    {B : Set (CoordinateDisc (A := K) v r)} (hB : B ∉ rationalRootBranches v r p q) :
    inwardRootSlope v r p q B = 0 := by
  classical
  have hp : B ∉ rootBranches v r p := fun h => hB (Finset.mem_union_left _ h)
  have hq : B ∉ rootBranches v r q := fun h => hB (Finset.mem_union_right _ h)
  rw [inwardRootSlope, branchRootCount_eq_zero_of_not_mem v r q hq,
    branchRootCount_eq_zero_of_not_mem v r p hp]
  rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum
