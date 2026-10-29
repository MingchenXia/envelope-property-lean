/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact local gluing in a dense rational lattice of continuous functions

The first reduction in FHX Lemma 5.5 glues local global-PL expressions into a single global
PL expression. The topological argument only needs a rational vector lattice of continuous
functions with uniform approximation. Clipped approximations to Urysohn functions provide
exact cutoffs; a finite minimum of penalized local expressions then gives exact gluing.

This argument concerns global PL membership, not positivity or plurisubharmonicity.
-/

noncomputable section

namespace EnvelopeProperty.RationalFunctionLattice

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (L : Submodule ℚ (X → ℝ))
  (hconst : ∀ q : ℚ, (fun _ : X => (q : ℝ)) ∈ L)
  (hmin : ∀ f ∈ L, ∀ g ∈ L, (fun x => min (f x) (g x)) ∈ L)
  (hmax : ∀ f ∈ L, ∀ g ∈ L, (fun x => max (f x) (g x)) ∈ L)
  (hcont : ∀ f ∈ L, Continuous f)
  (happrox : ∀ f : X → ℝ, Continuous f → ∀ ε : ℝ, 0 < ε →
    ∃ g ∈ L, ∀ x, |f x - g x| < ε)

include hconst hmin hmax hcont happrox

/-- Clipping a uniform approximation to a Urysohn function gives an exact local cutoff. -/
theorem exists_cutoff {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ b ∈ L, (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∉ U, b y = 0) ∧
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, b y = 1 := by
  have hdisj : Disjoint Uᶜ {x} := by
    rw [Set.disjoint_singleton_right]
    simpa using hx
  obtain ⟨χ, hχ0, hχ1, _hχ01⟩ :=
    exists_continuous_zero_one_of_isClosed hU.isClosed_compl isClosed_singleton hdisj
  obtain ⟨τ, hτ, hχτ⟩ := happrox χ χ.continuous (1 / 8) (by norm_num)
  have hlin : (fun y => 2 * τ y - (1 / 2 : ℝ)) ∈ L := by
    convert L.sub_mem (L.smul_mem (2 : ℚ) hτ) (hconst (1 / 2)) using 1
    ext y
    simp [Pi.smul_apply, Rat.smul_def]
  let b : X → ℝ := fun y => max 0 (min 1 (2 * τ y - 1 / 2))
  have hb : b ∈ L := by
    simpa only [Rat.cast_zero, Rat.cast_one] using
      hmax _ (hconst 0) _ (hmin _ (hconst 1) _ hlin)
  refine ⟨b, hb, fun y => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩,
    ?_, {y | (3 / 4 : ℝ) < τ y}, isOpen_lt continuous_const (hcont τ hτ), ?_, ?_⟩
  · intro y hy
    have hχy : χ y = 0 := hχ0 hy
    have hτy := (abs_lt.mp (hχτ y)).1
    rw [hχy] at hτy
    change max 0 (min 1 (2 * τ y - 1 / 2)) = 0
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · have hχx : χ x = 1 := hχ1 (Set.mem_singleton x)
    have hτx := (abs_lt.mp (hχτ x)).2
    rw [hχx] at hτx
    change (3 / 4 : ℝ) < τ x
    linarith
  · intro y hy
    change max 0 (min 1 (2 * τ y - 1 / 2)) = 1
    have hy' : (3 / 4 : ℝ) < τ y := hy
    rw [min_eq_left (by linarith)]
    norm_num

/-- Local membership in a uniformly dense rational vector lattice is global membership. -/
theorem mem_of_locally_mem {f : X → ℝ}
    (hlocal : ∀ x, ∃ (U : Set X) (g : X → ℝ), IsOpen U ∧ x ∈ U ∧ g ∈ L ∧
      ∀ y ∈ U, f y = g y) : f ∈ L := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have hf : f = 0 := funext fun x => isEmptyElim x
    rw [hf]
    exact L.zero_mem
  choose U g hU hxU hg hfg using hlocal
  choose b hb hb01 hb0 V hV hxV hb1 using fun x =>
    exists_cutoff L hconst hmin hmax hcont happrox (hU x) (hxU x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  have hcover : ∀ y, ∃ i ∈ s, b i y = 1 := by
    intro y
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
    exact ⟨i, hi, hb1 i y hy⟩
  have hsne : s.Nonempty := by
    obtain ⟨i, hi, _⟩ := hcover (Classical.arbitrary X)
    exact ⟨i, hi⟩
  have hmatch : ∀ i y, b i y ≠ 0 → f y = g i y := by
    intro i y hbi
    apply hfg i y
    by_contra hy
    exact hbi (hb0 i y hy)
  have hbound : ∀ i : X, ∃ C : ℝ, ∀ y, |g i y| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont _ (hg i)).continuousOn
    exact ⟨C, fun y => by simpa only [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hbound
  obtain ⟨M, hM⟩ := exists_rat_gt (max 0 (s.sup' hsne C))
  have hMpos : (0 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hgM : ∀ i ∈ s, ∀ y, |g i y| ≤ (M : ℝ) := by
    intro i hi y
    exact (hC i y).trans ((Finset.le_sup' C hi).trans ((le_max_right _ _).trans hM.le))
  have hfM : ∀ y, |f y| ≤ (M : ℝ) := by
    intro y
    obtain ⟨i, hi, hbi⟩ := hcover y
    rw [hmatch i y (by rw [hbi]; norm_num)]
    exact hgM i hi y
  let H : X → X → ℝ := fun i y => g i y + (4 * (M : ℝ)) * (1 - b i y)
  have hH : ∀ i, H i ∈ L := by
    intro i
    convert L.add_mem (hg i) (L.smul_mem (4 * M)
      (L.sub_mem (hconst 1) (hb i))) using 1
    ext y
    simp [H, Pi.smul_apply, Rat.smul_def]
  have hG : s.inf' hsne H = f := by
    funext y
    rw [Finset.inf'_apply]
    apply le_antisymm
    · obtain ⟨i, hi, hbi⟩ := hcover y
      refine (Finset.inf'_le (fun i => H i y) hi).trans_eq ?_
      dsimp only [H]
      rw [← hmatch i y (by rw [hbi]; norm_num), hbi]
      ring
    · refine Finset.le_inf' hsne _ ?_
      intro i hi
      dsimp only [H]
      by_cases hbi : b i y = 0
      · rw [hbi]
        have hgy := (abs_le.mp (hgM i hi y)).1
        have hfy := (le_abs_self (f y)).trans (hfM y)
        linarith
      · rw [← hmatch i y hbi]
        have hnonneg : 0 ≤ (4 * (M : ℝ)) * (1 - b i y) :=
          mul_nonneg (by linarith) (sub_nonneg.mpr (hb01 i y).2)
        linarith
  rw [← hG]
  exact Finset.inf'_induction hsne H (fun a ha b hb => hmin a ha b hb) (fun i _ => hH i)

end EnvelopeProperty.RationalFunctionLattice
