/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Actual finite prime separation on one original normalized chart

Every original separating element and finite product is constructed.
-/
noncomputable section
namespace EnvelopeProperty

/-- Actual noncontainment constructs ONE original element in ALL other original ideals
and outside the selected original prime. -/
theorem exists_finite_prime_separator {R J : Type*} [CommRing R] [Fintype J]
    (P : J → Ideal R) (j₀ : J) [(P j₀).IsPrime]
    (hnot : ∀ j, j ≠ j₀ → ¬ P j ≤ P j₀) :
    ∃ a : R, a ∉ P j₀ ∧ ∀ j, j ≠ j₀ → a ∈ P j := by
  classical
  let T := {j : J // j ≠ j₀}
  have hchoices (j : T) : ∃ a : R, a ∈ P j ∧ a ∉ P j₀ := by
    exact Set.not_subset.mp (hnot j j.2)
  choose a ha using hchoices
  refine ⟨∏ j : T, a j, ?_, ?_⟩
  · intro hm
    obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact (ha j).2 hj
  · intro j hj
    let t : T := ⟨j, hj⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
    exact (P j).mul_mem_right _ (ha t).1

/-- Distinct ACTUAL height-one centres derive every noncontainment premise internally. -/
theorem exists_finite_heightOne_prime_separator {R J : Type*} [CommRing R]
    [IsNoetherianRing R] [Fintype J] (P : J → Ideal R) [∀ j, (P j).IsPrime]
    (hheight : ∀ j, (P j).height = 1) (j₀ : J) (hne : ∀ j, j ≠ j₀ → P j ≠ P j₀) :
    ∃ a : R, a ∉ P j₀ ∧ ∀ j, j ≠ j₀ → a ∈ P j := by
  apply exists_finite_prime_separator P j₀
  intro j hj hle
  exact hne j hj ((P j).eq_of_le_of_height_le hle (by rw [hheight, hheight]))

end EnvelopeProperty
