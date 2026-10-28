import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Linarith

/-! A connectedness threshold argument for the numerical nef-plus-ample proof.
This module is purely analytic; its geometric intersection-polynomial inputs
are constructed separately. -/

open Set Filter Topology

namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmple

/-- Continuous mixed values satisfy the rational nonnegativity tests at every
positive real point where the top value is positive. -/
theorem nonneg_of_rational_positive_tests (f h : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0))
    (hrat : ∀ q : ℚ, 0 < q → 0 < f q → 0 ≤ h q)
    {t : ℝ} (ht : 0 < t) (hft : 0 < f t) : 0 ≤ h t := by
  by_contra hn
  have hneg : h t < 0 := lt_of_not_ge hn
  let U : Set ℝ := (Ioi 0 ∩ f ⁻¹' Ioi 0) ∩ (Ioi 0 ∩ h ⁻¹' Iio 0)
  have hU : IsOpen U :=
    (hf.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi).inter
      (hh.isOpen_inter_preimage isOpen_Ioi isOpen_Iio)
  have hUne : U.Nonempty := ⟨t, ⟨⟨ht, hft⟩, ⟨ht, hneg⟩⟩⟩
  obtain ⟨q, hq⟩ :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_mem_open hU hUne
  have hqpos : (0 : ℝ) < q := hq.1.1
  exact (not_lt_of_ge (hrat q (by exact_mod_cast hqpos) hq.1.2)) hq.2.2

/-- Eventual strict positivity and the actual rational mixed-value inequalities
exclude every positive threshold. No continuity of the positive factor `g`
and no nonnegativity test where `f ≤ 0` are required. -/
theorem positive_of_eventually_positive_and_rational_mixed_nonneg
    (f g h : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0))
    (hidentity : ∀ t : ℝ, 0 < t → f t = h t + t * g t)
    (hg : ∀ t : ℝ, 0 < t → 0 < g t)
    (hevent : ∀ᶠ t : ℝ in atTop, 0 < f t)
    (hrat : ∀ q : ℚ, 0 < q → 0 < f q → 0 ≤ h q) :
    ∀ t : ℝ, 0 < t → 0 < f t := by
  let Y := Ioi (0 : ℝ)
  let F : Y → ℝ := fun x => f x
  let H : Y → ℝ := fun x => h x
  have hF : Continuous F := continuousOn_iff_continuous_domRestrict.mp hf
  have hH : Continuous H := continuousOn_iff_continuous_domRestrict.mp hh
  let S : Set Y := {x | 0 < F x}
  have hSopen : IsOpen S := isOpen_lt continuous_const hF
  have hS_eq : S = {x : Y | 0 ≤ H x} := by
    ext x
    constructor
    · intro hx
      exact nonneg_of_rational_positive_tests f h hf hh hrat x.property hx
    · intro hx
      change 0 < f x
      rw [hidentity x x.property]
      exact add_pos_of_nonneg_of_pos hx (mul_pos x.property (hg x x.property))
  have hSclosed : IsClosed S := by
    rw [hS_eq]
    exact isClosed_le continuous_const hH
  have hSne : S.Nonempty := by
    obtain ⟨b, hb⟩ := eventually_atTop.mp hevent
    have ht : (0 : ℝ) < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
    exact ⟨⟨max b 1, ht⟩, hb (max b 1) (le_max_left b 1)⟩
  let : PreconnectedSpace Y := Subtype.preconnectedSpace isPreconnected_Ioi
  have hStop : S = univ := (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ hSne
  intro t ht
  have hmem : (⟨t, ht⟩ : Y) ∈ S := by rw [hStop]; trivial
  exact hmem

end EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
