/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-! # Genuine antitone extended-real limits and rational real approximation -/
open Filter Topology
noncomputable section
namespace EnvelopeProperty

/-! ### Infima of decreasing sequences in `EReal` -/

section EReal

/-- The infimum of a decreasing sequence is its limit. -/
theorem iInf_eq_of_tendsto_of_antitone {a : ℕ → EReal} {l : EReal} (ha : Antitone a)
    (h : Tendsto a atTop (𝓝 l)) : ⨅ j, a j = l :=
  tendsto_nhds_unique (tendsto_atTop_iInf ha) h

/-- A monotone map continuous at the limit commutes with the infimum of a decreasing
sequence. -/
theorem iInf_comp_of_antitone {a : ℕ → EReal} (ha : Antitone a) {F : EReal → EReal}
    (hF : Monotone F) (hc : ContinuousAt F (⨅ j, a j)) : ⨅ j, F (a j) = F (⨅ j, a j) :=
  iInf_eq_of_tendsto_of_antitone (hF.comp_antitone ha) (hc.tendsto.comp (tendsto_atTop_iInf ha))

/-- The infimum of the maximum of two decreasing sequences. -/
theorem iInf_max_of_antitone {a b : ℕ → EReal} (ha : Antitone a) (hb : Antitone b) :
    ⨅ j, max (a j) (b j) = max (⨅ j, a j) (⨅ j, b j) :=
  iInf_eq_of_tendsto_of_antitone (fun _ _ hij => max_le_max (ha hij) (hb hij))
    ((tendsto_atTop_iInf ha).max (tendsto_atTop_iInf hb))

/-- The infimum of the sum of two decreasing sequences that are not `⊤`. -/
theorem iInf_add_of_antitone {a b : ℕ → EReal} (ha : Antitone a) (hb : Antitone b)
    (ha0 : a 0 ≠ ⊤) (hb0 : b 0 ≠ ⊤) : ⨅ j, (a j + b j) = (⨅ j, a j) + ⨅ j, b j := by
  have h1 : (⨅ j, a j) ≠ ⊤ := ne_top_of_le_ne_top ha0 (iInf_le _ 0)
  have h2 : (⨅ j, b j) ≠ ⊤ := ne_top_of_le_ne_top hb0 (iInf_le _ 0)
  refine iInf_eq_of_tendsto_of_antitone (fun _ _ hij => add_le_add (ha hij) (hb hij)) ?_
  exact (EReal.continuousAt_add (p := ((⨅ j, a j), (⨅ j, b j))) (Or.inl h1)
    (Or.inr h2)).tendsto.comp ((tendsto_atTop_iInf ha).prodMk_nhds (tendsto_atTop_iInf hb))

/-- Adding a real constant commutes with the infimum of a decreasing sequence. -/
theorem iInf_add_coe_of_antitone {a : ℕ → EReal} (ha : Antitone a) (ha0 : a 0 ≠ ⊤) (c : ℝ) :
    ⨅ j, (a j + (c : EReal)) = (⨅ j, a j) + (c : EReal) := by
  rw [iInf_add_of_antitone ha antitone_const ha0 (EReal.coe_ne_top c), iInf_const]

/-- Multiplication by a positive real commutes with the infimum of a decreasing sequence. -/
theorem iInf_coe_mul_of_antitone {a : ℕ → EReal} (ha : Antitone a) {c : ℝ} (hc : 0 < c) :
    ⨅ j, (c : EReal) * a j = (c : EReal) * ⨅ j, a j := by
  refine iInf_comp_of_antitone ha
    (fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hc.le)) ?_
  have hc' : (c : EReal) ≠ 0 := by exact_mod_cast hc.ne'
  have : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) ((c : EReal), ⨅ j, a j) :=
    EReal.continuousAt_mul (Or.inl hc') (Or.inl hc') (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))
  exact this.comp (continuous_const.prodMk continuous_id).continuousAt

/-- `⨅ j, (r - j) = -∞`. -/
theorem iInf_coe_sub_natCast (r : ℝ) : ⨅ j : ℕ, (((r - j : ℝ)) : EReal) = ⊥ := by
  refine iInf_eq_bot.2 fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb (lt_irrefl _)
  | coe b =>
    obtain ⟨j, hj⟩ := exists_nat_gt (r - b)
    exact ⟨j, by rw [EReal.coe_lt_coe_iff]; linarith⟩
  | top => exact ⟨0, EReal.coe_lt_top _⟩

/-- `⨅ j, -j = -∞`. -/
theorem iInf_neg_natCast : ⨅ j : ℕ, (((-(j : ℝ) : ℝ)) : EReal) = ⊥ := by
  simpa using iInf_coe_sub_natCast 0

/-- A positive real multiple of an extended real `≠ ⊥` is `≠ ⊥`. -/
theorem coe_mul_ne_bot {c : ℝ} (hc : 0 < c) {a : EReal} (ha : a ≠ ⊥) : (c : EReal) * a ≠ ⊥ := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | coe a => exact EReal.coe_ne_bot (c * a) ∘ fun h => by rw [EReal.coe_mul]; exact h
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot

/-- A decreasing sequence of rationals converging to a given real number. -/
theorem exists_antitone_rat_iInf_eq (c : ℝ) :
    ∃ q : ℕ → ℚ, Antitone q ∧ (∀ j, c < q j) ∧ ⨅ j, (((q j : ℚ) : ℝ) : EReal) = (c : EReal) := by
  have h : ∀ j : ℕ, ∃ q : ℚ, c + 1 / ((j : ℝ) + 2) < q ∧ (q : ℝ) < c + 1 / ((j : ℝ) + 1) := by
    intro j
    refine exists_rat_btwn ?_
    have : (1 : ℝ) / ((j : ℝ) + 2) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  choose q hq1 hq2 using h
  have hpos : ∀ j, c < q j := fun j => lt_trans (by
    have : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
    linarith) (hq1 j)
  have hanti : Antitone q := by
    refine antitone_nat_of_succ_le fun j => ?_
    have h1 : ((q (j + 1) : ℚ) : ℝ) < c + 1 / ((j : ℝ) + 2) := by
      have := hq2 (j + 1)
      push_cast at this
      rwa [show (j : ℝ) + 1 + 1 = j + 2 by ring] at this
    have h2 := hq1 j
    have : ((q (j + 1) : ℚ) : ℝ) ≤ q j := by linarith
    exact_mod_cast this
  refine ⟨q, hanti, hpos, le_antisymm ?_ (le_iInf fun j => by exact_mod_cast (hpos j).le)⟩
  refine le_of_forall_gt fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb not_lt_bot
  | coe b =>
    rw [EReal.coe_lt_coe_iff] at hb
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hb)
    refine (iInf_le _ j).trans_lt ?_
    rw [EReal.coe_lt_coe_iff]
    linarith [hq2 j]
  | top => exact (iInf_le _ 0).trans_lt (EReal.coe_lt_top _)

end EReal

end EnvelopeProperty
