/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Ultrametricity of the actual infimum additive quotient seminorm -/
noncomputable section
namespace EnvelopeProperty.NormedAdditiveQuotient

/-- Actual strict-ball representatives derive the whole quotient ultrametric
inequality without closedness, separation, completeness or any ring structure. -/
instance quotientIsUltrametricDist {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] (S : AddSubgroup E) : IsUltrametricDist (E ⧸ S) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  apply le_of_forall_gt
  intro r hr
  have hx : ‖x‖ < r := (le_max_left _ _).trans_lt hr
  have hy : ‖y‖ < r := (le_max_right _ _).trans_lt hr
  obtain ⟨a, rfl, ha⟩ := QuotientAddGroup.norm_lt_iff.mp hx
  obtain ⟨b, rfl, hb⟩ := QuotientAddGroup.norm_lt_iff.mp hy
  exact QuotientAddGroup.norm_lt_iff.mpr
    ⟨a+b, rfl, (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)⟩

end EnvelopeProperty.NormedAdditiveQuotient
