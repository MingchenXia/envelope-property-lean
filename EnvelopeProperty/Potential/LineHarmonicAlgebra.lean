import EnvelopeProperty.Potential.LineHarmonicMaximum

/-! # The real vector space of actual harmonic functions -/

open scoped NNReal Polynomial
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

theorem IsHarmonic.const (b : ℝ) : U.IsHarmonic (fun _ => b) := by
  refine ⟨b,fun _ => 0,?_⟩
  intro x
  simp [harmonicExpression]

theorem IsHarmonic.add {h k : U.carrier → ℝ} (hh : U.IsHarmonic h) (hk : U.IsHarmonic k) :
    U.IsHarmonic (h+k) := by
  obtain ⟨c,γ,hγ⟩ := hh
  obtain ⟨d,δ,hδ⟩ := hk
  refine ⟨c+d,fun j => γ j+δ j,?_⟩
  intro x
  simp only [Pi.add_apply,hγ,hδ,harmonicExpression,add_mul,Finset.sum_add_distrib]
  ring

theorem IsHarmonic.smul (a : ℝ) {h : U.carrier → ℝ} (hh : U.IsHarmonic h) :
    U.IsHarmonic (a • h) := by
  obtain ⟨c,γ,hγ⟩ := hh
  refine ⟨a*c,fun j => a*γ j,?_⟩
  intro x
  simp only [Pi.smul_apply,smul_eq_mul,hγ,harmonicExpression,mul_add,Finset.mul_sum,mul_assoc]

theorem IsHarmonic.neg {h : U.carrier → ℝ} (hh : U.IsHarmonic h) : U.IsHarmonic (-h) := by
  simpa only [neg_one_smul] using hh.smul U (-1)

theorem IsHarmonic.sub {h k : U.carrier → ℝ} (hh : U.IsHarmonic h) (hk : U.IsHarmonic k) :
    U.IsHarmonic (h-k) := by
  simpa only [sub_eq_add_neg] using hh.add U (hk.neg U)

/-- Membership is the literal finite-coordinate representation predicate on actual functions. -/
def harmonicSubmodule : Submodule ℝ (U.carrier → ℝ) where
  carrier := {h | U.IsHarmonic h}
  zero_mem' := IsHarmonic.const U 0
  add_mem' := fun hh hk => hh.add U hk
  smul_mem' := fun a _ hh => hh.smul U a

theorem mem_harmonicSubmodule (h : U.carrier → ℝ) : h ∈ U.harmonicSubmodule ↔ U.IsHarmonic h :=
  Iff.rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
