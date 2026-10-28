import EnvelopeProperty.Potential.LineSubharmonic
import Mathlib.Data.EReal.Inv

/-! # Nonnegative scaling in actual harmonic comparison -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

private theorem fc_ereal_pos_mul_le_coe_iff (a : ℝ) (ha : 0 < a) (u : EReal) (b : ℝ) :
    (a : EReal)*u ≤ (b : EReal) ↔ u ≤ ((b/a : ℝ) : EReal) := by
  induction u with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe x =>
    rw [← EReal.coe_mul,EReal.coe_le_coe_iff,EReal.coe_le_coe_iff,mul_comm a x]
    exact (le_div_iff₀ ha).symm

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}
variable {u : RelativeSpectrum w K[X] → EReal} {Ω : Set (RelativeSpectrum w K[X])}

theorem IsLineSubharmonicOn.mul_pos (hu : IsLineSubharmonicOn u Ω) (a : ℝ) (ha : 0 < a) :
    IsLineSubharmonicOn (fun x => (a : EReal)*u x) Ω where
  upperSemicontinuousOn := by
    have hc : Continuous (fun z : EReal => (a : EReal)*z) := by
      apply continuous_iff_continuousAt.mpr
      intro b
      exact EReal.Tendsto.const_mul continuous_id.continuousAt
        (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))
    exact hc.comp_upperSemicontinuousOn hu.upperSemicontinuousOn
      (fun _ _ h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr ha.le))
  ne_top := by
    intro x hx
    exact (EReal.mul_ne_top _ _).mpr ⟨Or.inl (EReal.coe_ne_bot a),
      Or.inl (EReal.coe_nonneg.mpr ha.le),Or.inl (EReal.coe_ne_top a),Or.inr (hu.ne_top x hx)⟩
  comparison := by
    intro m U h hU hh hB x
    have hhdiv : U.IsHarmonic (fun z => h z/a) := by
      have he : a⁻¹ • h = (fun z => h z/a) := by
        funext z
        simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      rw [← he]
      exact hh.smul U a⁻¹
    apply (fc_ereal_pos_mul_le_coe_iff a ha _ _).mpr
    exact hu.comparison U _ hU hhdiv
      (fun z hz => (fc_ereal_pos_mul_le_coe_iff a ha _ _).mp (hB z hz)) x

variable [IsAlgClosed K]

theorem IsLineSubharmonicOn.mul_nonneg (hu : IsLineSubharmonicOn u Ω) (a : ℝ) (ha : 0 ≤ a) :
    IsLineSubharmonicOn (fun x => (a : EReal)*u x) Ω := by
  rcases ha.eq_or_lt with h | h
  · rw [← h]
    simpa only [EReal.coe_zero,zero_mul] using IsLineSubharmonicOn.const (w := w) 0 Ω
  · exact hu.mul_pos a h

end EnvelopeProperty.Berkovich.RelativeSpectrum
