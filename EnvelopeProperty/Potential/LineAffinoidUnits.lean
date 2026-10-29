import EnvelopeProperty.Potential.LineAffinoidSpectrum
import EnvelopeProperty.Berkovich.BanachSpectralUnits

/-! # Actual units of the original standard-affinoid function completion -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- On a field, pointwise domination of actual valuations forces equality by inverse constants. -/
theorem valuation_eq_of_pointwise_le {v₁ v₂ : Valuation K ℝ≥0}
    (h : ∀ a, v₁ a ≤ v₂ a) : v₁ = v₂ := by
  apply Valuation.ext
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · apply le_antisymm (h a)
    have hi := h a⁻¹
    rw [map_inv₀,map_inv₀] at hi
    exact (inv_le_inv₀ (pos_iff_ne_zero.mpr ((_root_.map_ne_zero v₁).mpr ha))
      (pos_iff_ne_zero.mpr ((_root_.map_ne_zero v₂).mpr ha))).mp hi

/-- EVERY actual absolute bounded point has the SAME prescribed original coefficient values. -/
theorem boundedSpectrum_coefficient_values (x : NormBoundedSpectrum U.AnalyticFunctions) (a : K) :
    x.1.val (U.analyticCoefficients a) = w a := by
  let v : Valuation K ℝ≥0 := x.1.val.comap U.analyticCoefficients
  have hv : ∀ a, v a ≤ w a := fun a =>
    (x.2 (U.analyticCoefficients a)).trans_eq (U.nnnorm_algebraMap_analyticFunctions a)
  exact congrArg (fun v : Valuation K ℝ≥0 => v a) (valuation_eq_of_pointwise_le hv)

/-- The original whole bounded point, now with its DERIVED original coefficient condition. -/
def prescribedAnalyticBoundedPoint (x : NormBoundedSpectrum U.AnalyticFunctions) :
    U.AnalyticBoundedSpectrum := ⟨x,U.boundedSpectrum_coefficient_values x⟩

variable [IsAlgClosed K]

/-- The FULL actual unit criterion for the whole genuine completed function ring. -/
theorem analyticFunctions_isUnit_iff (f : U.AnalyticFunctions) :
    IsUnit f ↔ ∀ x : U.carrier, U.analyticValue f x ≠ 0 := by
  constructor
  · intro hf x
    exact nnnorm_ne_zero_iff.mpr ((hf.map (U.evaluationToH x)).ne_zero)
  · intro hf
    apply (isUnit_iff_forall_normBoundedSpectrum_ne_zero f).mpr
    intro x
    let y := U.prescribedAnalyticBoundedPoint x
    have he := U.analyticSpectrumHomeomorph_symm_val (U.analyticSpectrumHomeomorph y) f
    rw [Homeomorph.symm_apply_apply] at he
    exact fun hzero => hf (U.analyticSpectrumHomeomorph y) (he.symm.trans hzero)

theorem analyticFunctions_isUnit_iff_pos (f : U.AnalyticFunctions) :
    IsUnit f ↔ ∀ x : U.carrier, 0 < U.analyticValue f x := by
  simpa only [pos_iff_ne_zero] using U.analyticFunctions_isUnit_iff f
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
