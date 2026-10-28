import EnvelopeProperty.Potential.FiniteFreeBanachAlgebra
import EnvelopeProperty.Berkovich.SpectrumBoundedMaps

/-! # Genuine bounded coefficient maps in the entire constructed finite free analytic algebra -/

open scoped NNReal Classical
noncomputable section
namespace Module.Basis
variable {R E ι : Type*} [NormedCommRing R] [CommRing E] [Algebra R E] [Fintype ι]
variable (b : Basis ι R E)

/-- The whole original basis-coefficient norm obeys the actual scalar bound. -/
theorem fcCoefficientNorm_smul_le (r : R) (a : E) :
    b.fcCoefficientNorm (r • a) ≤ ‖r‖ * b.fcCoefficientNorm a := by
  unfold fcCoefficientNorm
  rw [map_smul]
  exact norm_smul_le r _

/-- The original coefficient inclusion has an actual bound in the constructed operator ring norm. -/
theorem fcCoefficientRingNorm_algebraMap_le (r : R) :
    b.fcCoefficientRingNorm (algebraMap R E r) ≤
      (b.fcMultiplicationBound * b.fcCoefficientNorm 1) * ‖r‖ := by
  calc
    _ ≤ b.fcMultiplicationBound * b.fcCoefficientNorm (algebraMap R E r) :=
      b.fcCoefficientRingNorm_le _
    _ ≤ b.fcMultiplicationBound * (‖r‖ * b.fcCoefficientNorm 1) := by
      apply mul_le_mul_of_nonneg_left _ b.fcMultiplicationBound_pos.le
      simpa only [Algebra.smul_def, mul_one] using b.fcCoefficientNorm_smul_le r 1
    _ = _ := by ring

end Module.Basis

namespace EnvelopeProperty.FiniteFreeAnalyticCopy
variable {R E ι : Type*} [NormedCommRing R] [CommRing E] [Algebra R E] [Fintype ι]
variable (b : Module.Basis ι R E)

/-- The actual entire coefficient inclusion is bounded, including the zero algebra. -/
theorem coefficientHom_isBounded :
    (algebraMap R (FiniteFreeAnalyticCopy b)).IsBounded := by
  let C := b.fcMultiplicationBound * b.fcCoefficientNorm 1
  have hC : 0 ≤ C := mul_nonneg b.fcMultiplicationBound_pos.le (b.fcCoefficientNorm_nonneg 1)
  refine ⟨1 + C, by linarith, fun r => ?_⟩
  change b.fcCoefficientRingNorm (algebraMap R E r) ≤ _
  exact (b.fcCoefficientRingNorm_algebraMap_le r).trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) (norm_nonneg r))

/-- The same original coefficient inclusion is genuinely continuous in the constructed whole algebra norm. -/
theorem continuous_coefficientHom : Continuous (algebraMap R (FiniteFreeAnalyticCopy b)) := by
  obtain ⟨C, _, hb⟩ := coefficientHom_isBounded b
  exact AddMonoidHomClass.continuous_of_bound (algebraMap R (FiniteFreeAnalyticCopy b)) C hb

end EnvelopeProperty.FiniteFreeAnalyticCopy
