import TranscendentalNakamaye.Pending.DivisorialChangeOfVariables

set_option autoImplicit false

/-! # Exact raw multiplier image integrals off an actual null source set -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace TranscendentalNakamaye.Pending.HolomorphicWeightedImageChangeOfVariables

open FirstPass DivisorialChangeOfVariables

noncomputable section

variable {N : ℕ}

/-- Actual differentiability supplies the null exceptional-image assertion internally. -/
theorem ae_eq_image_sdiff_of_differentiableOn
    {F : ComplexModel N → ComplexModel N} {U S : Set (ComplexModel N)}
    (hF : DifferentiableOn ℂ F U) (hS : volume S = 0) :
    F '' (U \ S) =ᵐ[volume] F '' U := by
  have hnull : volume (F '' (U ∩ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hF.mono inter_subset_left).restrictScalars ℝ) (measure_mono_null inter_subset_right hS)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  apply propext
  constructor
  · exact fun h => image_mono sdiff_subset h
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hxS
    exact hy ⟨x, ⟨hx, hxS⟩, rfl⟩

/-- Exact image equality holds for the literal density at every pole and every real level. -/
theorem lintegral_multiplierDensity_comp_eq {F : ComplexModel N → ComplexModel N}
    {U : Set (ComplexModel N)} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {S : Set (ComplexModel N)} (hS : volume S = 0) (hinj : InjOn F (U \ S))
    (w : ComplexModel N → EReal) (c : ℝ) (g : ComplexModel N → ℂ) :
    ∫⁻ z in U, multiplierDensity (fun z => w (F z)) c
        (fun z => g (F z) * complexJacobian F z) z =
      ∫⁻ y in F '' U, multiplierDensity w c g y := by
  set S' := toMeasurable volume S with hS'
  have hS'0 : volume S' = 0 := by rw [hS', measure_toMeasurable]; exact hS
  set s := U \ S' with hs
  have hsm : MeasurableSet s := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  have hinj' : InjOn F s := hinj.mono (sdiff_subset_sdiff_right (subset_toMeasurable _ _))
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F ((fderiv ℂ F x).restrictScalars ℝ) s x :=
    fun x hx => ((hF.differentiableAt (hU.mem_nhds hx.1)).hasFDerivAt.restrictScalars ℝ)
      |>.hasFDerivWithinAt
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj'
    (multiplierDensity w c g)
  calc ∫⁻ z in U, multiplierDensity (fun z => w (F z)) c
          (fun z => g (F z) * complexJacobian F z) z
        = ∫⁻ z in s, multiplierDensity (fun z => w (F z)) c
          (fun z => g (F z) * complexJacobian F z) z :=
          (setLIntegral_congr (sdiff_null_ae_eq_self hS'0)).symm
      _ = ∫⁻ x in s, ENNReal.ofReal |((fderiv ℂ F x).restrictScalars ℝ).det| *
            multiplierDensity w c g (F x) := by
          refine setLIntegral_congr_fun hsm fun z _ => ?_
          rw [det_restrictScalars_eq_normSq, abs_of_nonneg (Complex.normSq_nonneg _)]
          simp only [multiplierDensity, complexJacobian, norm_mul, mul_pow]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
            Complex.normSq_eq_norm_sq, mul_comm (‖(fderiv ℂ F z).det‖ ^ 2)]
      _ = ∫⁻ y in F '' s, multiplierDensity w c g y := hcov.symm
      _ = ∫⁻ y in F '' U, multiplierDensity w c g y :=
          setLIntegral_congr (ae_eq_image_sdiff_of_differentiableOn hF hS'0)

end
end TranscendentalNakamaye.Pending.HolomorphicWeightedImageChangeOfVariables
