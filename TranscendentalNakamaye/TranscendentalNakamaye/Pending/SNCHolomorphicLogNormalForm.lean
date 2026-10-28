import TranscendentalNakamaye.Pending.HolomorphicCoordinateFactorization
import TranscendentalNakamaye.Pending.MultiplierHaarLinearTransport
import TranscendentalNakamaye.Pending.SNCCoordinateMonomialMultiplier

set_option autoImplicit false

/-! # Actual SNC logarithmic weights and internally constructed AE normal forms -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace TranscendentalNakamaye.Pending.SNCHolomorphicLogNormalForm

open FirstPass

noncomputable section

/-- Genuine Haar uniqueness and the actual linear coordinates supply all coordinate nullities. -/
theorem ae_coordinates_ne_zero (n : ℕ) :
    ∀ᵐ z : ComplexModel n ∂volume, ∀ i : Fin n, z i ≠ 0 := by
  let L : ComplexModel n ≃L[ℂ] (Fin n → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  let μ : Measure (Fin n → ℂ) := (volume : Measure (ComplexModel n)).map L
  have : μ.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  let t : ℝ≥0 := μ.addHaarScalarFactor (volume : Measure (Fin n → ℂ))
  have ht : t ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hμ : μ = t • (volume : Measure (Fin n → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul μ volume
  have hplain : ∀ᵐ w : Fin n → ℂ ∂volume, ∀ i : Fin n, w i ≠ 0 :=
    ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0
  have hmap : ∀ᵐ w ∂μ, ∀ i : Fin n, w i ≠ 0 := by
    rw [hμ]
    exact (Measure.ae_smul_measure_iff ht).mpr hplain
  have hpull := ae_of_ae_map L.continuous.measurable.aemeasurable hmap
  simpa only [L, PiLp.coe_continuousLinearEquiv] using hpull

/-- Away from the genuine zero coordinates, the original extended logarithm is finite. -/
theorem log_norm_unit_monomial_of_coordinates_ne_zero {n : ℕ}
    (a : Fin n → ℕ) {u : ℂ} (hu : u ≠ 0) (z : ComplexModel n)
    (hz : ∀ i : Fin n, z i ≠ 0) :
    ENNReal.log (ENNReal.ofReal ‖u * ∏ i : Fin n, z i ^ a i‖) =
      ((Real.log ‖u‖ + ∑ i : Fin n, (a i : ℝ) * Real.log ‖z i‖ : ℝ) : EReal) := by
  have hprod : (∏ i : Fin n, z i ^ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hz i)
  rw [ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (mul_ne_zero hu hprod))]
  congr 1
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hprod),
    Complex.norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (pow_ne_zero _ (hz i)))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_pow, Real.log_pow]

private theorem coe_sum_real {s : ℕ} (f : Fin s → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) :=
  map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ

/-- Every exponent and the continuous remainder follow from the original holomorphic functions. -/
theorem exists_coordinate_log_ae_normal_form {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) (r : Fin s → ℝ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    (hzero : ∀ i, ∀ᶠ z in 𝓝 0, G i z = 0 → ∃ j : Fin n, z j = 0)
    {ρ : ComplexModel n → ℝ} (hρ : ∀ᶠ z in 𝓝 0, ContinuousAt ρ z) :
    ∃ (a : Fin s → Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
      (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
      (fun z => (∑ i : Fin s, ((2 * r i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖G i z‖)) + (ρ z : EReal)) =ᵐ[volume.restrict (ball 0 R)]
      (fun z => (∑ j : Fin n, ((2 * ∑ i : Fin s, r i * (a i j : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) := by
  classical
  choose a H hH hH0 heq using fun i =>
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus
      (hG i) (hzero i)
  have hrow : ∀ i, ∀ᶠ z in 𝓝 0,
      DifferentiableAt ℂ (H i) z ∧ H i z ≠ 0 ∧ G i z = H i z * ∏ j : Fin n, z j ^ a i j := by
    intro i
    filter_upwards [hH i, (hH i).self_of_nhds.continuousAt.eventually_ne (hH0 i), heq i]
      with z hz hz0 hzG
    exact ⟨hz, hz0, hzG⟩
  have hall : ∀ᶠ z in 𝓝 0, ContinuousAt ρ z ∧ ∀ i : Fin s,
      DifferentiableAt ℂ (H i) z ∧ H i z ≠ 0 ∧ G i z = H i z * ∏ j : Fin n, z j ^ a i j :=
    hρ.and (eventually_all.mpr hrow)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hall
  let η : ComplexModel n → ℝ := fun z => ρ z + ∑ i : Fin s, 2 * r i * Real.log ‖H i z‖
  refine ⟨a, η, R, hR, ?_, ?_⟩
  · intro z hz
    have hcont : ∀ i : Fin s, ContinuousAt (fun w => 2 * r i * Real.log ‖H i w‖) z := by
      intro i
      exact continuousAt_const.mul (((hball hz).2 i).1.continuousAt.norm.log
        (norm_ne_zero_iff.mpr ((hball hz).2 i).2.1))
    have hsum : ContinuousAt (fun w => ∑ i : Fin s, 2 * r i * Real.log ‖H i w‖) z := by
      fun_prop
    exact (hball hz).1.add hsum
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (ae_coordinates_ne_zero n)] with z hz hzcoord
    have hlogG (i : Fin s) : ENNReal.log (ENNReal.ofReal ‖G i z‖) =
        ((Real.log ‖H i z‖ + ∑ j : Fin n, (a i j : ℝ) * Real.log ‖z j‖ : ℝ) : EReal) := by
      rw [((hball hz).2 i).2.2]
      exact log_norm_unit_monomial_of_coordinates_ne_zero (a i) ((hball hz).2 i).2.1 z hzcoord
    have hlogz (j : Fin n) : ENNReal.log (ENNReal.ofReal ‖z j‖) =
        ((Real.log ‖z j‖ : ℝ) : EReal) :=
      ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (hzcoord j))
    have hcross : (∑ i : Fin s, 2 * r i * ∑ j : Fin n, (a i j : ℝ) * Real.log ‖z j‖) =
        ∑ j : Fin n, (2 * ∑ i : Fin s, r i * (a i j : ℝ)) * Real.log ‖z j‖ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hlogG, hlogz, ← EReal.coe_mul]
    simp only [← coe_sum_real, ← EReal.coe_add]
    congr 1
    dsimp only [η]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hcross]
    ring

end
end TranscendentalNakamaye.Pending.SNCHolomorphicLogNormalForm
