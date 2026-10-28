import TranscendentalNakamaye.Pending.PrincipalHolomorphicGeneratorQuotients
import TranscendentalNakamaye.Pending.SNCHolomorphicLogNormalForm

set_option autoImplicit false

/-! # The original finite generator norm and its genuine principal log normal form -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace TranscendentalNakamaye.Pending.PrincipalGeneratorLogNormNormalForm

open FirstPass

noncomputable section

/-- This identity retains the zero common factor and the actual extended logarithm. -/
theorem generatorLog_common_factor {X : Type*} {s : ℕ}
    (h : X → ℂ) (Q : Fin s → X → ℂ) (x : X)
    (hQ : 0 < generatorNormSq Q x) :
    generatorLog (fun i y => h y * Q i y) x =
      ((2 : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖h x‖) +
        ((Real.log (generatorNormSq Q x) : ℝ) : EReal) := by
  have hsum : (∑ i : Fin s, ‖h x * Q i x‖ ^ 2) = ‖h x‖ ^ 2 * generatorNormSq Q x := by
    simp only [norm_mul, mul_pow, generatorNormSq, Finset.mul_sum]
  rw [generatorLog_eq_log_sum, hsum]
  by_cases hh : h x = 0
  · simp only [hh, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul,
      ENNReal.ofReal_zero, ENNReal.log_zero]
    rw [EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 2), EReal.bot_add]
  · have hhpos : 0 < ‖h x‖ := norm_pos_iff.mpr hh
    rw [ENNReal.log_ofReal_of_pos (mul_pos (pow_pos hhpos 2) hQ),
      ENNReal.log_ofReal_of_pos hhpos, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    rw [Real.log_mul (ne_of_gt (pow_pos hhpos 2)) hQ.ne', Real.log_pow]
    norm_num

private theorem coe_sum_real {s : ℕ} (f : Fin s → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) :=
  map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ

/-- Full principal generation, not individual zero loci, produces the whole-family log weight. -/
theorem exists_generatorLog_coordinate_ae_normal_form {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH})
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ (a : Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
      (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
      generatorLog G =ᵐ[volume.restrict (ball 0 R)]
        (fun z => (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) := by
  classical
  obtain ⟨Q, hQ, hGQ, i, hi⟩ :=
    PrincipalHolomorphicGeneratorQuotients.exists_holomorphic_quotients_of_principal_span
      G hG hH hHnon hspan
  obtain ⟨a, K, hK, hK0, hHK⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus
      hH hzero
  have hQc : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt (generatorNormSq Q) z := by
    filter_upwards [eventually_all.mpr hQ] with z hz
    have hcont (j : Fin s) : ContinuousAt (Q j) z := (hz j).continuousAt
    change ContinuousAt (fun w => ∑ j : Fin s, ‖Q j w‖ ^ 2) z
    fun_prop
  have hQpos : 0 < generatorNormSq Q 0 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖Q j 0‖)
      ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hQp : ∀ᶠ z in 𝓝 (0 : ComplexModel n), 0 < generatorNormSq Q z :=
    hQc.self_of_nhds.eventually (lt_mem_nhds hQpos)
  have hKn : ∀ᶠ z in 𝓝 (0 : ComplexModel n), K z ≠ 0 :=
    hK.self_of_nhds.continuousAt.eventually_ne hK0
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ContinuousAt (generatorNormSq Q) z ∧ 0 < generatorNormSq Q z ∧
      DifferentiableAt ℂ K z ∧ K z ≠ 0 ∧ H z = K z * ∏ j : Fin n, z j ^ a j ∧
      ∀ j : Fin s, G j z = H z * Q j z := by
    filter_upwards [hQc, hQp, hK, hKn, hHK, eventually_all.mpr hGQ]
      with z hqc hqp hkd hkn hhk hgq
    exact ⟨hqc, hqp, hkd, hkn, hhk, hgq⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hall
  let η : ComplexModel n → ℝ := fun z =>
    2 * Real.log ‖K z‖ + Real.log (generatorNormSq Q z)
  refine ⟨a, η, R, hR, ?_, ?_⟩
  · intro z hz
    obtain ⟨hqc, hqp, hkd, hkn, _, _⟩ := hball hz
    exact (continuousAt_const.mul (hkd.continuousAt.norm.log (norm_ne_zero_iff.mpr hkn))).add
      (hqc.log hqp.ne')
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (SNCHolomorphicLogNormalForm.ae_coordinates_ne_zero n)]
      with z hz hzcoord
    obtain ⟨_, hqp, _, hkn, hhk, hgq⟩ := hball hz
    have hfamily : generatorLog G z = generatorLog (fun j w => H w * Q j w) z := by
      simp only [generatorLog_eq_log_sum]
      apply congrArg (fun t : ℝ => ENNReal.log (ENNReal.ofReal t))
      exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hgq j)
    have hlogH : ENNReal.log (ENNReal.ofReal ‖H z‖) =
        ((Real.log ‖K z‖ + ∑ j : Fin n, (a j : ℝ) * Real.log ‖z j‖ : ℝ) : EReal) := by
      rw [hhk]
      exact SNCHolomorphicLogNormalForm.log_norm_unit_monomial_of_coordinates_ne_zero
        a hkn z hzcoord
    have hlogz (j : Fin n) : ENNReal.log (ENNReal.ofReal ‖z j‖) =
        ((Real.log ‖z j‖ : ℝ) : EReal) :=
      ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (hzcoord j))
    have hsum : (∑ j : Fin n, (2 * (a j : ℝ)) * Real.log ‖z j‖) =
        2 * ∑ j : Fin n, (a j : ℝ) * Real.log ‖z j‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfamily, generatorLog_common_factor H Q z hqp, hlogH]
    simp_rw [hlogz, ← EReal.coe_mul]
    simp only [← coe_sum_real, ← EReal.coe_add]
    congr 1
    dsimp only [η]
    rw [hsum]
    ring

end
end TranscendentalNakamaye.Pending.PrincipalGeneratorLogNormNormalForm
