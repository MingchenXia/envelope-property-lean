import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PrincipalGeneratorLogNormNormalForm

set_option autoImplicit false

/-! # Pointwise principal-family logarithms at every coordinate pole

Natural principal generation and the actual coordinate zero locus supply
all orders, quotients and units. The output holds throughout a neighborhood,
not just almost everywhere. Nonnegative integer exponents retain all poles.
Reference: Demailly, CADG, local analytic ideals; Analytic Methods, multipliers.
-/

open Set Filter Metric
open scoped Topology ENNReal

namespace ComplexGeometry.AnalyticGeometry.PrincipalGeneratorLogPointwiseNormalForm

open Pluripotential

noncomputable section

private theorem log_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞) :
    ENNReal.log (∏ i ∈ S, f i) = ∑ i ∈ S, ENNReal.log (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ENNReal.log_mul_add, ih]

private theorem mul_sum_nonneg_real {ι : Type*} (S : Finset ι) (f : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ S, f i) = ∑ i ∈ S, (c : EReal) * f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

/-- Nonnegative integer orders give a genuine all-point extended logarithm
identity, including zero factors and the empty product. -/
theorem log_norm_unit_monomial_eq {n : ℕ} (a : Fin n → ℕ)
    (v : ℂ) (z : ComplexModel n) :
    ENNReal.log (ENNReal.ofReal ‖v * ∏ i : Fin n, z i ^ a i‖) =
      ENNReal.log (ENNReal.ofReal ‖v‖) +
        ∑ i : Fin n, ((a i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖) := by
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg v), ENNReal.log_mul_add,
    Complex.norm_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => norm_nonneg (z i ^ a i)),
    log_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_pow, ENNReal.ofReal_pow (norm_nonneg (z i)), ENNReal.log_pow, EReal.coe_natCast]

/-- The original whole principal family has an internally produced
normal form at every point of a genuine neighborhood, including all poles. -/
theorem exists_generatorLog_coordinate_normal_form {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH})
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ (a : Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
      (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
      ∀ z ∈ ball (0 : ComplexModel n) R,
        generatorLog G z = (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal) := by
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
  · intro z hz
    obtain ⟨_, hqp, _, hkn, hhk, hgq⟩ := hball hz
    have hfamily : generatorLog G z = generatorLog (fun j w => H w * Q j w) z := by
      simp only [generatorLog_eq_log_sum]
      apply congrArg (fun t : ℝ => ENNReal.log (ENNReal.ofReal t))
      exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hgq j)
    have hlogH : ENNReal.log (ENNReal.ofReal ‖H z‖) =
        (Real.log ‖K z‖ : EReal) + ∑ j : Fin n,
          ((a j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) := by
      rw [hhk, log_norm_unit_monomial_eq,
        ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hkn)]
    rw [hfamily, PrincipalGeneratorLogNormNormalForm.generatorLog_common_factor H Q z hqp,
      hlogH, EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)) (EReal.coe_ne_top (2 : ℝ)), mul_sum_nonneg_real _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp_rw [← mul_assoc, ← EReal.coe_mul]
    dsimp only [η]
    rw [EReal.coe_add]
    ac_rfl

end
end ComplexGeometry.AnalyticGeometry.PrincipalGeneratorLogPointwiseNormalForm
