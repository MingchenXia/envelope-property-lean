import EnvelopeProperty.Char0.NativeSNCCharts
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.SNCHolomorphicTestMultiplierCriterion
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PrincipalGeneratorLogPointwiseNormalForm

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EnvelopeProperty.Char0.NativeSNCMultiplierCriterion

open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaHolomorphicJetMonomialSpan HolomorphicGermReducednessBridge

noncomputable section

/-- Literal coordinate monomial, retaining zero powers and dimension zero. -/
def coordinateMonomial {n : ℕ} (a : Fin n → ℕ) (z : ComplexModel n) : ℂ :=
  ∏ i, z i ^ a i

private theorem holomorphic_product {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → ComplexModel n → ℂ)
    (hF : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (F i) z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => ∏ i ∈ s, F i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using
      eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hF i) ih

theorem coordinateMonomial_holomorphic {n : ℕ} (a : Fin n → ℕ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (coordinateMonomial a) z :=
  holomorphic_product Finset.univ _ (fun i =>
    eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (a i))

private theorem germ_product {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → ComplexModel n → ℂ)
    (hF : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (F i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, F i z) (holomorphic_product s F hF) =
      ∏ i ∈ s, HolGerm.mk (F i) (hF i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have hp := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) : (ComplexModel n → ℂ) →+*
      Germ (𝓝 (0 : ComplexModel n)) ℂ) F s
  simp only [Germ.coe_coeRingHom] at hp
  rw [← hp, Finset.prod_fn]

theorem coordinateMonomial_germ {n : ℕ} (a : Fin n → ℕ) :
    HolGerm.mk (coordinateMonomial a) (coordinateMonomial_holomorphic a) =
      ∏ i, coordinateGerm i ^ a i := by
  change HolGerm.mk (fun z : ComplexModel n => ∏ i ∈ Finset.univ, z i ^ a i)
    (holomorphic_product Finset.univ _ (fun i =>
      eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (a i))) = _
  rw [germ_product]
  apply Finset.prod_congr rfl
  intro i _
  exact HolGerm.mk_pow (fun z : ComplexModel n => z i)
    (eventually_differentiableAt_coordinate i) (a i)

private theorem coordinateMonomial_add {n : ℕ} (a d : Fin n → ℕ) (z : ComplexModel n) :
    coordinateMonomial (fun i => a i + d i) z =
      coordinateMonomial a z * coordinateMonomial d z := by
  simp only [coordinateMonomial, pow_add, Finset.prod_mul_distrib]

/-- The rounded exponent after an actual Jacobian order is subtracted. -/
def roundedOrder {n : ℕ} (b : Fin n → ℝ) (d : Fin n → ℕ) (c : ℝ) : Fin n → ℕ :=
  fun i => Nat.floor (c * b i) - d i

private theorem roundedOrder_le_iff {x : ℝ} {d a : ℕ} :
    Nat.floor x - d ≤ a ↔ x < (a : ℝ) + d + 1 := by
  rw [Nat.sub_le_iff_le_add, ← Nat.lt_succ_iff,
    Nat.floor_lt' (Nat.succ_ne_zero _)]
  simp only [Nat.cast_succ, Nat.cast_add]

private theorem monomial_dvd_of_le {n : ℕ} {a b : Fin n → ℕ} (h : ∀ i, a i ≤ b i) :
    (∏ i, coordinateGerm (n := n) i ^ a i) ∣ ∏ i, coordinateGerm i ^ b i := by
  refine ⟨∏ i, coordinateGerm i ^ (b i - a i), ?_⟩
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add, Nat.add_sub_of_le (h i)]

/-- Arbitrary holomorphic tests, including extra zeros and the zero germ,
satisfy the literal weighted SNC integral precisely when the rounded
coordinate monomial divides the WHOLE original test germ. -/
theorem multiplierIntegrableAt_mul_coordinateMonomial_iff {n : ℕ}
    (b : Fin n → ℝ) (d : Fin n → ℕ) {c : ℝ} (hc : 0 < c)
    {F : ComplexModel n → ℂ} {ρ : ComplexModel n → ℝ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z) :
    MultiplierIntegrableAt (fun z : ComplexModel n =>
      (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal))
      c (fun z => F z * coordinateMonomial d z) 0 volume ↔
    (∏ i, coordinateGerm i ^ roundedOrder b d c i) ∣ HolGerm.mk F hF := by
  constructor
  · intro hint
    by_cases hn : HolGerm.mk F hF = 0
    · rw [hn]
      exact dvd_zero _
    have hnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0 := by
      by_contra h
      apply hn
      have heq : F =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => (0 : ℂ) := by
        filter_upwards [Filter.not_frequently.mp h] with z hz
        exact not_ne_iff.mp hz
      exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero
    obtain ⟨a, H, hH, _, heq, hnot⟩ :=
      HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hnon
    have hfactor : (fun z => F z * coordinateMonomial d z) =ᶠ[𝓝 (0 : ComplexModel n)]
        fun z => H z * coordinateMonomial (fun i => a i + d i) z := by
      filter_upwards [heq] with z hz
      rw [hz, coordinateMonomial_add]
      simp only [coordinateMonomial, mul_assoc]
    have hthreshold := SNCHolomorphicTestMultiplierCriterion.thresholds_of_multiplier_integrable
      (fun i => a i + d i) b hH hnot hfactor hρ hint
    have hle : ∀ i, roundedOrder b d c i ≤ a i := by
      intro i
      apply roundedOrder_le_iff.mpr
      simpa only [Nat.cast_add] using hthreshold i
    apply (monomial_dvd_of_le hle).trans
    refine ⟨HolGerm.mk H hH, ?_⟩
    have hm : HolGerm.mk F hF = HolGerm.mk H hH *
        HolGerm.mk (coordinateMonomial a) (coordinateMonomial_holomorphic a) := by
      rw [← HolGerm.mk_mul H (coordinateMonomial a) hH (coordinateMonomial_holomorphic a)]
      exact HolGerm.mk_eq_mk_iff.mpr heq
    rw [coordinateMonomial_germ] at hm
    exact hm.trans (mul_comm _ _)
  · rintro ⟨h, heq⟩
    obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk h
    have hfactor : F =ᶠ[𝓝 (0 : ComplexModel n)]
        fun z => H z * coordinateMonomial (roundedOrder b d c) z := by
      apply (HolGerm.mk_eq_mk_iff (hf := hF)
        (hg := eventually_differentiableAt_mul hH (coordinateMonomial_holomorphic _))).mp
      rw [HolGerm.mk_mul H (coordinateMonomial (roundedOrder b d c))
        hH (coordinateMonomial_holomorphic _), coordinateMonomial_germ]
      exact heq.trans (mul_comm _ _)
    apply HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
      (fun i => roundedOrder b d c i + d i) b hc hH ?_ hρ ?_
    · filter_upwards [hfactor] with z hz
      rw [hz]
      simp only [coordinateMonomial, pow_add, Finset.prod_mul_distrib, mul_assoc]
    · intro i
      simpa only [Nat.cast_add] using
        (roundedOrder_le_iff (x := c * b i) (d := d i)
          (a := roundedOrder b d c i)).mp (le_refl _)


private theorem mul_sum_nonneg_real {ι : Type*} (S : Finset ι) (F : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ S, F i) = ∑ i ∈ S, (c : EReal) * F i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

private theorem coordinateMonomial_nonzero {n : ℕ} (a : Fin n → ℕ) :
    HolGerm.mk (coordinateMonomial a) (coordinateMonomial_holomorphic a) ≠ 0 := by
  rw [coordinateMonomial_germ]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    pow_ne_zero _ (HolomorphicCoordinatePrime.prime_coordinate_germ i).ne_zero

private theorem frequently_nonzero_of_germ_ne_zero {n : ℕ} {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hn : HolGerm.mk F hF ≠ 0) : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0 := by
  by_contra h
  apply hn
  have heq : F =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => (0 : ℂ) := by
    filter_upwards [Filter.not_frequently.mp h] with z hz
    exact not_ne_iff.mp hz
  exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero

/-- The ORIGINAL finite generator family has the exact prescribed coordinate
orders. Its actual holomorphic quotients and positive residual norm are
manufactured from equality of its WHOLE principal ideal. All coordinate poles
are retained pointwise, and no test-function zero-locus premise is used. -/
theorem exists_generatorLog_fixed_coordinate_normal_form {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (a : Fin n → ℕ)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {∏ i, coordinateGerm i ^ a i}) :
    ∃ ρ : ComplexModel n → ℝ,
      (∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z) ∧
      generatorLog G =ᶠ[𝓝 (0 : ComplexModel n)] fun z =>
        (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
          (ρ z : EReal) := by
  have hspan' : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk (coordinateMonomial a) (coordinateMonomial_holomorphic a)} := by
    rwa [coordinateMonomial_germ]
  obtain ⟨Q, hQ, hGQ, i, hi⟩ :=
    PrincipalHolomorphicGeneratorQuotients.exists_holomorphic_quotients_of_principal_span
      G hG (coordinateMonomial_holomorphic a)
      (frequently_nonzero_of_germ_ne_zero _ (coordinateMonomial_nonzero a)) hspan'
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
  refine ⟨fun z => Real.log (generatorNormSq Q z), ?_, ?_⟩
  · filter_upwards [hQc, hQp] with z hqc hqp
    exact hqc.log hqp.ne'
  · filter_upwards [hQp, eventually_all.mpr hGQ] with z hqp hgq
    have hfamily : generatorLog G z =
        generatorLog (fun j w => coordinateMonomial a w * Q j w) z := by
      simp only [generatorLog_eq_log_sum]
      apply congrArg (fun r : ℝ => ENNReal.log (ENNReal.ofReal r))
      exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hgq j)
    have hlogM : ENNReal.log (ENNReal.ofReal ‖coordinateMonomial a z‖) =
        ∑ i : Fin n, ((a i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖) := by
      simpa only [coordinateMonomial, one_mul, norm_one, ENNReal.ofReal_one, ENNReal.log_one, zero_add]
        using PrincipalGeneratorLogPointwiseNormalForm.log_norm_unit_monomial_eq a 1 z
    rw [hfamily, PrincipalGeneratorLogNormNormalForm.generatorLog_common_factor _ Q z hqp,
      hlogM, mul_sum_nonneg_real _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp_rw [← mul_assoc, ← EReal.coe_mul]

/-- Equality of the two WHOLE principal ideals internally manufactures the
actual holomorphic unit factor of the actual analytic Jacobian. -/
theorem exists_unit_mul_coordinateMonomial_of_span {n : ℕ}
    {J : ComplexModel n → ℂ}
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ J z)
    (d : Fin n → ℕ)
    (hspan : Ideal.span {HolGerm.mk J hJ} =
      Ideal.span {∏ i, coordinateGerm i ^ d i}) :
    ∃ (U : ComplexModel n → ℂ)
      (_hU : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ U z),
      U 0 ≠ 0 ∧ J =ᶠ[𝓝 (0 : ComplexModel n)] fun z => U z * coordinateMonomial d z := by
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  obtain ⟨U, hU, hrep⟩ := HolGerm.exists_eq_mk (u : HolGerm (ComplexModel n))
  have hU0 : U 0 ≠ 0 := by
    have he := (HolGerm.isUnit_iff_eval_ne_zero (u : HolGerm (ComplexModel n))).mp u.isUnit
    rwa [hrep, HolGerm.eval_mk] at he
  refine ⟨U, hU, hU0, ?_⟩
  apply (HolGerm.mk_eq_mk_iff (hf := hJ)
    (hg := eventually_differentiableAt_mul hU (coordinateMonomial_holomorphic d))).mp
  rw [HolGerm.mk_mul U (coordinateMonomial d) hU (coordinateMonomial_holomorphic d),
    coordinateMonomial_germ, ← hrep]
  exact hu.symm.trans (mul_comm _ _)

/-- For the ORIGINAL finite weight generators and ORIGINAL analytic Jacobian,
their WHOLE monomial ideal identities imply an exact rounded-divisibility
criterion for EVERY holomorphic test. Actual generator quotients and the
Jacobian unit are derived internally. -/
theorem multiplierIntegrableAt_generatorLog_mul_iff {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (a d : Fin n → ℕ)
    (hspanG : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {∏ i, coordinateGerm i ^ a i})
    {J : ComplexModel n → ℂ}
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ J z)
    (hspanJ : Ideal.span {HolGerm.mk J hJ} =
      Ideal.span {∏ i, coordinateGerm i ^ d i})
    {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    {c : ℝ} (hc : 0 < c) :
    MultiplierIntegrableAt (generatorLog G) c (fun z => F z * J z) 0 volume ↔
      (∏ i, coordinateGerm i ^ roundedOrder (fun j => (a j : ℝ)) d c i) ∣
        HolGerm.mk F hF := by
  obtain ⟨ρ, hρ, hweight⟩ := exists_generatorLog_fixed_coordinate_normal_form G hG a hspanG
  obtain ⟨U, hU, hU0, hJU⟩ := exists_unit_mul_coordinateMonomial_of_span hJ d hspanJ
  have htest : (fun z => F z * J z) =ᶠ[𝓝 (0 : ComplexModel n)]
      fun z => U z * (F z * coordinateMonomial d z) := by
    filter_upwards [hJU] with z hz
    rw [hz]
    ring
  have hunit := ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff
    (φ := fun z : ComplexModel n =>
      (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal))
    (c := c) (f := fun z => F z * coordinateMonomial d z) (μ := volume) hU hU0
  have hcriterion := multiplierIntegrableAt_mul_coordinateMonomial_iff
    (fun i => (a i : ℝ)) d hc hF hρ
  constructor
  · intro hint
    exact hcriterion.mp (hunit.mp (hint.congr hweight htest))
  · intro hdiv
    exact (hunit.mpr (hcriterion.mpr hdiv)).congr hweight.symm htest.symm

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open NativeEtaleCoordinates

/-- The actual algebraic etale tuple internally supplies adapted representatives
for EVERY native analytic test germ. Their weighted integral is equivalent to
membership in the WHOLE ideal generated by the original centered equations. -/
theorem exists_native_test_representative {R : Type} [CommRing R]
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (g : HolGerm (ComplexModel n)) :
    ∃ (F : ComplexModel n → ℂ)
      (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z),
      coordinateGermEquiv f n p t ht (HolGerm.mk F hF) = g ∧
      ∀ (b : Fin n → ℝ) (d : Fin n → ℕ) (c : ℝ), 0 < c →
      ∀ (ρ : ComplexModel n → ℝ),
        (∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z) →
        (MultiplierIntegrableAt (fun z : ComplexModel n =>
          (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal))
          c (fun z => F z * coordinateMonomial d z) 0 volume ↔
        g ∈ Ideal.span {coefficientGerm f n p
          (∏ i, centeredOriginal f n p t i ^ roundedOrder b d c i)}) := by
  let E := coordinateGermEquiv f n p t ht
  obtain ⟨F, hF, hrep⟩ := HolGerm.exists_eq_mk (E.symm g)
  have he : E (HolGerm.mk F hF) = g := by rw [← hrep]; exact E.apply_symm_apply g
  refine ⟨F, hF, he, ?_⟩
  intro b d c hc ρ hρ
  rw [multiplierIntegrableAt_mul_coordinateMonomial_iff b d hc hF hρ,
    Ideal.mem_span_singleton]
  have hm := coordinateGermEquiv_monomial f n p t ht (roundedOrder b d c)
  change E (∏ i, coordinateGerm i ^ roundedOrder b d c i) = _ at hm
  rw [← hm, ← he]
  exact (map_dvd_iff E).symm

end
end EnvelopeProperty.Char0.NativeSNCMultiplierCriterion
