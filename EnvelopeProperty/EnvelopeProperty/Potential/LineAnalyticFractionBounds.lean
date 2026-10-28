import EnvelopeProperty.Potential.CurveAnalyticFractions

/-! # Actual simultaneous analytic fraction norm bounds on genuine neighbourhoods -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- A pointwise strict bound controls the genuine WHOLE completion norm, by its DERIVED
actual finite-boundary formula. -/
theorem norm_lt_of_forall_analyticValue_lt (f : U.AnalyticFunctions) (M : ℝ) (hM : 0 < M)
    (hf : ∀ x : U.carrier, (U.analyticValue f x : ℝ) < M) : ‖f‖ < M := by
  let : Fintype U.boundary := U.rationalBoundaryFintype
  have hn : ‖f‖ = ‖fun z : U.boundary => U.evaluationToH ⟨z.1,U.boundary_subset z.2⟩ f‖ :=
    congrArg (fun r : ℝ≥0 => (r : ℝ)) (U.nnnorm_eq_boundary_nnnorm f)
  rw [hn]
  exact (pi_norm_lt_iff hM).mpr fun z => hf ⟨z.1,U.boundary_subset z.2⟩

/-- The actual original fraction using the genuine analytic inverse. -/
def polynomialAnalyticFraction (p d : K[X]) : U.AnalyticFunctions :=
  U.polynomialAnalyticMap p*Ring.inverse (U.polynomialAnalyticMap d)

theorem analyticValue_polynomialAnalyticFraction (p d : K[X])
    (hd : ∀ x : U.carrier, x.1.1.val d ≠ 0) (x : U.carrier) :
    U.analyticValue (U.polynomialAnalyticFraction p d) x = x.1.1.val p/x.1.1.val d := by
  change ‖U.evaluationToH x (U.polynomialAnalyticMap p*Ring.inverse (U.polynomialAnalyticMap d))‖₊ = _
  rw [map_mul,U.evaluationToH_inverse_polynomial d hd x]
  have hp : U.evaluationToH x (U.polynomialAnalyticMap p) = x.1.1.toH p :=
    (U.polynomialAnalyticEvaluation x).commutes p
  rw [hp,nnnorm_mul,nnnorm_inv,Spectrum.nnnorm_toH,Spectrum.nnnorm_toH,div_eq_mul_inv]

end FCStandardAffinoid

/-- Every finite family of strict ORIGINAL ratio bounds is realized as genuine analytic
completion norm bounds on an actual standard-affinoid neighbourhood of the original point. -/
theorem fc_exists_standardAffinoid_analyticFraction_norm_lt {ι : Type*} [Fintype ι]
    (x : RelativeSpectrum w K[X]) (d : K[X]) (hd : x.1.val d ≠ 0)
    (p : ι → K[X]) (M : ι → ℝ)
    (hM : ∀ i, (x.1.val (p i) : ℝ)/(x.1.val d : ℝ) < M i) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, x ∈ interior U.carrier ∧
      ∃ _hden : ∀ y : U.carrier, y.1.1.val d ≠ 0,
        ∀ i, ‖U.polynomialAnalyticFraction (p i) d‖ < M i := by
  have hdreal : (x.1.val d : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hd
  have hden : ∀ᶠ y : RelativeSpectrum w K[X] in 𝓝 x, y.1.val d ≠ 0 :=
    (isOpen_ne.preimage (continuous_val_apply d)).mem_nhds hd
  have hb (i : ι) : ∀ᶠ y : RelativeSpectrum w K[X] in 𝓝 x,
      (y.1.val (p i) : ℝ)/(y.1.val d : ℝ) < M i := by
    have hc : ContinuousAt (fun y : RelativeSpectrum w K[X] =>
        (y.1.val (p i) : ℝ)/(y.1.val d : ℝ)) x :=
      ((NNReal.continuous_coe.comp (continuous_val_apply (p i))).continuousAt).div
        (NNReal.continuous_coe.comp (continuous_val_apply d)).continuousAt hdreal
    exact hc (isOpen_Iio.mem_nhds (hM i))
  have hN : {y : RelativeSpectrum w K[X] | y.1.val d ≠ 0 ∧
      ∀ i, (y.1.val (p i) : ℝ)/(y.1.val d : ℝ) < M i} ∈ 𝓝 x := by
    filter_upwards [hden,eventually_all.mpr hb] with y hy hi
    exact ⟨hy,hi⟩
  obtain ⟨m,U,hx,hU⟩ := fc_exists_standardAffinoid_nhds x hN
  let hdenU : ∀ y : U.carrier, y.1.1.val d ≠ 0 := fun y => (hU y.2).1
  refine ⟨m,U,hx,hdenU,?_⟩
  intro i
  have hMpos : 0 < M i := (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).trans_lt (hM i)
  apply U.norm_lt_of_forall_analyticValue_lt _ _ hMpos
  intro y
  rw [U.analyticValue_polynomialAnalyticFraction (p i) d hdenU y,NNReal.coe_div]
  exact (hU y.2).2 i

/-- The genuine neighbourhood norm bound also permits a different ORIGINAL denominator at
each of the finitely many indices. -/
theorem fc_exists_standardAffinoid_analyticFraction_family_norm_lt {ι : Type*} [Fintype ι]
    (x : RelativeSpectrum w K[X]) (p d : ι → K[X])
    (hd : ∀ i, x.1.val (d i) ≠ 0) (M : ι → ℝ)
    (hM : ∀ i, (x.1.val (p i) : ℝ)/(x.1.val (d i) : ℝ) < M i) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, x ∈ interior U.carrier ∧
      ∃ _hden : ∀ i, ∀ y : U.carrier, y.1.1.val (d i) ≠ 0,
        ∀ i, ‖U.polynomialAnalyticFraction (p i) (d i)‖ < M i := by
  have hden (i : ι) : ∀ᶠ y : RelativeSpectrum w K[X] in 𝓝 x, y.1.val (d i) ≠ 0 :=
    (isOpen_ne.preimage (continuous_val_apply (d i))).mem_nhds (hd i)
  have hb (i : ι) : ∀ᶠ y : RelativeSpectrum w K[X] in 𝓝 x,
      (y.1.val (p i) : ℝ)/(y.1.val (d i) : ℝ) < M i := by
    have hc : ContinuousAt (fun y : RelativeSpectrum w K[X] =>
        (y.1.val (p i) : ℝ)/(y.1.val (d i) : ℝ)) x :=
      ((NNReal.continuous_coe.comp (continuous_val_apply (p i))).continuousAt).div
        (NNReal.continuous_coe.comp (continuous_val_apply (d i))).continuousAt
        (NNReal.coe_ne_zero.mpr (hd i))
    exact hc (isOpen_Iio.mem_nhds (hM i))
  have hN : {y : RelativeSpectrum w K[X] | (∀ i, y.1.val (d i) ≠ 0) ∧
      ∀ i, (y.1.val (p i) : ℝ)/(y.1.val (d i) : ℝ) < M i} ∈ 𝓝 x := by
    filter_upwards [eventually_all.mpr hden,eventually_all.mpr hb] with y hy hi
    exact ⟨hy,hi⟩
  obtain ⟨m,U,hx,hU⟩ := fc_exists_standardAffinoid_nhds x hN
  let hdenU : ∀ i, ∀ y : U.carrier, y.1.1.val (d i) ≠ 0 := fun i y => (hU y.2).1 i
  refine ⟨m,U,hx,hdenU,?_⟩
  intro i
  have hMpos : 0 < M i := (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).trans_lt (hM i)
  apply U.norm_lt_of_forall_analyticValue_lt _ _ hMpos
  intro y
  rw [U.analyticValue_polynomialAnalyticFraction (p i) (d i) (hdenU i) y,NNReal.coe_div]
  exact (hU y.2).2 i

end EnvelopeProperty.Berkovich.RelativeSpectrum
