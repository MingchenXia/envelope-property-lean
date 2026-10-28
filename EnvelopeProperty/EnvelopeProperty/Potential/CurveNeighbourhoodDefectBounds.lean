import EnvelopeProperty.Potential.CurveAnalyticBasisCoefficients
import EnvelopeProperty.Potential.CompletedFibreFractionCoefficients

/-! # Actual small neighbourhood bounds for every whole curve coefficient -/

open scoped NNReal Polynomial TensorProduct BigOperators
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]

def fcCurveMultiplicationUpper (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) : ℝ :=
  1+∑ i : ι, ∑ j : ι, ∑ k : ι, ((x.1.val (basis.equivFun (basis i*basis j) k) : ℝ)+1)

omit [IsAlgClosed K] in
theorem fcCurveMultiplicationUpper_pos (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) :
    0 < fcCurveMultiplicationUpper x basis := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)

def fcCurveOneCoefficientUpper (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) : ℝ :=
  1+∑ i : ι, ((x.1.val (basis.equivFun 1 i) : ℝ)+1)

omit [IsAlgClosed K] in
theorem fcCurveOneCoefficientUpper_pos (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) :
    0 < fcCurveOneCoefficientUpper x basis := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => by positivity)

/-- Every bound is on the whole actual analytic tensor. The constants controlling its
multiplication and the coefficients of one depend only on the original point and basis. -/
theorem fc_exists_standardAffinoid_curve_fraction_bounds
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (d : K[X]) (c : B) (hd : x.1.val d ≠ 0) (M η : ℝ) (hM : 0 < M) (hη : 0 < η)
    (hb : (basis.baseChange x.1.H).fcCoefficientNorm (Spectrum.fractionTensor x.1 d c) < M)
    (herr : (basis.baseChange x.1.H).fcCoefficientNorm
      ((Spectrum.fractionTensor x.1 d c)^2-Spectrum.fractionTensor x.1 d c) < η) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, x ∈ interior U.carrier ∧
      ∃ _hdU : ∀ y : U.carrier, y.1.1.val d ≠ 0,
        (U.curveAnalyticBasis basis).fcMultiplicationBound ≤ fcCurveMultiplicationUpper x basis ∧
        (U.curveAnalyticBasis basis).fcCoefficientNorm 1 ≤ fcCurveOneCoefficientUpper x basis ∧
        (U.curveAnalyticBasis basis).fcCoefficientNorm
          (U.curveAnalyticOriginalEquiv basis (U.curveAnalyticFraction basis d c)) < M ∧
        (U.curveAnalyticBasis basis).fcCoefficientNorm
          (U.curveAnalyticOriginalEquiv basis
            ((U.curveAnalyticFraction basis d c)^2-U.curveAnalyticFraction basis d c)) < η := by
  classical
  let I := (ι×ι×ι) ⊕ (ι ⊕ (ι ⊕ ι))
  let p : Option I → K[X] := fun i => i.elim 0 (Sum.elim
    (fun t => basis.equivFun (basis t.1*basis t.2.1) t.2.2)
    (Sum.elim (fun i => basis.equivFun c i)
      (Sum.elim (fun i => basis.equivFun (c^2-algebraMap K[X] B d*c) i)
        (fun i => basis.equivFun 1 i))))
  let D : Option I → K[X] := fun i => i.elim d (Sum.elim (fun _ => 1)
    (Sum.elim (fun _ => d) (Sum.elim (fun _ => d^2) (fun _ => 1))))
  let N : Option I → ℝ := fun i => i.elim 1 (Sum.elim
    (fun t => (x.1.val (basis.equivFun (basis t.1*basis t.2.1) t.2.2) : ℝ)+1)
    (Sum.elim (fun _ => M) (Sum.elim (fun _ => η)
      (fun i => (x.1.val (basis.equivFun 1 i) : ℝ)+1))))
  have hD : ∀ i, x.1.val (D i) ≠ 0 := by
    intro i
    cases i with
    | none => exact hd
    | some i =>
        rcases i with t | (i | (i | i))
        · simp only [D,Option.elim_some,Sum.elim_inl,map_one,ne_eq,one_ne_zero,not_false_eq_true]
        · exact hd
        · simpa only [D,Option.elim_some,Sum.elim_inr,Sum.elim_inl,map_pow] using pow_ne_zero 2 hd
        · simp only [D,Option.elim_some,Sum.elim_inr,map_one,ne_eq,one_ne_zero,not_false_eq_true]
  have hN : ∀ i, (x.1.val (p i) : ℝ)/(x.1.val (D i) : ℝ) < N i := by
    intro i
    cases i with
    | none => simp only [p,D,N,Option.elim_none,map_zero,NNReal.coe_zero,zero_div,zero_lt_one]
    | some i =>
        rcases i with t | (i | (i | i))
        · simp only [p,D,N,Option.elim_some,Sum.elim_inl,map_one,NNReal.coe_one,div_one]
          exact lt_add_one _
        · change (x.1.val (basis.equivFun c i) : ℝ)/(x.1.val d : ℝ) < M
          have he := congrArg (fun q : ℝ≥0 => (q : ℝ))
            (Spectrum.fractionTensor_coefficient_nnnorm x.1 basis d c i)
          have hcoord := (basis.baseChange x.1.H).norm_equivFun_le_fcCoefficientNorm
            (Spectrum.fractionTensor x.1 d c) i
          have he' : ‖(basis.baseChange x.1.H).equivFun (Spectrum.fractionTensor x.1 d c) i‖ =
              (x.1.val (basis.equivFun c i) : ℝ)/(x.1.val d : ℝ) := by
            simpa only [NNReal.coe_div,coe_nnnorm] using he
          rw [← he']
          exact hcoord.trans_lt hb
        · change (x.1.val (basis.equivFun (c^2-algebraMap K[X] B d*c) i) : ℝ)/
              (x.1.val (d^2) : ℝ) < η
          have he := congrArg (fun q : ℝ≥0 => (q : ℝ))
            (Spectrum.fractionTensor_defect_coefficient_nnnorm x.1 basis d c hd i)
          have hcoord := (basis.baseChange x.1.H).norm_equivFun_le_fcCoefficientNorm
            ((Spectrum.fractionTensor x.1 d c)^2-Spectrum.fractionTensor x.1 d c) i
          have he' : ‖(basis.baseChange x.1.H).equivFun
              ((Spectrum.fractionTensor x.1 d c)^2-Spectrum.fractionTensor x.1 d c) i‖ =
              (x.1.val (basis.equivFun (c^2-algebraMap K[X] B d*c) i) : ℝ)/(x.1.val (d^2) : ℝ) := by
            simpa only [NNReal.coe_div,coe_nnnorm] using he
          rw [← he']
          exact hcoord.trans_lt herr
        · simp only [p,D,N,Option.elim_some,Sum.elim_inr,map_one,NNReal.coe_one,div_one]
          exact lt_add_one _
  obtain ⟨m,U,hx,hden,hbounds⟩ := fc_exists_standardAffinoid_analyticFraction_family_norm_lt x p D hD N hN
  have hdU : ∀ y : U.carrier, y.1.1.val d ≠ 0 := hden none
  have honefrac (q : K[X]) : U.polynomialAnalyticFraction q 1 = U.polynomialAnalyticMap q := by
    simp only [FCStandardAffinoid.polynomialAnalyticFraction,map_one,Ring.inverse_one,mul_one]
  have htable (i j k : ι) : ‖U.polynomialAnalyticMap (basis.equivFun (basis i*basis j) k)‖ ≤
      (x.1.val (basis.equivFun (basis i*basis j) k) : ℝ)+1 := by
    have h := hbounds (some (Sum.inl (i,j,k)))
    simpa only [p,D,N,Option.elim_some,Sum.elim_inl,honefrac] using h.le
  have hmult : (U.curveAnalyticBasis basis).fcMultiplicationBound ≤ fcCurveMultiplicationUpper x basis := by
    change 1+_ ≤ 1+_
    apply add_le_add (le_refl 1)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    rw [U.curveAnalyticBasis_multiplication_coefficient]
    exact htable i j k
  have hone : (U.curveAnalyticBasis basis).fcCoefficientNorm 1 ≤ fcCurveOneCoefficientUpper x basis := by
    apply (pi_norm_le_iff_of_nonneg (fcCurveOneCoefficientUpper_pos x basis).le).mpr
    intro i
    rw [Algebra.TensorProduct.one_def,U.curveAnalyticBasis_coefficient_tmul,mul_one]
    have hi := hbounds (some (Sum.inr (Sum.inr (Sum.inr i))))
    have hi' : ‖U.polynomialAnalyticMap (basis.equivFun 1 i)‖ <
        (x.1.val (basis.equivFun 1 i) : ℝ)+1 := by
      simpa only [p,D,N,Option.elim_some,Sum.elim_inr,honefrac] using hi
    apply hi'.le.trans
    have hs : (x.1.val (basis.equivFun 1 i) : ℝ)+1 ≤
        ∑ j : ι, ((x.1.val (basis.equivFun 1 j) : ℝ)+1) :=
      Finset.single_le_sum (f := fun j : ι => (x.1.val (basis.equivFun 1 j) : ℝ)+1)
        (fun j _ => by positivity) (Finset.mem_univ i)
    change _ ≤ 1+_
    linarith
  refine ⟨m,U,hx,hdU,hmult,hone,?_,?_⟩
  · apply (pi_norm_lt_iff hM).mpr
    intro i
    rw [U.curveAnalyticFraction_coefficient]
    exact hbounds (some (Sum.inr (Sum.inl i)))
  · apply (pi_norm_lt_iff hη).mpr
    intro i
    rw [U.curveAnalyticFraction_defect_coefficient basis d c hdU]
    exact hbounds (some (Sum.inr (Sum.inr (Sum.inl i))))

end EnvelopeProperty.Berkovich.RelativeSpectrum
