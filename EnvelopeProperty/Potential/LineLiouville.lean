import EnvelopeProperty.Potential.LineDiscCompletion
import EnvelopeProperty.WeightedCompletionCoefficients

/-! # Original-field coefficients and Liouville for actual compatible disc functions -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The actual whole no-hole function ring compared with the existing original weighted completion. -/
def discToWeighted (r : ℝ≥0) (hr : 0 < r) :
    (zeroDisc (K := K) r).AnalyticFunctions ≃+* CompletedMonicDivision.Ring (A := K) r hr :=
  (discGaussEquiv r hr).symm.trans (GaussCompletion.weightedCompletionEquiv r hr).symm

theorem discToWeighted_polynomialMap (r : ℝ≥0) (hr : 0 < r) (p : K[X]) :
    discToWeighted r hr ((zeroDisc (K := K) r).polynomialAnalyticMap p) =
      CompletedMonicDivision.polynomialMap r hr p := by
  have he : (discGaussEquiv (K := K) r hr).symm
      ((zeroDisc (K := K) r).polynomialAnalyticMap p) = GaussCompletion.polynomialMap r hr p := by
    apply (discGaussEquiv r hr).injective
    rw [RingEquiv.apply_symm_apply,discGaussEquiv_polynomialMap]
  change (GaussCompletion.weightedCompletionEquiv r hr).symm
    ((discGaussEquiv r hr).symm ((zeroDisc (K := K) r).polynomialAnalyticMap p)) = _
  rw [he,GaussCompletion.weightedCompletionEquiv_symm_polynomialMap]

theorem nnnorm_discToWeighted (r : ℝ≥0) (hr : 0 < r) (f : (zeroDisc (K := K) r).AnalyticFunctions) :
    ‖discToWeighted r hr f‖₊ = ‖f‖₊ := by
  have he : discGaussEquiv r hr (GaussCompletion.weightedCompletionEquiv r hr (discToWeighted r hr f)) = f := by
    simp only [discToWeighted,RingEquiv.trans_apply,RingEquiv.apply_symm_apply]
  exact (GaussCompletion.nnnorm_weightedCompletionEquiv r hr _).symm.trans
    ((nnnorm_discGaussEquiv r hr _).symm.trans (congrArg nnnorm he))

theorem continuous_discToWeighted (r : ℝ≥0) (hr : 0 < r) :
    Continuous (discToWeighted (K := K) r hr) :=
  (AddMonoidHomClass.isometry_of_norm (discToWeighted r hr)
    (fun f => congrArg NNReal.toReal (nnnorm_discToWeighted r hr f))).continuous

variable [CompleteSpace K]

/-- Every coefficient belongs to the SAME original complete field, read on the actual whole completed function. -/
def discCoefficient (r : ℝ≥0) (hr : 0 < r) (n : ℕ) (f : (zeroDisc (K := K) r).AnalyticFunctions) : K :=
  WeightedPolynomialCompletion.coefficientMap (fun _ : PUnit.{1} => r) (fun _ => hr)
    (Finsupp.single PUnit.unit n) (discToWeighted r hr f)

theorem continuous_discCoefficient (r : ℝ≥0) (hr : 0 < r) (n : ℕ) :
    Continuous (discCoefficient (K := K) r hr n) :=
  (WeightedPolynomialCompletion.coefficientMap (fun _ : PUnit.{1} => r) (fun _ => hr)
    (Finsupp.single PUnit.unit n)).continuous.comp (continuous_discToWeighted r hr)

theorem discCoefficient_polynomialMap (r : ℝ≥0) (hr : 0 < r) (n : ℕ) (p : K[X]) :
    discCoefficient r hr n ((zeroDisc (K := K) r).polynomialAnalyticMap p) = p.coeff n := by
  rw [discCoefficient,discToWeighted_polynomialMap]
  change WeightedPolynomialCompletion.coefficientMap (fun _ : PUnit.{1} => r) (fun _ => hr)
    (Finsupp.single PUnit.unit n) (WeightedPolynomialCompletion.polynomialMap _ _
      ((MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm p)) = _
  rw [WeightedPolynomialCompletion.coefficientMap_polynomialMap,MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp only [Finsupp.single_eq_same]

theorem nnnorm_discCoefficient_mul_radius_le (r : ℝ≥0) (hr : 0 < r) (n : ℕ)
    (f : (zeroDisc (K := K) r).AnalyticFunctions) :
    ‖discCoefficient r hr n f‖₊*r^n ≤ ‖f‖₊ := by
  have h := WeightedPolynomialCompletion.nnnorm_coefficientMap_weight_le
    (fun _ : PUnit.{1} => r) (fun _ => hr) (Finsupp.single PUnit.unit n) (discToWeighted r hr f)
  rw [nnnorm_discToWeighted] at h
  simpa only [discCoefficient,WeightedPolynomial.weight_single] using h

theorem discCoefficient_ext (r : ℝ≥0) (hr : 0 < r)
    {f g : (zeroDisc (K := K) r).AnalyticFunctions}
    (h : ∀ n, discCoefficient r hr n f = discCoefficient r hr n g) : f = g := by
  apply (discToWeighted r hr).injective
  apply WeightedPolynomialCompletion.coefficientMap_ext
  intro d
  have hd : d = Finsupp.single PUnit.unit (d PUnit.unit) := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  rw [hd]
  exact h (d PUnit.unit)

variable [IsAlgClosed K]

theorem discCoefficient_restriction (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    (n : ℕ) (f : (zeroDisc (K := K) r).AnalyticFunctions) :
    discCoefficient s hs n ((zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s)
      (zeroDisc_carrier_subset hsr) f) = discCoefficient r hr n f := by
  exact congrFun ((denseRange_polynomialAnalyticMap_zeroDisc r).equalizer
    ((continuous_discCoefficient s hs n).comp ((zeroDisc (K := K) r).continuous_analyticRestriction _ _))
    (continuous_discCoefficient r hr n)
    (funext fun p => by
      change discCoefficient s hs n ((zeroDisc (K := K) r).analyticRestriction _ _
        ((zeroDisc (K := K) r).polynomialAnalyticMap p)) =
        discCoefficient r hr n ((zeroDisc (K := K) r).polynomialAnalyticMap p)
      rw [(zeroDisc (K := K) r).analyticRestriction_polynomial,discCoefficient_polynomialMap,
        discCoefficient_polynomialMap])) f

/-- Actual compatibility forces the SAME original coefficient on every positive-radius disc. -/
theorem discCoefficient_eq_of_compatible
    (c : ∀ r : ℝ≥0, (zeroDisc (K := K) r).AnalyticFunctions)
    (hc : ∀ r s (hsr : s ≤ r), (zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s)
      (zeroDisc_carrier_subset hsr) (c r) = c s)
    (r : ℝ≥0) (hr : 0 < r) (n : ℕ) :
    discCoefficient r hr n (c r) = discCoefficient 1 zero_lt_one n (c 1) := by
  by_cases h1r : 1 ≤ r
  · have he := discCoefficient_restriction r 1 hr zero_lt_one h1r n (c r)
    rw [hc r 1 h1r] at he
    exact he.symm
  · have hr1 : r ≤ 1 := le_of_not_ge h1r
    have he := discCoefficient_restriction 1 r zero_lt_one hr hr1 n (c 1)
    rw [hc 1 r hr1] at he
    exact he

/-- The actual all-radius growth inequality forces each higher coefficient norm to vanish. -/
theorem eq_zero_of_radius_growth (a C : ℝ≥0) (N n : ℕ) (hn : N < n)
    (h : ∀ r : ℝ≥0, 1 ≤ r → a*r^n ≤ C*r^N) : a = 0 := by
  by_contra ha
  have hapos : 0 < a := pos_iff_ne_zero.mpr ha
  let r := max 1 ((C+1)/a)
  have h1r : 1 ≤ r := le_max_left _ _
  have hr : 0 < r := zero_lt_one.trans_le h1r
  have hcancel : a*r^(n-N) ≤ C := by
    apply (mul_le_mul_iff_left₀ (pow_pos hr N)).mp
    calc
      (a*r^(n-N))*r^N = a*r^n := by
        rw [mul_assoc,← pow_add,Nat.sub_add_cancel hn.le]
      _ ≤ C*r^N := h r h1r
  have hpow : r ≤ r^(n-N) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show n-N ≠ 0 by omega)
    rw [hk,pow_succ]
    exact le_mul_of_one_le_left zero_le (one_le_pow₀ h1r)
  have hsmall : a*r ≤ C := (mul_le_mul' le_rfl hpow).trans hcancel
  have hbig : C+1 ≤ a*r := by
    have hh := (div_le_iff₀ hapos).mp (le_max_right 1 ((C+1)/a))
    simpa only [mul_comm] using hh
  exact (not_le_of_gt (lt_add_one C)) (hbig.trans hsmall)

theorem discCoefficient_eq_zero_of_growth
    (c : ∀ r : ℝ≥0, (zeroDisc (K := K) r).AnalyticFunctions)
    (hc : ∀ r s (hsr : s ≤ r), (zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s)
      (zeroDisc_carrier_subset hsr) (c r) = c s)
    (C : ℝ≥0) (N : ℕ) (hC : ∀ r, ‖c r‖₊ ≤ C*(max 1 r)^N) {n : ℕ} (hn : N < n) :
    discCoefficient 1 zero_lt_one n (c 1) = 0 := by
  apply nnnorm_eq_zero.mp
  apply eq_zero_of_radius_growth _ C N n hn
  intro r h1r
  have hr : 0 < r := zero_lt_one.trans_le h1r
  have hb := nnnorm_discCoefficient_mul_radius_le r hr n (c r)
  rw [discCoefficient_eq_of_compatible c hc r hr n] at hb
  exact hb.trans (by simpa only [max_eq_right h1r] using hC r)

/-- FULL actual Liouville: one ORIGINAL degree-bounded polynomial recovers EVERY whole disc function, including radius zero. -/
theorem exists_polynomial_of_compatible_growth
    (c : ∀ r : ℝ≥0, (zeroDisc (K := K) r).AnalyticFunctions)
    (hc : ∀ r s (hsr : s ≤ r), (zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s)
      (zeroDisc_carrier_subset hsr) (c r) = c s)
    (C : ℝ≥0) (N : ℕ) (hC : ∀ r, ‖c r‖₊ ≤ C*(max 1 r)^N) :
    ∃ P : K[X], P.natDegree ≤ N ∧ ∀ r, c r = (zeroDisc (K := K) r).polynomialAnalyticMap P := by
  classical
  let a : ℕ → K := fun n => discCoefficient 1 zero_lt_one n (c 1)
  let P : K[X] := ∑ i ∈ Finset.range (N+1), Polynomial.monomial i (a i)
  have hazero (n : ℕ) (hn : N < n) : a n = 0 :=
    discCoefficient_eq_zero_of_growth c hc C N hC hn
  have hcoeff (n : ℕ) : P.coeff n = a n := by
    by_cases hn : n < N+1
    · simp [P,Polynomial.coeff_monomial,hn]
    · have ha0 := hazero n (by omega)
      simp [P,Polynomial.coeff_monomial,hn,ha0]
  refine ⟨P,?_,?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [hcoeff]
    exact hazero n hn
  · intro r
    by_cases hr : 0 < r
    · apply discCoefficient_ext r hr
      intro n
      rw [discCoefficient_eq_of_compatible c hc r hr n,discCoefficient_polynomialMap,hcoeff]
    · have hr0 : r = 0 := le_antisymm (le_of_not_gt hr) zero_le
      subst r
      have h1 : c 1 = (zeroDisc (K := K) 1).polynomialAnalyticMap P := by
        apply discCoefficient_ext 1 zero_lt_one
        intro n
        rw [discCoefficient_polynomialMap,hcoeff]
      have he := hc 1 0 zero_le_one
      rw [h1,(zeroDisc (K := K) 1).analyticRestriction_polynomial] at he
      exact he.symm
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
