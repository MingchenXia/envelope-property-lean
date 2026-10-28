/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.MonicGaussDivision
import EnvelopeProperty.WeightedPolynomialCompletion
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Normed.Group.HomCompletion

/-! # Genuine completed bounded monic division retaining original remainder coefficients -/
open scoped NNReal Polynomial Topology
open Polynomial UniformSpace Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
open MonicGaussDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A]

/-- The ACTUAL existing one-variable weighted polynomial completion. -/
abbrev Ring (r : ℝ≥0) (hr : 0 < r) :=
  WeightedPolynomialCompletion.Ring (A := A) (fun _ : PUnit.{1} => r) (fun _ => hr)

private abbrev Source (r : ℝ≥0) (hr : 0 < r) :=
  WeightedPolynomialCompletion.PolynomialRing (A := A) (fun _ : PUnit.{1} => r) (fun _ => hr)

private def sourceToPolynomial (r : ℝ≥0) (hr : 0 < r) : Source (A := A) r hr →+* A[X] :=
  (MvPolynomial.uniqueAlgEquiv A PUnit.{1}).toRingHom.comp
    (WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).toRingHom

private theorem gauss_sourceToPolynomial (r : ℝ≥0) (hr : 0 < r) (f : Source (A := A) r hr) :
    gauss r (sourceToPolynomial r hr f) = ‖f‖₊ := by
  rw [gauss_eq_weighted, WeightedPolynomialCompletion.nnnorm_polynomial]
  exact congrArg (WeightedPolynomial.gauss (fun _ : PUnit.{1} => r))
    ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm_apply_apply _)

/-- The entire ORIGINAL polynomial RingHom into the actual completed ring. -/
def polynomialMap (r : ℝ≥0) (hr : 0 < r) : A[X] →+* Ring (A := A) r hr :=
  (WeightedPolynomialCompletion.polynomialMap (fun _ : PUnit.{1} => r) (fun _ => hr)).comp
    (MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm.toRingHom

/-- Every original polynomial retains its EXACT whole coefficient Gauss norm. -/
@[simp]
theorem nnnorm_polynomialMap (r : ℝ≥0) (hr : 0 < r) (f : A[X]) :
    ‖polynomialMap r hr f‖₊ = gauss r f := by
  exact (WeightedPolynomialCompletion.nnnorm_polynomialMap _ _ _).trans (gauss_eq_weighted r f).symm

/-- The WHOLE original polynomial image is genuinely dense. -/
theorem denseRange_polynomialMap (r : ℝ≥0) (hr : 0 < r) :
    DenseRange (polynomialMap (A := A) r hr) := by
  change Dense (Set.range ((WeightedPolynomialCompletion.polynomialMap
    (fun _ : PUnit.{1} => r) (fun _ => hr)) ∘ (MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm))
  rw [(MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm.surjective.range_comp]
  exact WeightedPolynomialCompletion.denseRange_polynomialMap _ _

private def quotientPolynomial {p : A[X]} (hp : p.Monic) : A[X] →+ A[X] where
  toFun f := f /ₘ p
  map_zero' := zero_divByMonic p
  map_add' f g := by
    apply hp.isRegular.1
    change p * ((f+g) /ₘ p) = p * (f /ₘ p + g /ₘ p)
    have hmul (t : A[X]) : p * (t /ₘ p) = t - t %ₘ p :=
      eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using modByMonic_add_div t p)
    rw [mul_add, hmul, hmul, hmul, add_modByMonic]
    ring

private def quotientSource (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic) :
    Source (A := A) r hr →+ Ring (A := A) r hr :=
  (polynomialMap r hr).toAddMonoidHom.comp
    ((quotientPolynomial hp).comp (sourceToPolynomial r hr).toAddMonoidHom)

private def quotientSourceBounded (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    NormedAddGroupHom (Source (A := A) r hr) (Ring (A := A) r hr) :=
  (quotientSource r hr hp).mkNormedAddGroupHom' (r ^ p.natDegree)⁻¹ fun f => by
    change ‖polynomialMap r hr ((sourceToPolynomial r hr f) /ₘ p)‖₊ ≤ _
    rw [nnnorm_polynomialMap]
    simpa only [div_eq_mul_inv, mul_comm, gauss_sourceToPolynomial] using
      gauss_divByMonic_le r hr hp hbound (sourceToPolynomial r hr f)

/-- The actual bounded ADDITIVE monic quotient on EVERY completed function. -/
def quotientMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    NormedAddGroupHom (Ring (A := A) r hr) (Ring (A := A) r hr) :=
  (quotientSourceBounded r hr hp hbound).extension

/-- The ACTUAL completed quotient restricts to the ORIGINAL algebraic monic quotient. -/
@[simp]
theorem quotientMap_polynomialMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (f : A[X]) :
    quotientMap r hr hp hbound (polynomialMap r hr f) = polynomialMap r hr (f /ₘ p) := by
  change (quotientSourceBounded r hr hp hbound).extension
    (((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f) : Source r hr) : Completion (Source r hr)) = _
  rw [NormedAddGroupHom.extension_coe]
  change polynomialMap r hr (((MvPolynomial.uniqueAlgEquiv A PUnit.{1})
    ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr))
      ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
        ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f)))) /ₘ p) = _
  rw [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- The sharp quotient bound holds on EVERY completed function. -/
theorem nnnorm_quotientMap_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    ‖quotientMap r hr hp hbound f‖₊ ≤ ‖f‖₊ / r ^ p.natDegree := by
  refine (denseRange_polynomialMap r hr).induction_on f
    (isClosed_le ((quotientMap r hr hp hbound).continuous.nnnorm)
      (continuous_nnnorm.div_const _)) ?_
  intro g
  rw [quotientMap_polynomialMap, nnnorm_polynomialMap, nnnorm_polynomialMap]
  exact gauss_divByMonic_le r hr hp hbound g

private def remainderCoefficientSource (r : ℝ≥0) (hr : 0 < r) (p : A[X]) (i : ℕ) :
    Source (A := A) r hr →+ A where
  toFun f := ((sourceToPolynomial r hr f) %ₘ p).coeff i
  map_zero' := by simp
  map_add' f g := by simp only [map_add, add_modByMonic, coeff_add]

private def remainderCoefficientSourceBounded (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (i : ℕ) :
    NormedAddGroupHom (Source (A := A) r hr) A :=
  (remainderCoefficientSource r hr p i).mkNormedAddGroupHom' (r ^ i)⁻¹ fun f => by
    change ‖((sourceToPolynomial r hr f) %ₘ p).coeff i‖₊ ≤ _
    rw [mul_comm]
    apply (le_div_iff₀ (pow_pos hr i)).mpr
    rw [← gauss_sourceToPolynomial r hr f]
    exact (le_gauss r _ i).trans (gauss_modByMonic_le r hr hp hbound _)

variable [T0Space A] [CompleteSpace A]

/-- The actual original A-valued remainder coefficients, obtained by genuine bounded completion. -/
def remainderCoefficientMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (i : ℕ) :
    NormedAddGroupHom (Ring (A := A) r hr) A :=
  (remainderCoefficientSourceBounded r hr hp hbound i).extension

/-- Every original remainder coefficient restricts to its ACTUAL algebraic monic-division value. -/
@[simp]
theorem remainderCoefficientMap_polynomialMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (i : ℕ) (f : A[X]) :
    remainderCoefficientMap r hr hp hbound i (polynomialMap r hr f) = (f %ₘ p).coeff i := by
  change (remainderCoefficientSourceBounded r hr hp hbound i).extension
    (((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
      ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f) : Source r hr) : Completion (Source r hr)) = _
  rw [NormedAddGroupHom.extension_coe]
  change (((MvPolynomial.uniqueAlgEquiv A PUnit.{1})
    ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr))
      ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
        ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm f)))) %ₘ p).coeff i = _
  rw [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- Each original A-valued completed remainder coefficient obeys its genuine weighted estimate. -/
theorem nnnorm_remainderCoefficientMap_mul_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (i : ℕ) (f : Ring (A := A) r hr) :
    ‖remainderCoefficientMap r hr hp hbound i f‖₊ * r ^ i ≤ ‖f‖₊ := by
  refine (denseRange_polynomialMap r hr).induction_on f
    (isClosed_le (((remainderCoefficientMap r hr hp hbound i).continuous.nnnorm).mul_const _)
      continuous_nnnorm) ?_
  intro g
  rw [remainderCoefficientMap_polynomialMap, nnnorm_polynomialMap]
  exact (le_gauss r _ i).trans (gauss_modByMonic_le r hr hp hbound g)

/-- The true remainder is an ORIGINAL finite polynomial with coefficients in the SAME A. -/
def remainderPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) : A[X] :=
  ∑ i : Fin p.natDegree, monomial i (remainderCoefficientMap r hr hp hbound i f)

/-- The ORIGINAL finite remainder polynomial has genuinely degree below d, including d=0. -/
theorem degree_remainderPolynomial_lt (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    (remainderPolynomial r hr hp hbound f).degree < (p.natDegree : WithBot ℕ) := by
  classical
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  rw [remainderPolynomial, finsetSum_coeff]
  exact Finset.sum_eq_zero fun i _ => by
    rw [coeff_monomial, if_neg (by have hi := i.isLt; omega)]

/-- Original polynomials retain the ENTIRE actual monic algebraic remainder. -/
@[simp]
theorem remainderPolynomial_polynomialMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (f : A[X]) :
    remainderPolynomial r hr hp hbound (polynomialMap r hr f) = f %ₘ p := by
  simp only [remainderPolynomial, remainderCoefficientMap_polynomialMap]
  exact sum_modByMonic_coeff hp p.degree_le_natDegree

/-- The true polynomial remainder retains each actual original completed A-coefficient. -/
theorem coeff_remainderPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) (n : ℕ) :
    (remainderPolynomial r hr hp hbound f).coeff n =
      if n < p.natDegree then remainderCoefficientMap r hr hp hbound n f else 0 := by
  classical
  rw [remainderPolynomial, finsetSum_coeff]
  split_ifs with hn
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin p.natDegree)]
    · simp only [coeff_monomial, if_true]
    · intro i _ hi
      rw [coeff_monomial, if_neg (by
        intro he
        exact hi (Fin.ext he))]
    · simp
  · exact Finset.sum_eq_zero fun i _ => by
      rw [coeff_monomial, if_neg (by have hi := i.isLt; omega)]

/-- The whole ORIGINAL polynomial remainder is contractive for every completed function. -/
theorem gauss_remainderPolynomial_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) : gauss r (remainderPolynomial r hr hp hbound f) ≤ ‖f‖₊ := by
  apply (gauss_le_iff _ _ _).mpr
  intro n
  rw [coeff_remainderPolynomial]
  split_ifs
  · exact nnnorm_remainderCoefficientMap_mul_le r hr hp hbound n f
  · simp

omit [IsUltrametricDist A] [T0Space A] [CompleteSpace A] in
private theorem gauss_monomial (r : ℝ≥0) (i : ℕ) (a : A) :
    gauss r (monomial i a) = ‖a‖₊ * r ^ i := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp [gauss, support_monomial, ha]

omit [T0Space A] [CompleteSpace A] in
private theorem continuous_polynomialMap_C (r : ℝ≥0) (hr : 0 < r) :
    Continuous ((polynomialMap (A := A) r hr).comp C) := by
  have he (a : A) : ‖((polynomialMap r hr).comp C) a‖ = ‖a‖ := by
    exact congrArg ((↑) : ℝ≥0 → ℝ) (show ‖polynomialMap r hr (C a)‖₊ = ‖a‖₊ from by
      rw [nnnorm_polynomialMap]
      exact (gauss_monomial r 0 a).trans (by simp))
  exact (AddMonoidHomClass.isometry_of_norm ((polynomialMap r hr).comp C) he).continuous

/-- The actual finite original remainder polynomial has a continuous entire image in the completion. -/
theorem continuous_remainderPolynomial_image (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Continuous (fun f : Ring (A := A) r hr => polynomialMap r hr (remainderPolynomial r hr hp hbound f)) := by
  classical
  simp only [remainderPolynomial, map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_polynomialMap_C r hr).comp
    (remainderCoefficientMap r hr hp hbound i).continuous).mul continuous_const

/-- Every ACTUAL completed function has the original monic quotient and SAME-A polynomial remainder. -/
theorem quotient_remainder_reconstruction (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    polynomialMap r hr p * quotientMap r hr hp hbound f +
      polynomialMap r hr (remainderPolynomial r hr hp hbound f) = f := by
  refine (denseRange_polynomialMap r hr).induction_on f
    (isClosed_eq ((continuous_const.mul (quotientMap r hr hp hbound).continuous).add
      (continuous_remainderPolynomial_image r hr hp hbound)) continuous_id) ?_
  intro g
  rw [quotientMap_polynomialMap, remainderPolynomial_polynomialMap, ← map_mul, ← map_add,
    add_comm, modByMonic_add_div]

omit [T0Space A] [CompleteSpace A] in
/-- The sharp original polynomial joint norm persists for EVERY actual completed quotient. -/
theorem nnnorm_monic_mul_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (q : Ring (A := A) r hr) (s : A[X]) (hs : s.degree < (p.natDegree : WithBot ℕ)) :
    ‖polynomialMap r hr p * q + polynomialMap r hr s‖₊ =
      max (r ^ p.natDegree * ‖q‖₊) (gauss r s) := by
  refine (denseRange_polynomialMap r hr).induction_on q
    (isClosed_eq ((continuous_const.mul continuous_id).add continuous_const).nnnorm
      ((continuous_const.mul continuous_nnnorm).max continuous_const)) ?_
  intro g
  rw [← map_mul, ← map_add, nnnorm_polynomialMap, nnnorm_polynomialMap]
  exact gauss_monic_mul_add r hr hp hbound g s hs

omit [CompleteSpace A] in
/-- Separation of the ORIGINAL coefficient ring derives injection of the WHOLE polynomial map. -/
theorem polynomialMap_injective (r : ℝ≥0) (hr : 0 < r) :
    Function.Injective (polynomialMap (A := A) r hr) := by
  intro f g he
  have hz : gauss r (f-g) = 0 := by
    rw [← nnnorm_polynomialMap r hr, map_sub, he, sub_self, nnnorm_zero]
  apply Polynomial.ext
  intro i
  have hi := le_gauss r (f-g) i
  rw [hz] at hi
  have hn : ‖(f-g).coeff i‖₊ = 0 :=
    (mul_eq_zero.mp (le_antisymm hi zero_le)).resolve_right (pow_pos hr i).ne'
  apply (Metric.inseparable_iff_nndist.mpr ?_).eq
  simpa only [nndist_eq_nnnorm, coeff_sub] using hn

/-- Every actual completed normal form has the EXACT sharp joint norm. -/
theorem nnnorm_quotient_remainder (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    ‖f‖₊ = max (r ^ p.natDegree * ‖quotientMap r hr hp hbound f‖₊)
      (gauss r (remainderPolynomial r hr hp hbound f)) := by
  have he := nnnorm_monic_mul_add r hr hp hbound
    (quotientMap r hr hp hbound f) (remainderPolynomial r hr hp hbound f)
    (degree_remainderPolynomial_lt r hr hp hbound f)
  rwa [quotient_remainder_reconstruction] at he

omit [CompleteSpace A] in
/-- The actual entire quotient and ORIGINAL A-polynomial remainder are unique. -/
theorem normalForm_unique (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (q₁ q₂ : Ring (A := A) r hr) (s₁ s₂ : A[X])
    (hs₁ : s₁.degree < (p.natDegree : WithBot ℕ))
    (hs₂ : s₂.degree < (p.natDegree : WithBot ℕ))
    (he : polynomialMap r hr p * q₁ + polynomialMap r hr s₁ =
      polynomialMap r hr p * q₂ + polynomialMap r hr s₂) : q₁ = q₂ ∧ s₁ = s₂ := by
  have hs : (s₁-s₂).degree < (p.natDegree : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt hs₁ hs₂)
  have hz : polynomialMap r hr p * (q₁-q₂) + polynomialMap r hr (s₁-s₂) = 0 := by
    rw [map_sub]
    linear_combination he
  have hn := nnnorm_monic_mul_add r hr hp hbound (q₁-q₂) (s₁-s₂) hs
  rw [hz, nnnorm_zero] at hn
  have hq : ‖q₁-q₂‖₊ = 0 :=
    (mul_eq_zero.mp (le_antisymm ((le_max_left _ _).trans_eq hn.symm) zero_le)).resolve_left
      (pow_pos hr _).ne'
  have hs' : gauss r (s₁-s₂) = 0 :=
    le_antisymm ((le_max_right _ _).trans_eq hn.symm) zero_le
  refine ⟨sub_eq_zero.mp (nnnorm_eq_zero.mp hq), ?_⟩
  apply polynomialMap_injective r hr
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact nnnorm_eq_zero.mp ((nnnorm_polynomialMap r hr _).trans hs')

/-- A genuine existence-and-uniqueness normal form for EVERY original completed function. -/
theorem existsUnique_normalForm (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    ∃! qr : Ring (A := A) r hr × A[X],
      qr.2.degree < (p.natDegree : WithBot ℕ) ∧
        polynomialMap r hr p * qr.1 + polynomialMap r hr qr.2 = f := by
  refine ⟨⟨quotientMap r hr hp hbound f, remainderPolynomial r hr hp hbound f⟩,
    ⟨degree_remainderPolynomial_lt r hr hp hbound f,
      quotient_remainder_reconstruction r hr hp hbound f⟩, ?_⟩
  intro qr hqr
  have he := normalForm_unique r hr hp hbound qr.1 (quotientMap r hr hp hbound f)
    qr.2 (remainderPolynomial r hr hp hbound f) hqr.1
    (degree_remainderPolynomial_lt r hr hp hbound f)
    (hqr.2.trans (quotient_remainder_reconstruction r hr hp hbound f).symm)
  exact Prod.ext he.1 he.2

/-- The ACTUAL finite family of original A-valued remainder coefficients. -/
def remainderCoefficients (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Ring (A := A) r hr →+ (Fin p.natDegree → A) where
  toFun f i := remainderCoefficientMap r hr hp hbound i f
  map_zero' := by ext i; exact map_zero _
  map_add' f g := by ext i; exact map_add _ _ _

/-- Completeness of the SAME A gives genuine continuous finite remainder coordinates. -/
theorem continuous_remainderCoefficients (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Continuous (remainderCoefficients r hr hp hbound) :=
  continuous_pi fun i => (remainderCoefficientMap r hr hp hbound i).continuous

omit [IsUltrametricDist A] [T0Space A] [CompleteSpace A] in
private theorem polynomial_divByMonic_smul {p : A[X]} (hp : p.Monic) (a : A) (f : A[X]) :
    (a • f) /ₘ p = a • (f /ₘ p) := by
  apply hp.isRegular.1
  change p * ((a • f) /ₘ p) = p * (a • (f /ₘ p))
  have hmul (t : A[X]) : p * (t /ₘ p) = t - t %ₘ p :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using modByMonic_add_div t p)
  rw [mul_smul_comm, hmul, hmul, smul_modByMonic, smul_sub]

omit [T0Space A] [CompleteSpace A] in
/-- The whole completed quotient respects the ACTUAL original coefficient action. -/
theorem quotientMap_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (a : A) (f : Ring (A := A) r hr) :
    quotientMap r hr hp hbound (polynomialMap r hr (C a) * f) =
      polynomialMap r hr (C a) * quotientMap r hr hp hbound f := by
  refine (denseRange_polynomialMap r hr).induction_on f
    (isClosed_eq ((quotientMap r hr hp hbound).continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul (quotientMap r hr hp hbound).continuous)) ?_
  intro g
  rw [← map_mul, quotientMap_polynomialMap, quotientMap_polynomialMap, ← map_mul]
  apply congrArg (polynomialMap r hr)
  simpa only [smul_eq_C_mul] using polynomial_divByMonic_smul hp a g

/-- Every original completed remainder coefficient respects the WHOLE actual A-action. -/
theorem remainderCoefficientMap_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (i : ℕ) (a : A) (f : Ring (A := A) r hr) :
    remainderCoefficientMap r hr hp hbound i (polynomialMap r hr (C a) * f) =
      a * remainderCoefficientMap r hr hp hbound i f := by
  refine (denseRange_polynomialMap r hr).induction_on f
    (isClosed_eq ((remainderCoefficientMap r hr hp hbound i).continuous.comp
      (continuous_const.mul continuous_id))
      (continuous_const.mul (remainderCoefficientMap r hr hp hbound i).continuous)) ?_
  intro g
  rw [← map_mul, remainderCoefficientMap_polynomialMap, remainderCoefficientMap_polynomialMap]
  simpa only [smul_eq_C_mul, coeff_C_mul] using congrArg (fun t : A[X] => t.coeff i)
    (smul_modByMonic (q := p) a g)

/-- The actual original finite polynomial remainder has the original full coefficient action. -/
theorem remainderPolynomial_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (a : A) (f : Ring (A := A) r hr) :
    remainderPolynomial r hr hp hbound (polynomialMap r hr (C a) * f) =
      a • remainderPolynomial r hr hp hbound f := by
  apply Polynomial.ext
  intro i
  rw [coeff_smul, coeff_remainderPolynomial, coeff_remainderPolynomial]
  split_ifs
  · exact remainderCoefficientMap_coeff_mul r hr hp hbound i a f
  · exact (mul_zero a).symm

/-- The original polynomial remainder is genuinely additive on ALL completed functions. -/
theorem remainderPolynomial_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f g : Ring (A := A) r hr) :
    remainderPolynomial r hr hp hbound (f+g) =
      remainderPolynomial r hr hp hbound f + remainderPolynomial r hr hp hbound g := by
  apply Polynomial.ext
  intro i
  rw [coeff_add, coeff_remainderPolynomial, coeff_remainderPolynomial, coeff_remainderPolynomial]
  split_ifs
  · exact map_add _ _ _
  · exact (zero_add (0 : A)).symm

end EnvelopeProperty.CompletedMonicDivision
