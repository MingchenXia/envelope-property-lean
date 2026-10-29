/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.CompletedMonicDivision
import Mathlib.Topology.MetricSpace.Contracting

/-! # Actual strict analytic perturbation of original completed monic division -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A]

/-- A genuine strict analytic perturbation retains the sharp WHOLE joint norm. -/
theorem nnnorm_perturbed_mul_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree)
    (q : Ring (A := A) r hr) (s : A[X]) (hs : s.degree < (p.natDegree : WithBot ℕ)) :
    ‖(polynomialMap r hr p + h)*q + polynomialMap r hr s‖₊ =
      max (r ^ p.natDegree * ‖q‖₊) (MonicGaussDivision.gauss r s) := by
  by_cases hq : q = 0
  · simp only [hq, mul_zero, zero_add, nnnorm_polynomialMap, nnnorm_zero, max_eq_right zero_le]
  · have hsmall : ‖h*q‖₊ < ‖polynomialMap r hr p * q + polynomialMap r hr s‖₊ := by
      rw [nnnorm_monic_mul_add r hr hp hbound q s hs]
      exact (nnnorm_mul_le h q).trans_lt ((mul_lt_mul_of_pos_right hh (nnnorm_pos.mpr hq)).trans_le
        (le_max_left _ _))
    have he : (polynomialMap r hr p + h)*q + polynomialMap r hr s =
        (polynomialMap r hr p*q + polynomialMap r hr s) + h*q := by ring
    rw [he, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hsmall.ne',
      max_eq_left hsmall.le, nnnorm_monic_mul_add r hr hp hbound q s hs]

private def perturbationStep (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h f : Ring (A := A) r hr) (q : Ring (A := A) r hr) : Ring (A := A) r hr :=
  quotientMap r hr hp hbound (f-h*q)

private theorem perturbationStep_contracting (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    ContractingWith (‖h‖₊ / r ^ p.natDegree) (perturbationStep r hr hp hbound h f) := by
  refine ⟨(div_lt_one (pow_pos hr _)).mpr hh, LipschitzWith.of_dist_le_mul ?_⟩
  intro q₁ q₂
  have he : perturbationStep r hr hp hbound h f q₁ - perturbationStep r hr hp hbound h f q₂ =
      quotientMap r hr hp hbound (-h*(q₁-q₂)) := by
    rw [perturbationStep, perturbationStep, ← map_sub]
    congr 1
    ring
  rw [dist_eq_norm, dist_eq_norm, he]
  have hn := nnnorm_quotientMap_le r hr hp hbound (-h*(q₁-q₂))
  have hm := nnnorm_mul_le (-h) (q₁-q₂)
  rw [nnnorm_neg] at hm
  have hb : ‖quotientMap r hr hp hbound (-h*(q₁-q₂))‖₊ ≤
      (‖h‖₊ / r ^ p.natDegree) * ‖q₁-q₂‖₊ := by
    exact hn.trans (by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hm zero_le)
  exact_mod_cast hb

/-- The actual analytic quotient is CONSTRUCTED as the genuine Banach fixed point. -/
def perturbedQuotient (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    Ring (A := A) r hr :=
  (perturbationStep_contracting r hr hp hbound h hh f).fixedPoint _

/-- Its genuine whole fixed-point identity holds in the SAME original completed ring. -/
theorem perturbedQuotient_fixed (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    quotientMap r hr hp hbound (f-h*perturbedQuotient r hr hp hbound h hh f) =
      perturbedQuotient r hr hp hbound h hh f :=
  (perturbationStep_contracting r hr hp hbound h hh f).fixedPoint_isFixedPt

variable [T0Space A] [CompleteSpace A]

/-- The remainder is an ORIGINAL polynomial in A[T], not a completed-series substitute. -/
def perturbedRemainder (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) : A[X] :=
  remainderPolynomial r hr hp hbound (f-h*perturbedQuotient r hr hp hbound h hh f)

/-- The true original perturbed remainder always has degree below the original monic degree. -/
theorem degree_perturbedRemainder_lt (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    (perturbedRemainder r hr hp hbound h hh f).degree < (p.natDegree : WithBot ℕ) :=
  degree_remainderPolynomial_lt r hr hp hbound _

/-- Every actual completed function has a whole normal form for the genuine analytic divisor p+h. -/
theorem perturbed_reconstruction (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    (polynomialMap r hr p+h) * perturbedQuotient r hr hp hbound h hh f +
      polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f) = f := by
  have he := quotient_remainder_reconstruction r hr hp hbound
    (f-h*perturbedQuotient r hr hp hbound h hh f)
  rw [perturbedQuotient_fixed] at he
  change polynomialMap r hr p * perturbedQuotient r hr hp hbound h hh f +
    polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f) =
      f-h*perturbedQuotient r hr hp hbound h hh f at he
  linear_combination he

omit [CompleteSpace A] in
/-- The genuine strict perturbation normal form is unique in BOTH actual components. -/
theorem perturbedNormalForm_unique (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree)
    (q₁ q₂ : Ring (A := A) r hr) (s₁ s₂ : A[X])
    (hs₁ : s₁.degree < (p.natDegree : WithBot ℕ))
    (hs₂ : s₂.degree < (p.natDegree : WithBot ℕ))
    (he : (polynomialMap r hr p+h)*q₁ + polynomialMap r hr s₁ =
      (polynomialMap r hr p+h)*q₂ + polynomialMap r hr s₂) : q₁ = q₂ ∧ s₁ = s₂ := by
  have hs : (s₁-s₂).degree < (p.natDegree : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt hs₁ hs₂)
  have hz : (polynomialMap r hr p+h)*(q₁-q₂) + polynomialMap r hr (s₁-s₂) = 0 := by
    rw [map_sub]
    linear_combination he
  have hn := nnnorm_perturbed_mul_add r hr hp hbound h hh (q₁-q₂) (s₁-s₂) hs
  rw [hz, nnnorm_zero] at hn
  have hq : ‖q₁-q₂‖₊ = 0 :=
    (mul_eq_zero.mp (le_antisymm ((le_max_left _ _).trans_eq hn.symm) zero_le)).resolve_left
      (pow_pos hr _).ne'
  have hs' : MonicGaussDivision.gauss r (s₁-s₂) = 0 :=
    le_antisymm ((le_max_right _ _).trans_eq hn.symm) zero_le
  refine ⟨sub_eq_zero.mp (nnnorm_eq_zero.mp hq), ?_⟩
  apply polynomialMap_injective r hr
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact nnnorm_eq_zero.mp ((nnnorm_polynomialMap r hr _).trans hs')

/-- Every completed function has a genuine UNIQUE quotient and ORIGINAL polynomial remainder for p+h. -/
theorem existsUnique_perturbedNormalForm (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    ∃! qr : Ring (A := A) r hr × A[X], qr.2.degree < (p.natDegree : WithBot ℕ) ∧
      (polynomialMap r hr p+h)*qr.1 + polynomialMap r hr qr.2 = f := by
  refine ⟨⟨perturbedQuotient r hr hp hbound h hh f, perturbedRemainder r hr hp hbound h hh f⟩,
    ⟨degree_perturbedRemainder_lt r hr hp hbound h hh f,
      perturbed_reconstruction r hr hp hbound h hh f⟩, ?_⟩
  intro qr hqr
  have he := perturbedNormalForm_unique r hr hp hbound h hh qr.1
    (perturbedQuotient r hr hp hbound h hh f) qr.2 (perturbedRemainder r hr hp hbound h hh f)
    hqr.1 (degree_perturbedRemainder_lt r hr hp hbound h hh f)
    (hqr.2.trans (perturbed_reconstruction r hr hp hbound h hh f).symm)
  exact Prod.ext he.1 he.2

/-- The ACTUAL strict analytic division has the exact original sharp norm identity. -/
theorem nnnorm_perturbed_normalForm (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    ‖f‖₊ = max (r ^ p.natDegree * ‖perturbedQuotient r hr hp hbound h hh f‖₊)
      (MonicGaussDivision.gauss r (perturbedRemainder r hr hp hbound h hh f)) := by
  have he := nnnorm_perturbed_mul_add r hr hp hbound h hh
    (perturbedQuotient r hr hp hbound h hh f) (perturbedRemainder r hr hp hbound h hh f)
    (degree_perturbedRemainder_lt r hr hp hbound h hh f)
  rwa [perturbed_reconstruction] at he

private theorem perturbedPair_eq (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f q : Ring (A := A) r hr) (s : A[X])
    (hs : s.degree < (p.natDegree : WithBot ℕ))
    (he : (polynomialMap r hr p+h)*q + polynomialMap r hr s = f) :
    q = perturbedQuotient r hr hp hbound h hh f ∧
      s = perturbedRemainder r hr hp hbound h hh f :=
  perturbedNormalForm_unique r hr hp hbound h hh q (perturbedQuotient r hr hp hbound h hh f)
    s (perturbedRemainder r hr hp hbound h hh f) hs (degree_perturbedRemainder_lt r hr hp hbound h hh f)
    (he.trans (perturbed_reconstruction r hr hp hbound h hh f).symm)

private theorem perturbedPair_zero (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    0 = perturbedQuotient r hr hp hbound h hh 0 ∧
      0 = perturbedRemainder r hr hp hbound h hh 0 :=
  perturbedPair_eq r hr hp hbound h hh 0 0 0 (by simp) (by simp)

private theorem perturbedPair_add (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f g : Ring (A := A) r hr) :
    perturbedQuotient r hr hp hbound h hh f + perturbedQuotient r hr hp hbound h hh g =
      perturbedQuotient r hr hp hbound h hh (f+g) ∧
    perturbedRemainder r hr hp hbound h hh f + perturbedRemainder r hr hp hbound h hh g =
      perturbedRemainder r hr hp hbound h hh (f+g) := by
  apply perturbedPair_eq r hr hp hbound h hh
  · exact (degree_add_le _ _).trans_lt (max_lt
      (degree_perturbedRemainder_lt r hr hp hbound h hh f)
      (degree_perturbedRemainder_lt r hr hp hbound h hh g))
  · have hf := perturbed_reconstruction r hr hp hbound h hh f
    have hg := perturbed_reconstruction r hr hp hbound h hh g
    rw [map_add]
    linear_combination hf + hg

/-- The original sharp quotient estimate holds for EVERY strict analytic perturbation. -/
theorem nnnorm_perturbedQuotient_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    ‖perturbedQuotient r hr hp hbound h hh f‖₊ ≤ ‖f‖₊ / r ^ p.natDegree := by
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  rw [mul_comm, nnnorm_perturbed_normalForm r hr hp hbound h hh f]
  exact le_max_left _ _

/-- The SAME original polynomial perturbed remainder is contractive. -/
theorem gauss_perturbedRemainder_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    MonicGaussDivision.gauss r (perturbedRemainder r hr hp hbound h hh f) ≤ ‖f‖₊ := by
  rw [nnnorm_perturbed_normalForm r hr hp hbound h hh f]
  exact le_max_right _ _

/-- The CONSTRUCTED strict analytic quotient is a genuine continuous bounded additive map. -/
def perturbedQuotientMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    NormedAddGroupHom (Ring (A := A) r hr) (Ring (A := A) r hr) where
  toFun := perturbedQuotient r hr hp hbound h hh
  map_add' f g := (perturbedPair_add r hr hp hbound h hh f g).1.symm
  bound' := ⟨((r ^ p.natDegree)⁻¹ : ℝ≥0), fun f => by
    exact_mod_cast (show ‖perturbedQuotient r hr hp hbound h hh f‖₊ ≤
      (r ^ p.natDegree)⁻¹ * ‖f‖₊ from by
        simpa only [div_eq_mul_inv, mul_comm] using nnnorm_perturbedQuotient_le r hr hp hbound h hh f)⟩

private def perturbedRemainderAddHom (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) : Ring (A := A) r hr →+ A[X] where
  toFun := perturbedRemainder r hr hp hbound h hh
  map_zero' := (perturbedPair_zero r hr hp hbound h hh).2.symm
  map_add' f g := (perturbedPair_add r hr hp hbound h hh f g).2.symm

/-- The ORIGINAL polynomial remainder has a genuine contractive additive image in the same completion. -/
def perturbedRemainderMap (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    NormedAddGroupHom (Ring (A := A) r hr) (Ring (A := A) r hr) :=
  ((polynomialMap r hr).toAddMonoidHom.comp
    (perturbedRemainderAddHom r hr hp hbound h hh)).mkNormedAddGroupHom' 1 fun f => by
      change ‖polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f)‖₊ ≤ 1 * ‖f‖₊
      rw [nnnorm_polynomialMap, one_mul]
      exact gauss_perturbedRemainder_le r hr hp hbound h hh f

private theorem perturbedPair_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (a : A) (f : Ring (A := A) r hr) :
    polynomialMap r hr (C a) * perturbedQuotient r hr hp hbound h hh f =
      perturbedQuotient r hr hp hbound h hh (polynomialMap r hr (C a)*f) ∧
    a • perturbedRemainder r hr hp hbound h hh f =
      perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (C a)*f) := by
  apply perturbedPair_eq r hr hp hbound h hh
  · exact (degree_smul_le _ _).trans_lt (degree_perturbedRemainder_lt r hr hp hbound h hh f)
  · have he := perturbed_reconstruction r hr hp hbound h hh f
    rw [smul_eq_C_mul, map_mul]
    linear_combination polynomialMap r hr (C a) * he

/-- The genuine strict analytic quotient retains the WHOLE original coefficient action. -/
theorem perturbedQuotient_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (a : A) (f : Ring (A := A) r hr) :
    perturbedQuotient r hr hp hbound h hh (polynomialMap r hr (C a)*f) =
      polynomialMap r hr (C a) * perturbedQuotient r hr hp hbound h hh f :=
  (perturbedPair_coeff_mul r hr hp hbound h hh a f).1.symm

/-- Its original polynomial remainder retains EVERY actual coefficient scalar identity. -/
theorem perturbedRemainder_coeff_mul (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (a : A) (f : Ring (A := A) r hr) :
    perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (C a)*f) =
      a • perturbedRemainder r hr hp hbound h hh f :=
  (perturbedPair_coeff_mul r hr hp hbound h hh a f).2.symm

end EnvelopeProperty.CompletedMonicDivision
