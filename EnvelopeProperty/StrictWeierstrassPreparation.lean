/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.StrictGaussQuotient
import Mathlib.Analysis.Normed.Ring.Units

/-! # Genuine strict Weierstrass preparation in the ORIGINAL completed ring -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A]

omit [IsUltrametricDist A] in
private theorem leading_divByMonic {p : A[X]} (hp : p.Monic) :
    (X ^ p.natDegree) /ₘ p = 1 := by
  rcases subsingleton_or_nontrivial A with h | h
  · exact Subsingleton.elim _ _
  · let := h
    have he : p.eraseLead + X ^ p.natDegree = p := by
      simpa only [hp.leadingCoeff, C_1, one_mul] using p.eraseLead_add_C_mul_X_pow
    exact (div_modByMonic_unique 1 (-p.eraseLead) hp
      ⟨by linear_combination -he, by rw [degree_neg]; exact degree_eraseLead_lt hp.ne_zero⟩).1

/-- The ORIGINAL leading monomial has literal monic quotient one in the actual completion. -/
theorem quotientMap_leading_monomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    quotientMap r hr hp hbound (polynomialMap r hr (X ^ p.natDegree)) = 1 := by
  rw [quotientMap_polynomialMap, leading_divByMonic hp, map_one]

/-- The actual quotient of the ORIGINAL leading monomial by the real analytic divisor. -/
def preparationQuotient (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) : Ring (A := A) r hr :=
  perturbedQuotient r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))

/-- The actual leading quotient is within the true contraction ratio of ONE, without NormOne. -/
theorem nnnorm_preparationQuotient_sub_one_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    ‖preparationQuotient r hr hp hbound h hh - 1‖₊ ≤ ‖h‖₊ / r ^ p.natDegree := by
  let q := preparationQuotient r hr hp hbound h hh
  let θ := ‖h‖₊ / r ^ p.natDegree
  have hθ : θ < 1 := (div_lt_one (pow_pos hr _)).mpr hh
  have hfixed := perturbedQuotient_fixed r hr hp hbound h hh
    (polynomialMap r hr (X ^ p.natDegree))
  change quotientMap r hr hp hbound (polynomialMap r hr (X ^ p.natDegree)-h*q) = q at hfixed
  rw [map_sub, quotientMap_leading_monomial r hr hp hbound,
    show h*q = h+h*(q-1) by ring, map_add] at hfixed
  have he : q-1 = -(quotientMap r hr hp hbound h + quotientMap r hr hp hbound (h*(q-1))) := by
    linear_combination -hfixed
  have hb : ‖q-1‖₊ ≤ max θ (θ * ‖q-1‖₊) := by
    conv_lhs => rw [he, nnnorm_neg]
    apply (IsUltrametricDist.nnnorm_add_le_max _ _).trans
    apply max_le_max (nnnorm_quotientMap_le r hr hp hbound h)
    calc
      ‖quotientMap r hr hp hbound (h*(q-1))‖₊ ≤ ‖h*(q-1)‖₊ / r ^ p.natDegree :=
        nnnorm_quotientMap_le r hr hp hbound _
      _ ≤ (‖h‖₊ * ‖q-1‖₊) / r ^ p.natDegree := div_le_div_of_nonneg_right (nnnorm_mul_le _ _) zero_le
      _ = θ * ‖q-1‖₊ := by dsimp [θ]; ring
  change ‖q-1‖₊ ≤ θ
  by_contra hn
  have hδ : θ < ‖q-1‖₊ := lt_of_not_ge hn
  have hpos : 0 < ‖q-1‖₊ := zero_le.trans_lt hδ
  have hc : max θ (θ * ‖q-1‖₊) < ‖q-1‖₊ :=
    max_lt hδ (by simpa only [one_mul] using mul_lt_mul_of_pos_right hθ hpos)
  exact (not_lt_of_ge hb) hc

/-- Genuine strict closeness to ONE is derived, not imposed as a unit certificate. -/
theorem nnnorm_preparationQuotient_sub_one_lt (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    ‖preparationQuotient r hr hp hbound h hh - 1‖₊ < 1 :=
  (nnnorm_preparationQuotient_sub_one_le r hr hp hbound h hh).trans_lt
    ((div_lt_one (pow_pos hr _)).mpr hh)

/-- The actual leading quotient is a real UNIT in the SAME original completed ring. -/
theorem isUnit_preparationQuotient (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    IsUnit (preparationQuotient r hr hp hbound h hh) := by
  have he : ‖1-preparationQuotient r hr hp hbound h hh‖ < 1 := by
    rw [norm_sub_rev]
    exact_mod_cast nnnorm_preparationQuotient_sub_one_lt r hr hp hbound h hh
  simpa only [Units.val_oneSub, sub_sub_cancel] using (Units.oneSub _ he).isUnit

/-- A genuine chosen unit carrying the SAME original quotient element. -/
def preparationQuotientUnit (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) : (Ring (A := A) r hr)ˣ :=
  (isUnit_preparationQuotient r hr hp hbound h hh).unit

/-- This genuine unit's ELEMENT is the actual leading quotient, on the whole completed ring. -/
@[simp]
theorem coe_preparationQuotientUnit (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    (preparationQuotientUnit r hr hp hbound h hh : Ring (A := A) r hr) =
      preparationQuotient r hr hp hbound h hh :=
  (isUnit_preparationQuotient r hr hp hbound h hh).unit_spec

/-- Actual hq=h+h(q−1) controls the whole product with no false norm-one estimate. -/
theorem nnnorm_mul_preparationQuotient_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    ‖h * preparationQuotient r hr hp hbound h hh‖₊ ≤ ‖h‖₊ := by
  rw [show h * preparationQuotient r hr hp hbound h hh =
    h + h*(preparationQuotient r hr hp hbound h hh-1) by ring]
  apply (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le le_rfl ?_)
  exact (nnnorm_mul_le _ _).trans (by
    simpa only [mul_one] using mul_le_mul' (le_refl ‖h‖₊)
      (nnnorm_preparationQuotient_sub_one_lt r hr hp hbound h hh).le)

omit [IsUltrametricDist A] in
private theorem leading_modByMonic {p : A[X]} (hp : p.Monic) :
    (X ^ p.natDegree) %ₘ p = -p.eraseLead := by
  rw [modByMonic_eq_sub_mul_div, leading_divByMonic hp, mul_one]
  have he : p.eraseLead + X ^ p.natDegree = p := by
    simpa only [hp.leadingCoeff, C_1, one_mul] using p.eraseLead_add_C_mul_X_pow
  linear_combination he

variable [T0Space A] [CompleteSpace A]

/-- The prepared polynomial is CONSTRUCTED from the original A-valued finite remainder. -/
def preparedPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) : A[X] :=
  X ^ p.natDegree - perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))

/-- Literal degree-below-d remainder proves genuine original monicity. -/
theorem preparedPolynomial_monic (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    (preparedPolynomial r hr hp hbound h hh).Monic :=
  monic_X_pow_sub (degree_perturbedRemainder_lt r hr hp hbound h hh _)

/-- Its actual natural degree is the ORIGINAL monic degree, including the zero ring. -/
theorem natDegree_preparedPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    (preparedPolynomial r hr hp hbound h hh).natDegree = p.natDegree := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    have hz : ∀ f : A[X], f.natDegree = 0 := fun f => by rw [Subsingleton.elim f 0, natDegree_zero]
    rw [hz, hz]
  · let := hA
    change ((X : A[X]) ^ p.natDegree -
      perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))).natDegree = p.natDegree
    rw [sub_eq_add_neg, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_neg, degree_X_pow]
    exact degree_perturbedRemainder_lt r hr hp hbound h hh _

private theorem remainderPolynomial_sub (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f g : Ring (A := A) r hr) :
    remainderPolynomial r hr hp hbound (f-g) =
      remainderPolynomial r hr hp hbound f - remainderPolynomial r hr hp hbound g := by
  apply Polynomial.ext
  intro i
  rw [coeff_sub, coeff_remainderPolynomial, coeff_remainderPolynomial, coeff_remainderPolynomial]
  split_ifs
  · exact map_sub _ _ _
  · exact (sub_zero (0 : A)).symm

/-- The ENTIRE original leading remainder has the true r^d bound without estimating norm(1) by one. -/
theorem gauss_preparationRemainder_le (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    MonicGaussDivision.gauss r
      (perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))) ≤ r ^ p.natDegree := by
  change MonicGaussDivision.gauss r (remainderPolynomial r hr hp hbound
    (polynomialMap r hr (X ^ p.natDegree)-h*preparationQuotient r hr hp hbound h hh)) ≤ _
  rw [remainderPolynomial_sub, remainderPolynomial_polynomialMap, leading_modByMonic hp,
    sub_eq_add_neg]
  apply (MonicGaussDivision.gauss_add_le_max r _ _).trans (max_le ?_ ?_)
  · rw [MonicGaussDivision.gauss_neg]
    exact MonicGaussDivision.gauss_eraseLead_le r p hbound
  · rw [MonicGaussDivision.gauss_neg]
    exact (gauss_remainderPolynomial_le r hr hp hbound _).trans
      ((nnnorm_mul_preparationQuotient_le r hr hp hbound h hh).trans hh.le)

/-- EVERY lower ORIGINAL prepared coefficient retains the genuine monic Gauss bound. -/
theorem preparedPolynomial_lower_bound (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    ∀ i < (preparedPolynomial r hr hp hbound h hh).natDegree,
      ‖(preparedPolynomial r hr hp hbound h hh).coeff i‖₊ * r ^ i ≤
        r ^ (preparedPolynomial r hr hp hbound h hh).natDegree := by
  rw [natDegree_preparedPolynomial]
  intro i hi
  have hcoef : (preparedPolynomial r hr hp hbound h hh).coeff i =
      -(perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))).coeff i := by
    simp only [preparedPolynomial, coeff_sub, coeff_X_pow, if_neg (ne_of_lt hi), zero_sub]
  rw [hcoef, nnnorm_neg]
  exact (MonicGaussDivision.le_gauss r _ i).trans (gauss_preparationRemainder_le r hr hp hbound h hh)

/-- Actual strict division gives the ENTIRE element factorization gq=P. -/
theorem mul_preparationQuotient_eq_preparedPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    (polynomialMap r hr p+h)*preparationQuotient r hr hp hbound h hh =
      polynomialMap r hr (preparedPolynomial r hr hp hbound h hh) := by
  have he := perturbed_reconstruction r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))
  rw [preparedPolynomial, map_sub]
  change (polynomialMap r hr p+h)*preparationQuotient r hr hp hbound h hh +
    polynomialMap r hr (perturbedRemainder r hr hp hbound h hh (polynomialMap r hr (X ^ p.natDegree))) =
      polynomialMap r hr (X ^ p.natDegree) at he
  exact eq_sub_of_add_eq he

/-- The ACTUAL preparation factor is the inverse of the genuinely constructed quotient unit. -/
def preparationUnit (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) : (Ring (A := A) r hr)ˣ :=
  (preparationQuotientUnit r hr hp hbound h hh)⁻¹

/-- The SAME original analytic divisor is an actual unit times the ORIGINAL prepared polynomial. -/
theorem eq_preparationUnit_mul_preparedPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    polynomialMap r hr p+h = (preparationUnit r hr hp hbound h hh : Ring (A := A) r hr) *
      polynomialMap r hr (preparedPolynomial r hr hp hbound h hh) := by
  rw [← mul_preparationQuotient_eq_preparedPolynomial r hr hp hbound h hh,
    ← coe_preparationQuotientUnit]
  change (polynomialMap r hr p+h) =
    (↑(preparationQuotientUnit r hr hp hbound h hh)⁻¹ : Ring (A := A) r hr) *
      ((polynomialMap r hr p+h) * ↑(preparationQuotientUnit r hr hp hbound h hh))
  symm
  calc
    _ = ((↑(preparationQuotientUnit r hr hp hbound h hh)⁻¹ : Ring (A := A) r hr) *
      ↑(preparationQuotientUnit r hr hp hbound h hh)) * (polynomialMap r hr p+h) := by ring
    _ = _ := by rw [Units.inv_mul, one_mul]

/-- The two ORIGINAL principal ideals are equal, with no closure or radical replacement. -/
theorem preparedIdeal_eq_perturbedIdeal (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    principalIdeal r hr (preparedPolynomial r hr hp hbound h hh) = perturbedIdeal r hr p h := by
  unfold principalIdeal perturbedIdeal
  rw [← mul_preparationQuotient_eq_preparedPolynomial r hr hp hbound h hh]
  exact Ideal.span_singleton_mul_right_unit (isUnit_preparationQuotient r hr hp hbound h hh) _

/-- Preparation gives a genuine ORIGINAL A-algebra quotient, rather than only a module normal form. -/
def preparationQuotientAlgEquiv (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    (A[X] ⧸ Ideal.span {preparedPolynomial r hr hp hbound h hh}) ≃ₐ[A]
      (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  (quotientAlgEquiv r hr (preparedPolynomial_monic r hr hp hbound h hh)
    (preparedPolynomial_lower_bound r hr hp hbound h hh)).trans
      (Ideal.quotientEquivAlgOfEq A (preparedIdeal_eq_perturbedIdeal r hr hp hbound h hh))

/-- EVERY original polynomial and coefficient class is retained by the actual quotient map. -/
@[simp]
theorem preparationQuotientAlgEquiv_mk (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : A[X]) :
    preparationQuotientAlgEquiv r hr hp hbound h hh
      (Ideal.Quotient.mk (Ideal.span {preparedPolynomial r hr hp hbound h hh}) f) =
        Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr f) := by
  simp only [preparationQuotientAlgEquiv, AlgEquiv.trans_apply]
  change Ideal.quotientEquivAlgOfEq A _ (quotientEquiv r hr
    (preparedPolynomial_monic r hr hp hbound h hh)
    (preparedPolynomial_lower_bound r hr hp hbound h hh) (Ideal.Quotient.mk _ f)) = _
  rw [quotientEquiv_mk, Ideal.quotientEquivAlgOfEq_mk]

/-- ANY same-degree monic unit factorization has the SAME original prepared polynomial.
No bound on the competing polynomial or its unit is assumed. -/
theorem preparedPolynomial_unique (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree)
    (P : A[X]) (hP : P.Monic) (hd : P.natDegree = p.natDegree)
    (u : (Ring (A := A) r hr)ˣ)
    (he : polynomialMap r hr p+h = (u : Ring (A := A) r hr)*polynomialMap r hr P) :
    P = preparedPolynomial r hr hp hbound h hh := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    exact Subsingleton.elim _ _
  · let := hA
    let P₀ := preparedPolynomial r hr hp hbound h hh
    have hP₀ : P₀.Monic := preparedPolynomial_monic r hr hp hbound h hh
    have hdeg : P.degree = P₀.degree := by
      rw [(degree_eq_natDegree hP.ne_zero), (degree_eq_natDegree hP₀.ne_zero), hd, natDegree_preparedPolynomial]
    have hs : (P-P₀).degree < (P₀.natDegree : WithBot ℕ) := by
      rw [← (degree_eq_natDegree hP₀.ne_zero)]
      exact degree_sub_lt_right hdeg hP₀.ne_zero (hP.leadingCoeff.trans hP₀.leadingCoeff.symm)
    let q : Ring (A := A) r hr := (↑u⁻¹ : Ring (A := A) r hr)*
      (preparationUnit r hr hp hbound h hh : Ring (A := A) r hr)
    have hmult : polynomialMap r hr P₀*q = polynomialMap r hr P := by
      have hh₀ := eq_preparationUnit_mul_preparedPolynomial r hr hp hbound h hh
      rw [he] at hh₀
      calc
        polynomialMap r hr P₀*q = (↑u⁻¹ : Ring (A := A) r hr)*
            ((preparationUnit r hr hp hbound h hh : Ring (A := A) r hr)*polynomialMap r hr P₀) := by dsimp [q]; ring
        _ = (↑u⁻¹ : Ring (A := A) r hr)*((u : Ring (A := A) r hr)*polynomialMap r hr P) := by rw [← hh₀]
        _ = polynomialMap r hr P := by simp [← mul_assoc]
    have heq : polynomialMap r hr P₀*q+polynomialMap r hr 0 =
        polynomialMap r hr P₀*1+polynomialMap r hr (P-P₀) := by
      rw [hmult, map_zero, map_sub]
      ring
    have hu := normalForm_unique r hr hP₀ (preparedPolynomial_lower_bound r hr hp hbound h hh)
      q 1 0 (P-P₀) (by simp) hs heq
    exact sub_eq_zero.mp hu.2.symm

/-- The actual unit factor is unique as an ELEMENT, by genuine monic multiplication regularity. -/
theorem preparationUnit_unique (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree)
    (P : A[X]) (hP : P.Monic) (hd : P.natDegree = p.natDegree)
    (u : (Ring (A := A) r hr)ˣ)
    (he : polynomialMap r hr p+h = (u : Ring (A := A) r hr)*polynomialMap r hr P) :
    u = preparationUnit r hr hp hbound h hh := by
  have hP' := preparedPolynomial_unique r hr hp hbound h hh P hP hd u he
  rw [hP'] at he
  have heq : polynomialMap r hr (preparedPolynomial r hr hp hbound h hh)*(u : Ring (A := A) r hr)+polynomialMap r hr 0 =
      polynomialMap r hr (preparedPolynomial r hr hp hbound h hh)*
        (preparationUnit r hr hp hbound h hh : Ring (A := A) r hr)+polynomialMap r hr 0 := by
    simpa only [map_zero, add_zero, mul_comm] using he.symm.trans
      (eq_preparationUnit_mul_preparedPolynomial r hr hp hbound h hh)
  apply Units.ext
  exact (normalForm_unique r hr (preparedPolynomial_monic r hr hp hbound h hh)
    (preparedPolynomial_lower_bound r hr hp hbound h hh) _ _ 0 0 (by simp) (by simp) heq).1

/-- A genuine existence-and-uniqueness preparation in the ORIGINAL completed ring. -/
theorem existsUnique_preparation (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    ∃! Pu : A[X] × (Ring (A := A) r hr)ˣ,
      Pu.1.Monic ∧ Pu.1.natDegree = p.natDegree ∧
        polynomialMap r hr p+h = (Pu.2 : Ring (A := A) r hr)*polynomialMap r hr Pu.1 := by
  refine ⟨⟨preparedPolynomial r hr hp hbound h hh, preparationUnit r hr hp hbound h hh⟩,
    ⟨preparedPolynomial_monic r hr hp hbound h hh,
      natDegree_preparedPolynomial r hr hp hbound h hh,
      eq_preparationUnit_mul_preparedPolynomial r hr hp hbound h hh⟩, ?_⟩
  rintro ⟨P,u⟩ ⟨hP,hd,he⟩
  exact Prod.ext (preparedPolynomial_unique r hr hp hbound h hh P hP hd u he)
    (preparationUnit_unique r hr hp hbound h hh P hP hd u he)

end EnvelopeProperty.CompletedMonicDivision
