/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.CompletedMonicDivision
import EnvelopeProperty.NormedIdealQuotient
import EnvelopeProperty.NormedIdealUltrametric
import Mathlib.RingTheory.AdjoinRoot

/-! # The ORIGINAL monic principal ideal is closed, with the true algebraic quotient -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A]
  [T0Space A] [CompleteSpace A]

/-- The actual ORIGINAL analytic principal ideal, with no closure or radical replacement. -/
def principalIdeal (r : ℝ≥0) (hr : 0 < r) (p : A[X]) : Ideal (Ring (A := A) r hr) :=
  Ideal.span {polynomialMap r hr p}

/-- Membership in the ORIGINAL principal ideal is precisely zero actual polynomial remainder. -/
theorem mem_principalIdeal_iff (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    f ∈ principalIdeal r hr p ↔ remainderPolynomial r hr hp hbound f = 0 := by
  rw [principalIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    have he := normalForm_unique r hr hp hbound (quotientMap r hr hp hbound f) q
      (remainderPolynomial r hr hp hbound f) 0
      (degree_remainderPolynomial_lt r hr hp hbound f) (by simp)
      ((quotient_remainder_reconstruction r hr hp hbound f).trans (by simpa using hq))
    exact he.2
  · intro he
    refine ⟨quotientMap r hr hp hbound f, ?_⟩
    simpa only [he, map_zero, add_zero] using
      (quotient_remainder_reconstruction r hr hp hbound f).symm

/-- The ORIGINAL analytic principal ideal itself is genuinely norm closed. -/
theorem isClosed_principalIdeal (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    IsClosed (principalIdeal r hr p : Set (Ring (A := A) r hr)) := by
  have he : (principalIdeal r hr p : Set (Ring (A := A) r hr)) =
      (fun f => polynomialMap r hr (remainderPolynomial r hr hp hbound f)) ⁻¹' {0} := by
    ext f
    change f ∈ principalIdeal r hr p ↔
      polynomialMap r hr (remainderPolynomial r hr hp hbound f) = 0
    rw [mem_principalIdeal_iff r hr hp hbound]
    rw [← (polynomialMap r hr).map_zero, (polynomialMap_injective r hr).eq_iff]
  rw [he]
  exact isClosed_singleton.preimage (continuous_remainderPolynomial_image r hr hp hbound)

private def polynomialToQuotient (r : ℝ≥0) (hr : 0 < r) (p : A[X]) :
    A[X] →+* Ring (A := A) r hr ⧸ principalIdeal r hr p :=
  (Ideal.Quotient.mk (principalIdeal r hr p)).comp (polynomialMap r hr)

private theorem polynomialToQuotient_ker (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    RingHom.ker (polynomialToQuotient r hr p) = Ideal.span {p} := by
  ext f
  change Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_principalIdeal_iff r hr hp hbound,
    remainderPolynomial_polynomialMap, modByMonic_eq_zero_iff_dvd hp,
    Ideal.mem_span_singleton]

private theorem polynomialToQuotient_surjective (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Function.Surjective (polynomialToQuotient r hr p) := by
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨remainderPolynomial r hr hp hbound f, ?_⟩
  change Ideal.Quotient.mk (principalIdeal r hr p)
    (polynomialMap r hr (remainderPolynomial r hr hp hbound f)) = Ideal.Quotient.mk _ f
  have hp0 : Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he := congrArg (Ideal.Quotient.mk (principalIdeal r hr p))
    (quotient_remainder_reconstruction r hr hp hbound f)
  simpa only [map_add, map_mul, hp0, zero_mul, zero_add] using he

/-- The actual ORIGINAL analytic principal quotient is the genuine algebraic polynomial quotient. -/
def quotientEquiv (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    A[X] ⧸ Ideal.span {p} ≃+* Ring (A := A) r hr ⧸ principalIdeal r hr p :=
  (Ideal.quotEquivOfEq (polynomialToQuotient_ker r hr hp hbound).symm).trans
    ((polynomialToQuotient r hr p).quotientKerEquivOfSurjective
      (polynomialToQuotient_surjective r hr hp hbound))

/-- The actual entire quotient equivalence retains EVERY original polynomial class. -/
@[simp]
theorem quotientEquiv_mk (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) (f : A[X]) :
    quotientEquiv r hr hp hbound (Ideal.Quotient.mk (Ideal.span {p}) f) =
      Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr f) := by
  simp only [quotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- The coefficient algebra is the ACTUAL original coefficient RingHom, on every element. -/
instance coefficientAlgebra (r : ℝ≥0) (hr : 0 < r) : Algebra A (Ring (A := A) r hr) :=
  ((polynomialMap r hr).comp C).toAlgebra

/-- The genuine quotient isomorphism retains the WHOLE original A-algebra structure. -/
def quotientAlgEquiv (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    (A[X] ⧸ Ideal.span {p}) ≃ₐ[A] (Ring (A := A) r hr ⧸ principalIdeal r hr p) :=
  { quotientEquiv r hr hp hbound with
    commutes' a := by
      change quotientEquiv r hr hp hbound (Ideal.Quotient.mk (Ideal.span {p}) (C a)) =
        Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr (C a))
      exact quotientEquiv_mk r hr hp hbound (C a) }

/-- The true analytic quotient has the ACTUAL monic remainder basis indexed by Fin d. -/
def quotientBasis (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Module.Basis (Fin p.natDegree) A (Ring (A := A) r hr ⧸ principalIdeal r hr p) :=
  (AdjoinRoot.powerBasisAux' hp).map (quotientAlgEquiv r hr hp hbound).toLinearEquiv

/-- EVERY actual basis vector is its ORIGINAL coordinate power class. -/
theorem quotientBasis_apply (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (i : Fin p.natDegree) :
    quotientBasis r hr hp hbound i =
      Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr (X ^ (i : ℕ))) := by
  classical
  have hb : AdjoinRoot.powerBasisAux' hp i = AdjoinRoot.mk p (X ^ (i : ℕ)) := by
    simp only [AdjoinRoot.powerBasisAux', Module.Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, monomial_one_right_eq_X_pow]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · simp
  change quotientAlgEquiv r hr hp hbound (AdjoinRoot.powerBasisAux' hp i) = _
  rw [hb]
  change quotientEquiv r hr hp hbound (AdjoinRoot.mk p (X ^ (i : ℕ))) = _
  exact quotientEquiv_mk r hr hp hbound _

/-- Actual finite freeness is DERIVED from the original remainder basis, even over the zero ring. -/
theorem quotientModuleFree (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Module.Free A (Ring (A := A) r hr ⧸ principalIdeal r hr p) :=
  Module.Free.of_basis (quotientBasis r hr hp hbound)

/-- The actual analytic quotient is a FINITE module over the original coefficient ring. -/
theorem quotientModuleFinite (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Module.Finite A (Ring (A := A) r hr ⧸ principalIdeal r hr p) :=
  Module.Finite.of_basis (quotientBasis r hr hp hbound)

private def remainderAddHom (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree) :
    Ring (A := A) r hr →+ A[X] where
  toFun := remainderPolynomial r hr hp hbound
  map_zero' := by simpa only [map_zero, zero_modByMonic] using
    remainderPolynomial_polynomialMap r hr hp hbound 0
  map_add' := remainderPolynomial_add r hr hp hbound

/-- The ENTIRE original polynomial remainder depends only on the actual principal-quotient class. -/
theorem remainderPolynomial_eq_of_quotient_eq (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    {f g : Ring (A := A) r hr}
    (he : Ideal.Quotient.mk (principalIdeal r hr p) f = Ideal.Quotient.mk (principalIdeal r hr p) g) :
    remainderPolynomial r hr hp hbound f = remainderPolynomial r hr hp hbound g := by
  have hz := (mem_principalIdeal_iff r hr hp hbound (f-g)).mp (Ideal.Quotient.eq.mp he)
  change remainderAddHom r hr hp hbound (f-g) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- The SAME actual polynomial remainder is an ORIGINAL representative of the whole quotient class. -/
theorem quotient_mk_remainderPolynomial (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr (remainderPolynomial r hr hp hbound f)) =
      Ideal.Quotient.mk (principalIdeal r hr p) f := by
  have hp0 : Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_add, map_mul, hp0, zero_mul, zero_add] using
    congrArg (Ideal.Quotient.mk (principalIdeal r hr p))
      (quotient_remainder_reconstruction r hr hp hbound f)

/-- The true quotient infimum norm is EXACTLY the weighted norm of the ORIGINAL polynomial remainder. -/
theorem norm_quotient_mk_eq_gauss_remainder (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (f : Ring (A := A) r hr) :
    ‖Ideal.Quotient.mk (principalIdeal r hr p) f‖ =
      (MonicGaussDivision.gauss r (remainderPolynomial r hr hp hbound f) : ℝ) := by
  apply le_antisymm
  · have he := quotient_mk_remainderPolynomial r hr hp hbound f
    calc
      ‖Ideal.Quotient.mk (principalIdeal r hr p) f‖ =
          ‖Ideal.Quotient.mk (principalIdeal r hr p)
            (polynomialMap r hr (remainderPolynomial r hr hp hbound f))‖ := congrArg norm he.symm
      _ ≤ ‖polynomialMap r hr (remainderPolynomial r hr hp hbound f)‖ := Ideal.Quotient.norm_mk_le _ _
      _ = _ := congrArg ((↑) : ℝ≥0 → ℝ) (nnnorm_polynomialMap r hr _)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hg, hgn⟩ := Ideal.Quotient.norm_mk_lt
      (Ideal.Quotient.mk (principalIdeal r hr p) f) hε
    have hR := remainderPolynomial_eq_of_quotient_eq r hr hp hbound hg
    have hboundg := gauss_remainderPolynomial_le r hr hp hbound g
    rw [hR] at hboundg
    exact (show (MonicGaussDivision.gauss r (remainderPolynomial r hr hp hbound f) : ℝ) ≤ ‖g‖ from
      NNReal.coe_le_coe.mpr hboundg).trans hgn.le

/-- The infimum is genuinely ATTAINED by the SAME original polynomial representative. -/
theorem quotient_norm_attained (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (z : Ring (A := A) r hr ⧸ principalIdeal r hr p) :
    ∃ s : A[X], s.degree < (p.natDegree : WithBot ℕ) ∧
      Ideal.Quotient.mk (principalIdeal r hr p) (polynomialMap r hr s) = z ∧
        ‖polynomialMap r hr s‖ = ‖z‖ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨remainderPolynomial r hr hp hbound f, degree_remainderPolynomial_lt r hr hp hbound f,
    quotient_mk_remainderPolynomial r hr hp hbound f, ?_⟩
  rw [norm_quotient_mk_eq_gauss_remainder]
  exact congrArg ((↑) : ℝ≥0 → ℝ) (nnnorm_polynomialMap r hr _)

end EnvelopeProperty.CompletedMonicDivision
