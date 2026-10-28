import EnvelopeProperty.Cartier.PolynomialCartierProjection
import EnvelopeProperty.Cartier.Polynomial
import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Coefficient-preserving extraction for genuine relative polynomial Cartier

The coefficients at exponents `p • d + a` are retained as original coefficients.
The actual polynomial de Rham residual is coefficient-preserving exponent expansion
of these extracted polynomials times the prescribed Cartier monomial. No perfection,
coefficient root, or Cartier-image certificate is used.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCoefficients
open scoped Classical TensorProduct
open MvPolynomial PolynomialDeRham PolynomialResidualCoefficients
variable (k : Type*) [Field k] {σ : Type*}
variable (p : ℕ) [hp : Fact p.Prime]

/-- Extract every original coefficient on the specified affine exponent lattice. -/
def coefficientPoly (a : σ →₀ ℕ) : MvPolynomial σ k →+ MvPolynomial σ k :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.comapDomain.addMonoidHom (smul_add_injective hp.out.ne_zero a)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

/-- The SAME original coefficient is retained, with no coefficient automorphism. -/
theorem coeff_coefficientPoly (a : σ →₀ ℕ) (f : MvPolynomial σ k) (d : σ →₀ ℕ) :
    coeff d (coefficientPoly k p a f) = coeff (p • d + a) f := rfl

/-- On every matching monomial, only the exponent is compressed. -/
theorem coefficientPoly_monomial (a d : σ →₀ ℕ) (b : k) :
    coefficientPoly k p a (monomial (p • d + a) b) = monomial d b := by
  ext e
  rw [coeff_coefficientPoly, coeff_monomial, coeff_monomial]
  by_cases h : d = e
  · subst h
    simp only [if_true]
  · rw [if_neg ((smul_add_injective hp.out.ne_zero a).ne h), if_neg h]

/-- Every monomial outside the actual chosen exponent lattice has zero extractor. -/
theorem coefficientPoly_monomial_of_ne (a d : σ →₀ ℕ) (b : k)
    (h : ∀ e : σ →₀ ℕ, p • e + a ≠ d) :
    coefficientPoly k p a (monomial d b) = 0 := by
  ext e
  rw [coeff_coefficientPoly, coeff_monomial, if_neg (h e).symm, coeff_zero]

/-- Extraction is a genuine left inverse to coefficient-preserving expansion followed
by the SAME prescribed monomial, on the entire original polynomial ring. -/
theorem coefficientPoly_expand_mul (a : σ →₀ ℕ) (f : MvPolynomial σ k) :
    coefficientPoly k p a (expand p f * monomial a 1) = f := by
  induction f using MvPolynomial.induction_on' with
  | monomial d b =>
    rw [expand_monomial, monomial_mul, mul_one, coefficientPoly_monomial]
  | add f g hf hg =>
    rw [map_add, add_mul, map_add, hf, hg]

variable [LinearOrder σ] [Fintype σ]

/-- The actual Cartier exponent digit for the original wedge, with original coefficient 1. -/
def residueDigit (q : ℕ) (s : Set.powersetCard σ q) : Box σ p :=
  fun i => if i ∈ s then ⟨p-1, Nat.sub_lt hp.out.pos (by decide)⟩ else 0

omit [LinearOrder σ] [Fintype σ] in
/-- The original exponent is p-1 exactly at the original wedge factors. -/
theorem residueDigit_apply (q : ℕ) (s : Set.powersetCard σ q) (i : σ) :
    ((residueDigit (σ := σ) p q s i : Fin p) : ℕ) = if i ∈ s then p-1 else 0 := by
  unfold residueDigit
  split_ifs <;> rfl

omit [LinearOrder σ] in
private theorem residue_condition (q : ℕ) (s : Set.powersetCard σ q)
    (a : Box σ p) (d : σ →₀ ℕ) :
    (∀ i, p ∣ (p • d + a.toFinsupp) i + if i ∈ s then 1 else 0) ↔
      a = residueDigit p q s := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have ha := (a i).isLt
    have hd : p ∣ (a i : ℕ) + if i ∈ s then 1 else 0 := by
      have hi := h i
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Box.toFinsupp_apply, add_assoc] at hi
      exact (Nat.dvd_add_right (dvd_mul_right p (d i))).mp hi
    rw [residueDigit_apply]
    by_cases hi : i ∈ s
    · rw [if_pos hi] at hd ⊢
      have he : (a i : ℕ) + 1 = p :=
        Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)
      omega
    · rw [if_neg hi, add_zero] at hd
      rw [if_neg hi]
      exact Nat.eq_zero_of_dvd_of_lt hd ha
  · rintro rfl i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Box.toFinsupp_apply, residueDigit_apply]
    by_cases hi : i ∈ s
    · rw [if_pos hi, if_pos hi, add_assoc, Nat.sub_add_cancel hp.out.one_le]
      exact dvd_add (dvd_mul_right p (d i)) (dvd_refl p)
    · rw [if_neg hi, if_neg hi, add_zero, add_zero]
      exact dvd_mul_right p (d i)

omit [LinearOrder σ] in
/-- The WHOLE actual scalar residual has its original coefficient-preserving expression. -/
theorem scalarResidualList_eq_expand (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    scalarResidualList k p q s Finset.univ.toList f =
      expand p (coefficientPoly k p (residueDigit p q s).toFinsupp f) *
        monomial (residueDigit p q s).toFinsupp 1 := by
  induction f using MvPolynomial.induction_on' with
  | monomial d b =>
    obtain ⟨c, a, rfl⟩ := exists_box_smul_add p d
    rw [scalarResidualList_monomial]
    simp only [Finset.mem_toList, Finset.mem_univ, forall_const, residue_condition]
    by_cases ha : a = residueDigit p q s
    · subst a
      rw [if_pos rfl, coefficientPoly_monomial, expand_monomial, monomial_mul, mul_one]
    · rw [if_neg ha, coefficientPoly_monomial_of_ne, map_zero, zero_mul]
      intro c' hc
      exact ha (box_eq_of_smul_add_eq p hc).symm
  | add f g hf hg =>
    rw [map_add, map_add, map_add, add_mul, hf, hg]

/-- Every original tensor-basis coefficient of the WHOLE full residual is recovered
without any coefficient roots, over imperfect fields as well. -/
theorem allResidual_basis_eq_expand (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    allResidual k p q (f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
      (expand p (coefficientPoly k p (residueDigit p q s).toFinsupp f) *
        monomial (residueDigit p q s).toFinsupp 1) ⊗ₜ[k]
          (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s := by
  rw [allResidual, residualList_basis, scalarResidualList_eq_expand]

/-- The SAME actual original exterior cotangent residual retains these unchanged coefficients. -/
theorem originalAllResidual_smul_basis (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    PolynomialCartierProjection.originalAllResidual k p q
      (f • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
      (expand p (coefficientPoly k p (residueDigit p q s).toFinsupp f) *
        monomial (residueDigit p q s).toFinsupp 1) •
          (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s := by
  rw [← formEquiv_tmul_basis, PolynomialCartierProjection.originalAllResidual_formEquiv,
    allResidual_basis_eq_expand, formEquiv_tmul_basis]

end EnvelopeProperty.Cartier.RelativePolynomialCoefficients
