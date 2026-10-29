import EnvelopeProperty.Berkovich.SpectrumLaurentGauss
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Genuine finite Laurent expansions of the entire original tensor module -/
open scoped Classical LaurentPolynomial TensorProduct NNReal
noncomputable section
namespace EnvelopeProperty.LaurentModuleExpansion
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual monomial basis of the ORIGINAL Laurent algebra gives the
whole finite-coefficient equivalence; M need not be finite or free. -/
def coefficients : R[T;T⁻¹] ⊗[R] M ≃ₗ[R] ℤ →₀ M :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis ℤ R)

/-- EVERY original pure tensor retains its actual original coefficient. -/
theorem coefficients_tmul (F : R[T;T⁻¹]) (m : M) (i : ℤ) :
    coefficients (F ⊗ₜ[R] m) i = F.coeff i • m := by
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

@[simp] theorem coefficients_T_tmul (i : ℤ) (m : M) :
    coefficients ((LaurentPolynomial.T i : R[T;T⁻¹]) ⊗ₜ[R] m) = Finsupp.single i m := by
  ext j
  rw [coefficients_tmul]
  simp only [LaurentPolynomial.T_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- The inverse equivalence is the genuine finite sum of ORIGINAL monomials. -/
theorem coefficients_symm (c : ℤ →₀ M) :
    coefficients.symm c = c.sum (fun i m => (LaurentPolynomial.T i : R[T;T⁻¹]) ⊗ₜ[R] m) :=
  TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ _

/-- EVERY original tensor has its actual finite Laurent module expansion. -/
theorem eq_sum_T_tmul (z : R[T;T⁻¹] ⊗[R] M) :
    z = (coefficients z).sum
      (fun i m => (LaurentPolynomial.T i : R[T;T⁻¹]) ⊗ₜ[R] m) := by
  rw [← coefficients_symm, LinearEquiv.symm_apply_apply]

variable {S : Type*} [CommRing S] [Module R S]

/-- The actual entire evaluation map applies the original linear functional
to EVERY original finite module coefficient. -/
def evaluate (φ : M →ₗ[R] S) : R[T;T⁻¹] ⊗[R] M →ₗ[R] S[T;T⁻¹] :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ coefficients.toLinearMap

@[simp] theorem evaluate_coeff (φ : M →ₗ[R] S) (z : R[T;T⁻¹] ⊗[R] M) (i : ℤ) :
    (evaluate φ z).coeff i = φ (coefficients z i) := rfl

@[simp] theorem evaluate_T_tmul (φ : M →ₗ[R] S) (i : ℤ) (m : M) :
    evaluate φ ((LaurentPolynomial.T i : R[T;T⁻¹]) ⊗ₜ[R] m) =
      LaurentPolynomial.C (φ m) * LaurentPolynomial.T i := by
  apply LaurentPolynomial.ext
  intro j
  rw [evaluate_coeff, coefficients_T_tmul]
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> simp_all

/-- The actual Gauss maximum is over the ORIGINAL module coefficient support,
even when some original coefficients vanish under the actual evaluation. -/
theorem laurentGauss_evaluate (φ : M →ₗ[R] S) (w : Valuation S ℝ≥0)
    (r : ℝ≥0) (hr : 0 < r) (z : R[T;T⁻¹] ⊗[R] M) :
    (Berkovich.Spectrum.laurentGauss w r hr).val (evaluate φ z) =
      (coefficients z).support.sup (fun i => w (φ (coefficients z i)) * r ^ i) := by
  apply le_antisymm
  · rw [Berkovich.Spectrum.laurentGauss_val_eq_sup]
    apply Finset.sup_le
    intro i hi
    have hc : i ∈ (coefficients z).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      have he : (evaluate φ z).coeff i = 0 := by rw [evaluate_coeff, hz, map_zero]
      exact Finsupp.mem_support_iff.mp hi he
    rw [evaluate_coeff]
    exact Finset.le_sup (f := fun j : ℤ => w (φ (coefficients z j)) * r ^ j) hc
  · apply Finset.sup_le
    intro i _
    simpa only [evaluate_coeff] using
      Berkovich.Spectrum.le_laurentGauss_val w r hr (evaluate φ z) i

/-- ONE actual finite coefficient-pair family is chosen BEFORE any evaluation. -/
def terms (G : Finset (R[T;T⁻¹] ⊗[R] M)) : Finset (M × ℤ) :=
  G.biUnion fun z => (coefficients z).support.image fun i => (coefficients z i, i)

/-- The WHOLE original finite family has the genuine finite weighted maximum
of its actual original module coefficients; all integer weights are retained. -/
theorem laurentGauss_finite_family (G : Finset (R[T;T⁻¹] ⊗[R] M))
    (φ : M →ₗ[R] S) (w : Valuation S ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    G.sup (fun z => (Berkovich.Spectrum.laurentGauss w r hr).val (evaluate φ z)) =
      (terms G).sup (fun t => w (φ t.1) * r ^ t.2) := by
  simp only [laurentGauss_evaluate, terms, Finset.sup_biUnion, Finset.sup_image]
  rfl

end EnvelopeProperty.LaurentModuleExpansion
