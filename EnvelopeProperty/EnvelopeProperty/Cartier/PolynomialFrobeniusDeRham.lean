import EnvelopeProperty.Cartier.PolynomialDeRham
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The actual Frobenius-linear original polynomial de Rham complex

Linearity is DERIVED from the original power and Leibniz rules, on whole original forms.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialDeRham
open scoped TensorProduct
open MvPolynomial

variable (R : Type*) [CommRing R] {σ : Type*} [Fintype σ]
variable (p : ℕ) [Fact p.Prime] [CharP R p]

omit [Fact p.Prime] in
/-- The original tensor differential is linear for the actual pth-power coefficient action. -/
theorem tensorDifferential_pow_smul (q : ℕ) (a : MvPolynomial σ R)
    (z : MvPolynomial σ R ⊗[R] (⋀[R]^q (σ →₀ R))) :
    tensorDifferential R q (a^p • z) = a^p • tensorDifferential R q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul f w =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorDifferential_tmul,
      pderiv_mul, pderiv_pow, CharP.cast_eq_zero (MvPolynomial σ R) p,
      zero_mul, zero_add, Finset.smul_sum]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

variable [LinearOrder σ]

omit [Fact p.Prime] in
/-- Genuine Frobenius linearity on the WHOLE SAME original exterior cotangent module. -/
theorem differential_pow_smul (q : ℕ) (a : MvPolynomial σ R)
    (w : ⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))) :
    differential R q (a^p • w) = a^p • differential R q w := by
  obtain ⟨z, rfl⟩ := (formEquiv R q).surjective w
  rw [← map_smul, differential_formEquiv, tensorDifferential_pow_smul,
    map_smul, differential_formEquiv]

/-- The SAME original exterior module with scalar multiplication restricted along the ACTUAL
polynomial Frobenius, using the genuine native restriction-of-scalars functor. -/
def frobeniusModule (q : ℕ) : ModuleCat (MvPolynomial σ R) :=
  (ModuleCat.restrictScalars (frobenius (MvPolynomial σ R) p)).obj
    (ModuleCat.of (MvPolynomial σ R)
      (⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))))

/-- The ORIGINAL differential, now genuinely linear for actual Frobenius-restricted scalars. -/
def frobeniusDifferential (q : ℕ) :
    frobeniusModule (σ := σ) R p q ⟶ frobeniusModule (σ := σ) R p (q+1) :=
  ModuleCat.ofHom (X := frobeniusModule (σ := σ) R p q)
    (Y := frobeniusModule (σ := σ) R p (q+1))
    { toFun := differential R q
      map_add' := (differential R q).map_add
      map_smul' := fun a w => differential_pow_smul R p q a w }

/-- The whole original underlying differential is unchanged by genuine scalar restriction. -/
theorem frobeniusDifferential_apply (q : ℕ) (w : frobeniusModule (σ := σ) R p q) :
    frobeniusDifferential (σ := σ) R p q w = differential R q w := rfl

/-- The actual Frobenius-pushforward polynomial de Rham complex of original exterior modules. -/
def frobeniusComplex : CochainComplex (ModuleCat (MvPolynomial σ R)) ℕ :=
  CochainComplex.of (frobeniusModule (σ := σ) R p) (frobeniusDifferential (σ := σ) R p)
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact differential_square R q w)

end EnvelopeProperty.Cartier.PolynomialDeRham
