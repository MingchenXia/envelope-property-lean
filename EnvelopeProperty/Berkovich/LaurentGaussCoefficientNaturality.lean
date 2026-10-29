import EnvelopeProperty.Berkovich.SpectrumLaurentGauss
import EnvelopeProperty.Projective.NativeMultiplicativeGroup

/-! # Genuine Laurent Gauss naturality for the entire original coefficient map -/
open scoped Polynomial LaurentPolynomial NNReal
open Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The true original Laurent coefficient map retains the entire parameter unit. -/
def laurentCoefficientHom (φ : A →+* B) : A[T;T⁻¹] →+* B[T;T⁻¹] :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp φ) (parameterLaurentUnit B)

@[simp]
theorem laurentCoefficientHom_C (φ : A →+* B) (a : A) :
    laurentCoefficientHom φ (LaurentPolynomial.C a) = LaurentPolynomial.C (φ a) := by
  simp [laurentCoefficientHom]

@[simp]
theorem laurentCoefficientHom_T (φ : A →+* B) (n : ℤ) :
    laurentCoefficientHom φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  simp [laurentCoefficientHom, ProjBerk.parameterLaurentUnit_zpow]

/-- The entire polynomial coefficient square commutes with actual Laurent localization. -/
theorem laurentCoefficientHom_toLaurent (φ : A →+* B) (p : A[X]) :
    laurentCoefficientHom φ (Polynomial.toLaurent p) = Polynomial.toLaurent (p.map φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a => simp

/-- Actual coefficient compatibility derives whole Laurent Gauss naturality,
not only matching on polynomials or on the chosen parameter. -/
theorem laurentGauss_comap_coefficients (φ : A →+* B)
    (v : Valuation A ℝ≥0) (w : Valuation B ℝ≥0)
    (hφ : ∀ a, w (φ a) = v a) (r : ℝ≥0) (hr : 0 < r) :
    Spectrum.comap (laurentCoefficientHom φ) (laurentGauss w r hr) =
      laurentGauss v r hr := by
  apply Away.comap_injective A[T;T⁻¹] (Polynomial.X : A[X])
  apply Spectrum.ext_val
  intro p
  change (laurentGauss w r hr).val
    (laurentCoefficientHom φ (Polynomial.toLaurent p)) =
      (laurentGauss v r hr).val (Polynomial.toLaurent p)
  rw [laurentCoefficientHom_toLaurent, laurentGauss_val_toLaurent,
    laurentGauss_val_toLaurent]
  have he : Spectrum.comap φ (Spectrum.ofValuation w) = Spectrum.ofValuation v :=
    Spectrum.ext_val hφ
  have hg := congrArg (fun z : Spectrum A[X] => z.val p)
    (Spectrum.gauss_comap φ (Spectrum.ofValuation w) r)
  rw [he] at hg
  exact hg

/-- Every original Laurent expansion retains its actual original coefficient
maximum, even if some original coefficients vanish after scalar evaluation. -/
theorem laurentGauss_coefficients_eq_sup (φ : A →+* B)
    (v : Valuation A ℝ≥0) (w : Valuation B ℝ≥0)
    (hφ : ∀ a, w (φ a) = v a) (r : ℝ≥0) (hr : 0 < r) (f : A[T;T⁻¹]) :
    (laurentGauss w r hr).val (laurentCoefficientHom φ f) =
      f.coeff.support.sup (fun i => v (f.coeff i) * r ^ i) := by
  have he := congrArg (fun z : Spectrum A[T;T⁻¹] => z.val f)
    (laurentGauss_comap_coefficients φ v w hφ r hr)
  exact he.trans (laurentGauss_val_eq_sup v r hr f)

end EnvelopeProperty.Berkovich.Spectrum
