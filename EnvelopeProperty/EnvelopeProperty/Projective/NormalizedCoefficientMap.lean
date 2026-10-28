import EnvelopeProperty.Berkovich.SpectrumPolynomialGauss

/-! # Actual coefficient pullback of whole normalized projective points -/
open scoped Polynomial NNReal Topology
noncomputable section
namespace EnvelopeProperty.Berkovich
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Actual coefficient maps commute with every original homogeneous component. -/
theorem map_homogeneousComponent (φ : R →+* S)
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    MvPolynomial.map φ (MvPolynomial.homogeneousComponent d F) =
      MvPolynomial.homogeneousComponent d (MvPolynomial.map φ F) := by
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp

namespace Spectrum
/-- The actual Gauss coefficient interchange retains EVERY original base form. -/
theorem polynomialGauss_val_map_C (x : Spectrum (MvPolynomial (Fin (n + 1)) R))
    (r : ℝ≥0) (F : MvPolynomial (Fin (n + 1)) R) :
    (polynomialGauss x r).val (MvPolynomial.map Polynomial.C F) = x.val F := by
  have he : polynomialCoefficientSwap R (Fin (n + 1)) (MvPolynomial.map Polynomial.C F) =
      Polynomial.C F := by
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF => simp only [map_mul, MvPolynomial.map_X, hF, polynomialCoefficientSwap_X]
  change (gauss x r).val (polynomialCoefficientSwap R (Fin (n + 1))
    (MvPolynomial.map Polynomial.C F)) = _
  rw [he, gauss_val_C]
end Spectrum

namespace NormalizedProjectiveSpectrum
/-- The genuine whole coefficient pullback retains grading and normalization. -/
def coefficientComap (φ : R →+* S) (x : NormalizedProjectiveSpectrum S n) :
    NormalizedProjectiveSpectrum R n :=
  ⟨Spectrum.comap (MvPolynomial.map φ) x.1,
    (Spectrum.isPolynomialGraded_iff _).mpr (fun F d => by
      change x.1.val (MvPolynomial.map φ (MvPolynomial.homogeneousComponent d F)) ≤ _
      rw [map_homogeneousComponent]
      exact (Spectrum.isPolynomialGraded_iff _).mp x.2.1 _ d),
    by simpa only [Spectrum.comap_val_apply, MvPolynomial.map_X] using x.2.2⟩

/-- EVERY whole original polynomial has its actual pulled-back value. -/
theorem coefficientComap_val (φ : R →+* S) (x : NormalizedProjectiveSpectrum S n)
    (F : MvPolynomial (Fin (n + 1)) R) :
    (coefficientComap φ x).1.val F = x.1.val (MvPolynomial.map φ F) := rfl

/-- Whole coefficient pullback is continuous on the actual normalized spectra. -/
@[fun_prop] theorem continuous_coefficientComap (φ : R →+* S) :
    Continuous (coefficientComap (n := n) φ) :=
  (Spectrum.continuous_comap (MvPolynomial.map φ)).comp
    continuous_subtype_val |>.subtype_mk fun x => (coefficientComap φ x).2
end NormalizedProjectiveSpectrum

namespace RelativeNormalizedProjectiveSpectrum
/-- Restricting a genuine polynomial-Gauss-base point to the original base
forms produces an actual original normalized projective point. The input
need NOT itself be a Gauss extension of this point. -/
def polynomialRestriction (v : Valuation R ℝ≥0) (r : ℝ≥0)
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n) :
    RelativeNormalizedProjectiveSpectrum v n :=
  ⟨NormalizedProjectiveSpectrum.coefficientComap Polynomial.C x.1, by
    intro a
    change x.1.1.val (MvPolynomial.map Polynomial.C (MvPolynomial.C a)) = v a
    rw [MvPolynomial.map_C, x.2]
    exact Spectrum.gauss_val_C (Spectrum.ofValuation v) r a⟩

/-- EVERY original base form is retained by the genuine polynomial restriction. -/
theorem polynomialRestriction_val (v : Valuation R ℝ≥0) (r : ℝ≥0)
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n)
    (F : MvPolynomial (Fin (n + 1)) R) :
    (polynomialRestriction v r x).1.1.val F =
      x.1.1.val (MvPolynomial.map Polynomial.C F) := rfl

/-- Original whole relative points are recovered after actual Gauss extension
and coefficient restriction, with no condition on the radius. -/
theorem polynomialRestriction_polynomialGauss (v : Valuation R ℝ≥0) (r : ℝ≥0)
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    polynomialRestriction v r (polynomialGauss v x r) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro F
  exact Spectrum.polynomialGauss_val_map_C x.1.1 r F

/-- Restricting arbitrary genuine Gauss-base points to their original forms
is continuous on the WHOLE actual relative normalized projective spectrum. -/
@[fun_prop] theorem continuous_polynomialRestriction (v : Valuation R ℝ≥0) (r : ℝ≥0) :
    Continuous (polynomialRestriction (n := n) v r) :=
  ((NormalizedProjectiveSpectrum.continuous_coefficientComap Polynomial.C).comp
    continuous_subtype_val).subtype_mk fun x => (polynomialRestriction v r x).2
end RelativeNormalizedProjectiveSpectrum
end EnvelopeProperty.Berkovich
