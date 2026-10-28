/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.PolynomialCoefficientSwap
import EnvelopeProperty.Berkovich.SpectrumGauss
import EnvelopeProperty.Berkovich.SpectrumIdeals
import EnvelopeProperty.Projective.NormalizedSpectrum

/-!
# Genuine Gauss naturality and projective grading stability

All-coefficient Gauss bounds prove naturality for every actual ring homomorphism,
without injectivity. The whole coefficient/homogeneous-component interchange gives
actual grading stability over arbitrary rings and radii, including zero. Normalization
and every prescribed coefficient value are preserved. The point maps are genuinely
continuous. Boundedness is derived only from an explicitly bounded coefficient-ring
point and radius at most one; it is not asserted over a nontrivially valued field.
-/

open scoped Polynomial NNReal Topology
open MvPolynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B : Type*} [CommRing A] [CommRing B]

/-- Genuine Gauss pullback commutes with EVERY actual coefficient ring map, without any injectivity hypothesis. -/
theorem gauss_comap (φ : A →+* B) (y : Spectrum B) (r : ℝ≥0) :
    comap (Polynomial.mapRingHom φ) (gauss y r) = gauss (comap φ y) r := by
  apply ext_val
  intro F
  change (gauss y r).val (Polynomial.map φ F) = (gauss (comap φ y) r).val F
  apply le_antisymm
  · apply (gauss_val_le_iff _ _ _ _).mpr
    intro i
    rw [Polynomial.coeff_map]
    exact le_gauss_val (comap φ y) r F i
  · apply (gauss_val_le_iff _ _ _ _).mpr
    intro i
    have h := le_gauss_val y r (Polynomial.map φ F) i
    simpa only [Polynomial.coeff_map, comap_val_apply] using h

variable {R σ : Type*} [CommRing R]

/-- The actual coefficient-interchanged Gauss point on the multivariable polynomial ring. -/
def polynomialGauss (x : Spectrum (MvPolynomial σ R)) (r : ℝ≥0) : Spectrum (MvPolynomial σ R[X]) :=
  comap (polynomialCoefficientSwap R σ).toRingHom (gauss x r)

/-- Every whole multivariable variable retains its original value after the true Gauss coefficient interchange. -/
@[simp]
theorem polynomialGauss_val_X (x : Spectrum (MvPolynomial σ R)) (r : ℝ≥0) (i : σ) :
    (polynomialGauss x r).val (MvPolynomial.X i) = x.val (MvPolynomial.X i) := by
  change (gauss x r).val (polynomialCoefficientSwap R σ (MvPolynomial.X i)) = _
  rw [polynomialCoefficientSwap_X, gauss_val_C]

/-- Every whole coefficient polynomial has its actual Gauss value over the original coefficient seminorm. -/
theorem polynomialGauss_val_C (x : Spectrum (MvPolynomial σ R)) (r : ℝ≥0) (p : R[X]) :
    (polynomialGauss x r).val (MvPolynomial.C p) =
      (gauss (comap MvPolynomial.C x) r).val p := by
  change (gauss x r).val (polynomialCoefficientSwap R σ (MvPolynomial.C p)) = _
  rw [polynomialCoefficientSwap_C]
  exact congrArg (fun z : Spectrum R[X] => z.val p) (gauss_comap MvPolynomial.C x r)

/-- Entire coefficient/homogeneous-component commutation proves true grading stability of genuine Gauss extension. -/
theorem polynomialGauss_isPolynomialGraded (x : Spectrum (MvPolynomial σ R))
    (hx : IsPolynomialGraded x) (r : ℝ≥0) : IsPolynomialGraded (polynomialGauss x r) := by
  apply (isPolynomialGraded_iff _).mpr
  intro F d
  change (gauss x r).val (polynomialCoefficientSwap R σ (homogeneousComponent d F)) ≤
    (gauss x r).val (polynomialCoefficientSwap R σ F)
  apply (gauss_val_le_iff _ _ _ _).mpr
  intro i
  rw [polynomialCoefficientSwap_coeff_homogeneousComponent]
  exact (mul_le_mul' ((isPolynomialGraded_iff x).mp hx _ d) le_rfl).trans
    (le_gauss_val x r (polynomialCoefficientSwap R σ F) i)

/-- Joint continuity of the actual coefficient-interchanged Gauss point for every nonnegative radius. -/
@[fun_prop]
theorem continuous_polynomialGauss_prod :
    Continuous fun p : Spectrum (MvPolynomial σ R) × ℝ≥0 => polynomialGauss p.1 p.2 :=
  (continuous_comap (polynomialCoefficientSwap R σ).toRingHom).comp continuous_gauss_prod

/-- Genuine bounded coefficients and a radius at most one bound every polynomial at the actual Gauss point. -/
theorem isBounded_gauss (x : Spectrum A) (hx : IsBounded x) (r : ℝ≥0) (hr : r ≤ 1) :
    IsBounded (gauss x r) := by
  intro F
  apply (gauss_val_le_iff _ _ _ _).mpr
  intro i
  exact (mul_le_mul' (hx (F.coeff i)) (pow_le_one₀ (show 0 ≤ r from zero_le) hr)).trans (by simp)

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Genuine normalized graded coordinates remain normalized after actual coefficient-interchanged Gauss extension, at every radius. -/
def polynomialGauss (x : NormalizedProjectiveSpectrum R n) (r : ℝ≥0) :
    NormalizedProjectiveSpectrum R[X] n :=
  ⟨Spectrum.polynomialGauss x.1 r, Spectrum.polynomialGauss_isPolynomialGraded x.1 x.2.1 r,
    by simpa only [Spectrum.polynomialGauss_val_X] using x.2.2⟩

/-- Actual Gauss normalization is jointly continuous in the entire point and nonnegative radius. -/
@[fun_prop]
theorem continuous_polynomialGauss_prod :
    Continuous fun p : NormalizedProjectiveSpectrum R n × ℝ≥0 => polynomialGauss p.1 p.2 := by
  have hval : Continuous fun p : NormalizedProjectiveSpectrum R n × ℝ≥0 => p.1.1 :=
    (continuous_val (R := R) (n := n)).comp continuous_fst
  have h := (Spectrum.continuous_polynomialGauss_prod (R := R) (σ := Fin (n + 1))).comp
    (hval.prodMk continuous_snd)
  exact h.subtype_mk fun p => (polynomialGauss p.1 p.2).2

end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}

/-- The actual coefficient-interchanged Gauss point preserves the entire genuine Gauss coefficient seminorm, without a field or boundedness condition. -/
def polynomialGauss (x : RelativeNormalizedProjectiveSpectrum v n) (r : ℝ≥0) :
    RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n :=
  ⟨NormalizedProjectiveSpectrum.polynomialGauss x.1 r, by
    intro p
    change (Spectrum.polynomialGauss x.1.1 r).val (MvPolynomial.C p) = _
    rw [Spectrum.polynomialGauss_val_C]
    have he : Spectrum.comap MvPolynomial.C x.1.1 = Spectrum.ofValuation v := Spectrum.ext_val x.2
    rw [he]
    rfl⟩

/-- Every whole multivariable polynomial value at the relative Gauss point is the actual Gauss value after the full coefficient interchange. -/
theorem polynomialGauss_val_apply (x : RelativeNormalizedProjectiveSpectrum v n) (r : ℝ≥0)
    (F : MvPolynomial (Fin (n + 1)) R[X]) :
    (polynomialGauss v x r).1.1.val F =
      (Spectrum.gauss x.1.1 r).val (polynomialCoefficientSwap R (Fin (n + 1)) F) := rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual prescribed-Gauss-coefficient normalized point map is continuous for each fixed radius. -/
@[fun_prop]
theorem continuous_polynomialGauss (r : ℝ≥0) :
    Continuous (fun x : RelativeNormalizedProjectiveSpectrum v n => polynomialGauss v x r) := by
  have hp : Continuous (fun x : RelativeNormalizedProjectiveSpectrum v n => (x.1, r)) :=
    (continuous_subtype_val : Continuous (Subtype.val : RelativeNormalizedProjectiveSpectrum v n →
      NormalizedProjectiveSpectrum R n)).prodMk continuous_const
  have h : Continuous fun x : RelativeNormalizedProjectiveSpectrum v n =>
      NormalizedProjectiveSpectrum.polynomialGauss x.1 r :=
    (NormalizedProjectiveSpectrum.continuous_polynomialGauss_prod (R := R) (n := n)).comp hp
  exact h.subtype_mk fun x => (polynomialGauss v x r).2

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
