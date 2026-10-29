/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumPolynomialGauss
import EnvelopeProperty.Projective.NativeModelIdeals
import EnvelopeProperty.Projective.NativeBridge
import EnvelopeProperty.Projective.IdealBridge

/-!
# The old Gauss ideal function as a genuine native MODEL ideal logarithm

The actual whole coefficient interchange transports the old Gauss extension to the
relative normalized projective spectrum over the MODEL coefficient ring k[t], with
its precise bounded Gauss seminorm. For an actual homogeneous ideal J, the old ideal
I is its whole image under the genuine interchange. The entire original phiNorm and
phiIdeal then equal the true proper-center model norm and logarithm of J's actual
kernel ideal sheaf. Original powers are retained and zero and negative infinity conventions match.

The bound concerns k[t], not an entire nontrivially valued field. No scheme product
isomorphism with projective space times the affine line or coherent analytic sheaf
comparison is asserted before constructing those separate producers.
-/

open scoped Classical NNReal ENNReal Polynomial
open CategoryTheory AlgebraicGeometry MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {k : Type u} [Field k] {n : ℕ}

/-- The old actual Gauss extension is a genuine normalized projective point over the polynomial MODEL ring with its exact Gauss coefficient seminorm. -/
def gaussModelPoint (x : ProjBerk k n) :
    RelativeNormalizedProjectiveSpectrum (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) n :=
  RelativeNormalizedProjectiveSpectrum.polynomialGauss (1 : Valuation k ℝ≥0)
    (normalizedSpectrumHomeomorph x) gaussRadius

/-- Every original polynomial value is preserved by the true Gauss coefficient interchange. -/
theorem gaussModelPoint_val_apply (x : ProjBerk k n) (F : MvPolynomial (Fin (n + 1)) k[X]) :
    (gaussModelPoint x).1.1.val F =
      (gaussExt x).val (polynomialCoefficientSwap k (Fin (n + 1)) F) := rfl

/-- The actual original polynomial MODEL coefficients are bounded; no whole nontrivial-field bound is asserted. -/
theorem gaussModelCoefficient_le_one (p : k[X]) :
    gaussValuation (1 : Valuation k ℝ≥0) gaussRadius p ≤ 1 := by
  exact Spectrum.isBounded_gauss (Spectrum.ofValuation (1 : Valuation k ℝ≥0))
    (fun c => Valuation.one_apply_le_one c)
    gaussRadius gaussRadius_le_one p

/-- The whole new normalized MODEL point is continuous in the old projective point. -/
@[fun_prop]
theorem continuous_gaussModelPoint : Continuous (gaussModelPoint (k := k) (n := n)) :=
  (RelativeNormalizedProjectiveSpectrum.continuous_polynomialGauss (1 : Valuation k ℝ≥0) gaussRadius).comp
    normalizedSpectrumHomeomorph.continuous

private local instance gaussModelProper :
    IsProper (nativeStructureMap (R := k[X]) (n := n)) := nativeStructureMap_isProper

/-- The old whole Gauss ideal norm of the actual original homogeneous ideal image is its genuine proper-center MODEL norm. -/
theorem phiNorm_eq_nativeModelIdealNorm (J : HomogeneousIdeal (ProjectiveGrading k[X] n))
    (x : ProjBerk k n) :
    phiNorm (J.toIdeal.map (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x =
      RelativeSchemeValuedPoint.modelIdealNorm (nativeHomogeneousIdealSheaf J) gaussModelCoefficient_le_one
        (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _ (gaussModelPoint x)) := by
  rw [RelativeNormalizedProjectiveSpectrum.modelIdealNorm_quotient_eq_idealNorm]
  rw [phiNorm_eq_spectrumIdealNorm,
    Spectrum.idealNorm_map _ _ (show Spectrum.IsBounded (Berk.toSpectrum (gaussExt x)) from gaussExt_val_le_one x)]
  rfl

/-- The old actual phi_I for the original homogeneous ideal image is the genuine center-stalk logarithmic MODEL function, including negative infinity. -/
theorem phiIdeal_eq_nativeModelIdealLog (J : HomogeneousIdeal (ProjectiveGrading k[X] n))
    (x : ProjBerk k n) :
    phiIdeal (J.toIdeal.map (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x =
      RelativeSchemeValuedPoint.modelIdealLog (nativeHomogeneousIdealSheaf J) gaussModelCoefficient_le_one
        (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _ (gaussModelPoint x)) := by
  rw [phiIdeal_eq_log_phiNorm]
  exact congrArg ENNReal.log (phiNorm_eq_nativeModelIdealNorm J x)

end EnvelopeProperty.ProjBerk
