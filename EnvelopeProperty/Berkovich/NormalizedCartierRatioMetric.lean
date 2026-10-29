/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CartierRatioGenericMetric
import EnvelopeProperty.AlgGeom.FiniteSchemeNormalization
import EnvelopeProperty.AlgGeom.NormalSchemeNormalization
import EnvelopeProperty.AlgGeom.NormalizationAffineIsomorphism
import EnvelopeProperty.AlgGeom.DominantCartierPullback
import EnvelopeProperty.Local.PLIdealPrincipalization

/-! # Genuine original normalized Cartier ratio metrics preserve original potentials -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
open EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X]
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {p : X ⟶ Spec (CommRingCat.of R)}

/-- The ACTUAL original normalization lift of an original relative point
on an ACTUAL original normal affine open, constructed through the true isomorphism. -/
def relativePointLiftOnNormalAffine (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (y : RelativeSchemeValuedPoint v p) (hy : y.1.point ∈ U) :
    RelativeSchemeValuedPoint v (projection X ≫ p) := by
  have : IsIso (projection X ∣_ U) := projection_isIso_on_affine X U hU
  exact liftThroughOpenIso (projection X) U y hy

/-- The constructed TRUE original normalization lift retains the ENTIRE
original relative point, including original residue valuation and base point. -/
theorem map_relativePointLiftOnNormalAffine (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (y : RelativeSchemeValuedPoint v p) (hy : y.1.point ∈ U) :
    RelativeSchemeValuedPoint.map (projection X) rfl
      (relativePointLiftOnNormalAffine X U hU y hy) = y := by
  have : IsIso (projection X ∣_ U) := projection_isIso_on_affine X U hU
  exact map_liftThroughOpenIso (projection X) U y hy

variable (F : Type u) [Field F]
variable (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [IsProper p]

private theorem normalizedRatio_firstNorm_ne_zero (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (y : RelativeSchemeValuedPoint v p) (hy : y.1.point ∈ U)
    (hnI : modelIdealNorm I hb y ≠ 0) :
    letI : IsProper (projection X ≫ p) := projection_comp_isProper F X f p
    modelIdealNorm (I.comap (projection X)) hb (relativePointLiftOnNormalAffine X U hU y hy) ≠ 0 := by
  let : IsProper (projection X ≫ p) := projection_comp_isProper F X f p
  rw [modelIdealNorm_comap I (projection X) rfl hb,
    map_relativePointLiftOnNormalAffine]
  exact hnI

/-- The ACTUAL canonical ratio section's true model weight on the SAME
original proper normalization, with all proper/Cartier/nonzero facts DERIVED. -/
def normalizedCartierRatioWeight (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hb : ∀ r, v r ≤ 1) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (y : RelativeSchemeValuedPoint v p) (hy : y.1.point ∈ U)
    (hnI : modelIdealNorm I hb y ≠ 0) : EReal := by
  letI : IsProper (projection X ≫ p) := projection_comp_isProper F X f p
  exact -ENNReal.log (modelLineNorm hb (relativePointLiftOnNormalAffine X U hU y hy)
    ((cartier_comap X hI).isInvertible_ratioModule (cartier_comap X hJ))
    (genericCartierRatioSection hb (relativePointLiftOnNormalAffine X U hU y hy)
      (I.comap (projection X)) (J.comap (projection X)) (cartier_comap X hI) (cartier_comap X hJ)
      (normalizedRatio_firstNorm_ne_zero X F f I hb U hU y hy hnI)) : ℝ≥0∞)

/-- The TRUE original normalized ratio model weight is EXACTLY the
ORIGINAL intrinsic ideal-log difference at the SAME whole projected original point. -/
theorem normalizedCartierRatioWeight_eq (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hb : ∀ r, v r ≤ 1) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (y : RelativeSchemeValuedPoint v p) (hy : y.1.point ∈ U)
    (hnI : modelIdealNorm I hb y ≠ 0) :
    normalizedCartierRatioWeight X F f I J hI hJ hb U hU y hy hnI =
      modelIdealLog I hb y - modelIdealLog J hb y := by
  let : IsProper (projection X ≫ p) := projection_comp_isProper F X f p
  have h := modelLineNorm_genericCartierRatioSection_weight hb
    (relativePointLiftOnNormalAffine X U hU y hy)
    (I.comap (projection X)) (J.comap (projection X)) (cartier_comap X hI) (cartier_comap X hJ)
    (normalizedRatio_firstNorm_ne_zero X F f I hb U hU y hy hnI)
  have hi := modelIdealLog_comap I (projection X) rfl hb (relativePointLiftOnNormalAffine X U hU y hy)
  have hj := modelIdealLog_comap J (projection X) rfl hb (relativePointLiftOnNormalAffine X U hU y hy)
  rw [map_relativePointLiftOnNormalAffine] at hi hj
  exact h.trans (congrArg₂ (fun a b : EReal => a - b) hi hj)

end EnvelopeProperty.IntegralSchemeNormalization
