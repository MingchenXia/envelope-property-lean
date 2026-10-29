/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierAdmissibleModulePullback
import EnvelopeProperty.AlgGeom.DominantCartierPullback

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}} [IsIntegral X] [IsReduced Y]

/-- Actual dominance and integral source derive Cartier admissibility and
the original canonical ideal-module comparison isomorphism, without QC f. -/
theorem IsInvertible.toModulesComapPullbackMap_isIso_of_dominant_integral
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y) [IsDominant f] :
    IsIso (I.toModulesComapPullbackMap f) :=
  hI.toModulesComapPullbackMap_isIso_of_isInvertible_comap f
    (hI.comap_of_dominant_integral f)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty.IntegralSchemeNormalization
variable (Y : Scheme.{u}) [IsIntegral Y]

/-- The original generic-field normalization carries the same canonical
Cartier ideal-module comparison isomorphism, with no finiteness assumption. -/
theorem cartierModuleComparison_isIso {I : Y.IdealSheafData} (hI : I.IsInvertible) :
    IsIso (I.toModulesComapPullbackMap (projection Y)) :=
  hI.toModulesComapPullbackMap_isIso_of_isInvertible_comap (projection Y)
    (cartier_comap Y hI)

end EnvelopeProperty.IntegralSchemeNormalization
