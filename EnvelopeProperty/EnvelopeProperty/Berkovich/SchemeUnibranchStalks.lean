/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.UnibranchEquiv
import EnvelopeProperty.Berkovich.SchemeUnibranchNormalization

/-!
# Standard geometric unibranchness of actual scheme stalks

The scheme property is the STANDARD structural local-ring property at every
actual stalk, not a normalization fibre or native-point condition. The actual
Spec stalk isomorphism transports it to the original A_p before the native
normalization theorem is used. Scope remains integral affine normalization.
-/

open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace EnvelopeProperty

/-- STANDARD geometric unibranchness at EVERY actual scheme local stalk. No normalization or native endpoint is included. -/
class IsGeometricallyUnibranchScheme (X : Scheme.{u}) : Prop where
  isGeometricallyUnibranch_stalk (x : X) : IsGeometricallyUnibranchLocalRing (X.presheaf.stalk x)

set_option backward.isDefEq.respectTransparency false in
/-- The TRUE affine scheme-stalk isomorphism DERIVES structural geometric unibranchness of each ORIGINAL prime localization. -/
theorem isGeometricallyUnibranch_atPrime_of_scheme (A : Type u) [CommRing A]
    [IsGeometricallyUnibranchScheme (Spec (CommRingCat.of A))] (p : PrimeSpectrum A) :
    IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal) := by
  let : IsGeometricallyUnibranchLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    IsGeometricallyUnibranchScheme.isGeometricallyUnibranch_stalk (X := Spec (CommRingCat.of A)) p
  exact IsGeometricallyUnibranchLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv

namespace DomainNormalization
variable (A : Type u) [CommRing A] [IsDomain A]
  [IsGeometricallyUnibranchScheme (Spec (CommRingCat.of A))]

/-- Actual STANDARD scheme-stalk geometry DERIVES radiciality of the literal original normalization. -/
theorem projection_universallyInjective_of_schemeStalks : UniversallyInjective (projection A) :=
  projection_universallyInjective A (isGeometricallyUnibranch_atPrime_of_scheme A)

/-- Actual STANDARD geometric unibranchness on scheme stalks yields the true whole native normalization homeomorphism. -/
def nativeHomeomorph_of_schemeStalks :
    Berkovich.SchemeValuedPoint (Spec (CommRingCat.of (integralClosure A (FractionRing A)))) ≃ₜ
      Berkovich.SchemeValuedPoint (Spec (CommRingCat.of A)) :=
  nativeHomeomorph A (isGeometricallyUnibranch_atPrime_of_scheme A)

/-- The stalk-based native homeomorphism retains EVERY original whole normalization point map. -/
@[simp]
theorem nativeHomeomorph_of_schemeStalks_apply
    (y : Berkovich.SchemeValuedPoint (Spec (CommRingCat.of (integralClosure A (FractionRing A))))) :
    nativeHomeomorph_of_schemeStalks A y = Berkovich.SchemeValuedPoint.map (projection A) y := rfl

/-- Above ANY exact common coefficient point the SAME structural stalk hypothesis gives the actual native homeomorphism. -/
def relativeNativeHomeomorph_of_schemeStalks {R : Type u} [CommRing R]
    (v : Valuation R ℝ≥0) (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    Berkovich.RelativeSchemeValuedPoint v (projection A ≫ f) ≃ₜ Berkovich.RelativeSchemeValuedPoint v f :=
  relativeNativeHomeomorph A v f (isGeometricallyUnibranch_atPrime_of_scheme A)

/-- Whole original relative native points and their full residue valuations are preserved. -/
@[simp]
theorem relativeNativeHomeomorph_of_schemeStalks_apply {R : Type u} [CommRing R]
    (v : Valuation R ℝ≥0) (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (y : Berkovich.RelativeSchemeValuedPoint v (projection A ≫ f)) :
    relativeNativeHomeomorph_of_schemeStalks A v f y =
      Berkovich.RelativeSchemeValuedPoint.map (projection A) rfl y := rfl

end DomainNormalization
end EnvelopeProperty
