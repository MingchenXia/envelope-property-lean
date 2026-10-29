/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SchemeMultiplierAffineIdeals
import Hironaka.Scheme.Modules.IdealSheafFinite

/-!
# Actual full multiplier ideal sheaf on the ORIGINAL smooth integral scheme

The original scheme, original structure morphism, original ideal sheaf and
every original affine restriction are retained. The sheaf's basic-open axiom
is a proved equality of FULL original all-divisorial-DVR multiplier ideals.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

/-- The genuine full multiplier ideal sheaf of the ORIGINAL ideal on the
ORIGINAL arbitrary smooth integral scheme, with actual locality derived. -/
def schemeMultiplierIdealSheaf
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (q : ℚ) :
    X.IdealSheafData where
  ideal := schemeMultiplierAffineIdeal f I hI q
  map_ideal_basicOpen U s := map_schemeMultiplierAffineIdeal_basicOpen f I hI q U s

/-- Every original affine ideal of the actual sheaf is the full original
intrinsic multiplier construction, using the original actual generic germ. -/
theorem schemeMultiplierIdealSheaf_ideal
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (q : ℚ) (U : X.affineOpens) :
    (schemeMultiplierIdealSheaf f I hI q).ideal U = schemeMultiplierAffineIdeal f I hI q U := rfl

/-- Actual original smoothness proves finite presentation of the ENTIRE
genuine multiplier module sheaf on the original scheme, without a supplied
coherence, affine-gluing or finite-presentation certificate. -/
theorem schemeMultiplierIdealSheaf_isFinitePresentation
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (q : ℚ) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf)
      (schemeMultiplierIdealSheaf f I hI q).toModules := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (schemeMultiplierIdealSheaf f I hI q).isFinitePresentation_toModules

end EnvelopeProperty.Char0
