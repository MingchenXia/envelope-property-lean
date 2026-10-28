/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelHomNorms
import EnvelopeProperty.Berkovich.SchemeModelIdealCenter
import EnvelopeProperty.AlgGeom.LocalSpecIdealPullbackImage
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves

/-! # Genuine Cartier inclusion norms equal intrinsic original ideal norms -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f]

/-- The genuine ACTUAL Cartier line inclusion has EXACTLY the intrinsic
original model-ideal norm, from its ENTIRE actual valuative pullback ideal. -/
theorem modelHomNorm_idealInclusion (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    (modelHomNorm hb y hI.isInvertibleModule_toModules
      (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion : ℝ≥0∞) =
      modelIdealNorm I hb y := by
  obtain ⟨e⟩ := exists_centerLineUnitIso hb y hI.isInvertibleModule_toModules
  let d := Scheme.Modules.pullbackUnitIso (centerLift hb y)
  rw [modelHomNorm_eq_frames hb y hI.isInvertibleModule_toModules
    (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion e d,
    modelIdealNorm_eq_centerPullback I hb y,
    I.localSpec_pullbackIdeal_eq_span_frame (centerLift hb y) e,
    Spectrum.idealNorm_span (isBounded_centerTopSpectrum y)]
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  rfl

/-- The TRUE logarithm of the ACTUAL original Cartier inclusion norm
is the intrinsic original model ideal logarithm, including zero values. -/
theorem modelHomNorm_idealInclusion_log (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    ENNReal.log (modelHomNorm hb y hI.isInvertibleModule_toModules
      (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion : ℝ≥0∞) =
      modelIdealLog I hb y :=
  congrArg ENNReal.log (modelHomNorm_idealInclusion I hI hb y)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
