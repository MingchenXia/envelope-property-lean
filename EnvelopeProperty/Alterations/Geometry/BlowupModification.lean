import EnvelopeProperty.Alterations.Modification
import EnvelopeProperty.Alterations.Geometry.BlowupAlteration
import EnvelopeProperty.Alterations.Geometry.BlowupComplement

/-! # The actual global blowup as a modification -/

open AlgebraicGeometry CategoryTheory

namespace Alterations.Geometry.BlowupModification

universe u

open BlowupGluing

/-- The native global blowup in a proper-support ideal is a modification. -/
theorem blowupStructure_isModification {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    IsModification (blowupStructure D) := by
  let := BlowupAlteration.blowupStructure_isProper D
  exact {
    sourceIntegral := BlowupIntegral.isIntegral_blowup D hD
    targetIntegral := inferInstance
    birational := BlowupComplement.blowupStructure_birationalOver D hD }

end Alterations.Geometry.BlowupModification
