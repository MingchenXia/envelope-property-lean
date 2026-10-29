import EnvelopeProperty.Alterations.StableModificationBridge.NilradicalGlobalSections
import EnvelopeProperty.Alterations.Geometry.AffineReductionGlobalSections

/-!
# Nilradical Affineness

Affineness of the actual nilradical reduction INTERNALLY proves affineness of the SAME original scheme. -/

noncomputable section

namespace Alterations.StableModificationBridge.NilradicalAffineness

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

universe u

/-- The SAME actual affine nilradical reduction internally makes the original Noetherian scheme affine. -/
theorem isAffine_of_affine_reduction (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffine X.nilradical.subscheme] : IsAffine X :=
  Geometry.AffineReductionGlobalSections.isAffine_of_reduction_appTop_surjective X
    (NilradicalGlobalSections.reduction_appTop_surjective X)

end Alterations.StableModificationBridge.NilradicalAffineness
