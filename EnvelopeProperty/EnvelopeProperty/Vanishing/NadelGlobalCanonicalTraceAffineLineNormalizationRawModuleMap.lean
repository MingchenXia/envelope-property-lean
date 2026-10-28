import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationGamma

/-! # The original sheaf map on its declared top-section carriers -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u

/-- The actual top component, with its original source and target section types
kept as the declared interface. -/
def affineRawModuleMap {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (s : F.val.obj (op ⊤)) : G.val.obj (op ⊤) := f.app ⊤ s

/-- This interface evaluates the same actual sheaf component. -/
theorem affineRawModuleMap_apply {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (s : F.val.obj (op ⊤)) :
    affineRawModuleMap f s = f.app ⊤ s := rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
