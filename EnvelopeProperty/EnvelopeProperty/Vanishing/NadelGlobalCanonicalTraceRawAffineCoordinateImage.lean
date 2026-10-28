import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore

/-! # Original coordinate forms before any target field normalization

The target field structure is literally the composite with the original
coefficient map. No algebra structure on that target is introduced.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (source, short, original) in [
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalRawCoordinateWedge,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalWholeRawCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.originalSquareCoordinateImage),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalRingCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeAffineCoordinateImage)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing original raw coordinate producer"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private theorem originalRawAffineCoordinateImage
    {K : Type u} [Field K] (R T : CommRingCat.{u})
    (f : Spec R ⟶ Spec (.of K)) (φ : R ⟶ T) (d : ℕ) (z : Fin d → R) :
    ((exteriorCotangentSheafMorphism f (Spec.map φ) d).val.app (op ⊤)).hom.toFun
      (originalRawCoordinateWedge f d
        (fun j => affineCoordinateMap R (op ⊤) (z j))) =
      originalRawCoordinateWedge (Spec.map φ ≫ f) d
        (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j))) := by
  exact originalWholeRawCoordinateImage f (Spec.map φ) (Spec.map φ ≫ f) rfl d
    (fun j => affineCoordinateMap R (op ⊤) (z j))
    (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j)))
    (fun j => originalRingCoordinateImage R T φ (z j))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
