import EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryCoordinateImageCore

/-! # Original ordinary divisibility yields the same raw coordinate bound -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryDivisibilityCore
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
open NadelGlobalCanonicalTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

run_cmd
  let core := `EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryCoordinateImageCore
  for (short, original) in [
      (`ordinaryImage,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor.ordinaryImage),
      (`ordinaryImage_smul,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor.ordinaryImage_smul)] do
    let name := Lean.mkPrivateNameCore core original
    unless (← Lean.getEnv).contains name do throwError "missing checked ordinary-image law {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}
  let source := `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
  let name := Lean.mkPrivateNameCore source
    `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge
  unless (← Lean.getEnv).contains name do throwError "missing checked raw wedge"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalRawWedge name :: scope.openDecls}

private theorem ordinaryDivisibility_rawCoordinateBound
    (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B]
    (n : ℕ) (z : Fin n → B) (r : B)
    (hraw : ∃ w : affineCanonicalModule K B n,
      exteriorPower.ιMulti B n (fun j => KaehlerDifferential.D K B (z j)) = r • w) :
    ∃ w : Γ(exteriorCotangentSheaf (affineStructuralMap K (.of B)) n, ⊤),
      originalRawWedge (affineStructuralMap K (.of B)) n
          (fun j => affineCoordinateMap (.of B) (op ⊤) (z j)) =
        (Scheme.ΓSpecIso (.of B)).inv r • w := by
  obtain ⟨w, hfactor⟩ := hraw
  refine ⟨ordinaryImage K B n w, ?_⟩
  have hw := NadelBoundedCanonicalRawSections.ordinaryCoordinateSheafSection_eq K (.of B) n z
  have hf := congrArg (ordinaryImage K B n) hfactor
  exact hw.trans (hf.trans (ordinaryImage_smul K B n r w))

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryDivisibilityCore
