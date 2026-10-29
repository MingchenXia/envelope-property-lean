import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRestrictedGamma

/-! # The original affine native differential's actual decomposition -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
universe u

run_cmd
  for (short, original) in [
      (`rawOriginalAffineApply,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineAlgebraCanonicalPullbackMap_apply),
      (`rawOriginalAffineTransport,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineCanonicalΓTransport)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality original
    unless (← Lean.getEnv).contains name do throwError "missing original raw helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- Read the original native algebra-map differential through its original
field transport, with the same original restricted scalar presentation. -/
theorem affineAlgebraCanonicalPullbackMap_raw_apply {K : Type u} [Field K]
    (A B : CommRingCat.{u}) [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K A)]
    (w : (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n)) :
    restrictedModuleSpecGammaToRaw (A := A) (B := B) (CommRingCat.ofHom φ.toRingHom)
      (exteriorCotangentSheaf (affineStructuralMap K B) n)
      ((affineAlgebraCanonicalPullbackMap A B φ n).hom.toFun w) =
    restrictedModuleSpecGammaToRaw (A := A) (B := B) (CommRingCat.ofHom φ.toRingHom)
      (exteriorCotangentSheaf (affineStructuralMap K B) n)
      (restrictedModuleSpecGammaFromNative (A := A) (B := B) (CommRingCat.ofHom φ.toRingHom)
        (exteriorCotangentSheaf (affineStructuralMap K B) n)
        ((rawOriginalAffineTransport B (affineAlgebraMap_structuralSquare K A B φ) n).hom.toFun
          (ModuleRestrictionCarrier.toUnderlying A B φ.toRingHom
            ((moduleSpecΓFunctor (R := B)).obj
              (exteriorCotangentSheaf
                (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A) n))
            ((nativeCanonicalPullbackMap (affineStructuralMap K A)
              (CommRingCat.ofHom φ.toRingHom) n).hom.toFun w)))) := by
  exact congrArg
    (restrictedModuleSpecGammaToRaw (A := A) (B := B) (CommRingCat.ofHom φ.toRingHom)
      (exteriorCotangentSheaf (affineStructuralMap K B) n))
    (rawOriginalAffineApply A B φ n w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
