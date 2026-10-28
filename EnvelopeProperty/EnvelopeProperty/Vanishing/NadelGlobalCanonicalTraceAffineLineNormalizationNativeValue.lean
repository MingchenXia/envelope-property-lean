import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationNativeValueOnCarriers

/-! # The same original native differential for arbitrary bundled affine rings -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
universe u

/-- The actual native algebra-map differential has its original transported
adjoint value, with the original raw section carriers retained. -/
theorem affineAlgebraCanonicalPullbackMap_toRaw {K : Type u} [Field K]
    (A B : CommRingCat.{u}) [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K A)]
    (w : (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n)) :
    ModuleSpecGammaCarrier.toRaw B (exteriorCotangentSheaf (affineStructuralMap K B) n)
      (restrictedNativeSection φ.toRingHom
        ((moduleSpecΓFunctor (R := B)).obj
          (exteriorCotangentSheaf (affineStructuralMap K B) n))
        ((affineAlgebraCanonicalPullbackMap A B φ n).hom.toFun w)) =
    affineRawModuleMap (eqToHom (congrArg (fun g => exteriorCotangentSheaf g n)
      (affineAlgebraMap_structuralSquare K A B φ)))
        (affinePushforwardRawRead (A := A) (B := B) (CommRingCat.ofHom φ.toRingHom)
          (exteriorCotangentSheaf
            (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A) n)
          (affineRawModuleMap (exteriorCotangentSheafMorphism (affineStructuralMap K A)
            (Spec.map (CommRingCat.ofHom φ.toRingHom)) n)
              (ModuleSpecGammaCarrier.toRaw A
                (exteriorCotangentSheaf (affineStructuralMap K A) n) w))) := by
  cases A
  cases B
  exact affineAlgebraCanonicalPullbackMap_toRaw_onCarriers _ _ φ n w

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
