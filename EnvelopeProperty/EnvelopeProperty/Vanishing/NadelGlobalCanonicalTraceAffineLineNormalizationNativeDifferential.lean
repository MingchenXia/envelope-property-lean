import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRestrictedGamma
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationPushforwardRead
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRawModuleMap

/-! # The original arbitrary affine native differential in its raw carrier -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u

/-- Every original native differential value reads as the same actual
adjoint exterior-differential section. -/
theorem nativeCanonicalPullbackMap_restricted_toRaw {K : Type u} [Field K]
    {A B : CommRingCat.{u}} (f : Scheme.Hom (Spec A) (Spec (.of K))) (φ : CommRingCat.Hom A B) (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (w : (moduleSpecΓFunctor (R := A)).obj (exteriorCotangentSheaf f n)) :
    restrictedModuleSpecGammaToRaw (A := A) (B := B) φ (exteriorCotangentSheaf (Spec.map φ ≫ f) n)
      ((nativeCanonicalPullbackMap f φ n).hom.toFun w) =
    affinePushforwardRawRead (A := A) (B := B) φ
      (exteriorCotangentSheaf (Spec.map φ ≫ f) n)
      (affineRawModuleMap (exteriorCotangentSheafMorphism f (Spec.map φ) n)
        (ModuleSpecGammaCarrier.toRaw A (exteriorCotangentSheaf f n) w)) := by
  exact congrArg
    (restrictedModuleSpecGammaToRaw (A := A) (B := B) φ (exteriorCotangentSheaf (Spec.map φ ≫ f) n))
    (nativeCanonicalPullbackMap_apply f φ n w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
