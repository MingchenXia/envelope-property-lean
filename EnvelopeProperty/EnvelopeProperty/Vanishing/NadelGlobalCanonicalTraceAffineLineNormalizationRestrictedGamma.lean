import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationGamma
import EnvelopeProperty.AlgGeom.Canonical.ModuleRestrictionCarrier

/-! # Raw readers of the original restricted affine Gamma module -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u

/-- Read the same restricted native element in its original raw section carrier. -/
def restrictedModuleSpecGammaToRaw {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (M : (Spec B).Modules)
    (s : (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := B)).obj M)) :
    M.val.obj (op ⊤) :=
  ModuleSpecGammaCarrier.toRaw B M
    (ModuleRestrictionCarrier.toUnderlying A B φ.hom ((moduleSpecΓFunctor (R := B)).obj M) s)

/-- Give the same original native element its restricted scalar presentation. -/
def restrictedModuleSpecGammaFromNative {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (M : (Spec B).Modules) (s : (moduleSpecΓFunctor (R := B)).obj M) :
    (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := B)).obj M) :=
  ModuleRestrictionCarrier.fromUnderlying A B φ.hom ((moduleSpecΓFunctor (R := B)).obj M) s


/-- The two original restricted readers agree already for an arbitrary module. -/
theorem restrictedModuleSpecGammaToRaw_original {A B : CommRingCat.{u}}
    (φ : CommRingCat.Hom A B) (M : (Spec B).Modules)
    (v : (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := B)).obj M)) :
    ModuleSpecGammaCarrier.toRaw B M
        (restrictedNativeSection φ.hom ((moduleSpecΓFunctor (R := B)).obj M) v) =
      restrictedModuleSpecGammaToRaw φ M v := rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
