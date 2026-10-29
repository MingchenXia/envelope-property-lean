import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRestrictedGamma
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRawModuleMap

/-! # The original equality transport in the original restricted raw carrier -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
universe u

run_cmd
  for (short, original) in [
      (`rawOriginalAffineTransport,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineCanonicalΓTransport),
      (`rawOriginalAffineTransportEq,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineCanonicalΓTransport_eq)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality original
    unless (← Lean.getEnv).contains name do throwError "missing original field transport {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- The original field equality transport has its actual raw value for every
original restricted section, independently of any differential. -/
theorem affineCanonicalGammaTransport_restricted_toRaw {K : Type u} [Field K]
    {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    {f₁ f₂ : Scheme.Hom (Spec B) (Spec (.of K))} (h : f₁ = f₂) (n : ℕ)
    (s : (ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ n))) :
    restrictedModuleSpecGammaToRaw (A := A) (B := B) φ (exteriorCotangentSheaf f₂ n)
      (restrictedModuleSpecGammaFromNative (A := A) (B := B) φ (exteriorCotangentSheaf f₂ n)
        ((rawOriginalAffineTransport B h n).hom.toFun
          (ModuleRestrictionCarrier.toUnderlying A B φ.hom
            ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ n)) s))) =
    affineRawModuleMap (eqToHom (congrArg (fun f => exteriorCotangentSheaf f n) h))
      (restrictedModuleSpecGammaToRaw (A := A) (B := B) φ (exteriorCotangentSheaf f₁ n) s) := by
  rw [rawOriginalAffineTransportEq]
  cases h
  rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
