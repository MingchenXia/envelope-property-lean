import EnvelopeProperty.Global.NativeTestConfigurationLineTrivialization
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration

/-! # Original source line data produce ALL actual noncentral-open tensor powers -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (L : X.left.Modules)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L)

/-- Original source line data construct the WHOLE original open power isomorphism. -/
def unitOpenLinePowerIso (n : ℕ) :
    (Scheme.Modules.pullback C.unitOpenInclusion.left).obj (bundleTensorPower M n) ≅
      (Scheme.Modules.pullback C.unitOpenOriginalProjection.left).obj (bundleTensorPower L n) :=
  BundleTensorPowerPullback.pullbackIso C.unitOpenInclusion.left M n ≪≫
    BundleTensorPowerPullback.powerIso (C.unitOpenLineIso M L α e₁) n ≪≫
      (BundleTensorPowerPullback.pullbackIso C.unitOpenOriginalProjection.left L n).symm

/-- The SAME power comparison uses the ACTUAL original native open restriction. -/
def unitOpenRestrictLinePowerIso (n : ℕ) :
    (bundleTensorPower M n).restrict C.unitOpen.ι ≅
      (Scheme.Modules.pullback C.unitOpenOriginalProjection.left).obj (bundleTensorPower L n) :=
  (restrictFunctorIsoPullback C.unitOpen.ι).app (bundleTensorPower M n) ≪≫
    C.unitOpenLinePowerIso M L α e₁ n

/-- Every actual original generating family DERIVES genuine whole-open
generation of the SAME original total line power, with no matching premise. -/
def unitOpenPowerGeneratingSections (n : ℕ)
    (G : (bundleTensorPower L n).GeneratingSections) :
    ((bundleTensorPower M n).restrict C.unitOpen.ι).GeneratingSections := by
  let E := C.unitOpenRestrictLinePowerIso M L α e₁ n
  let : IsIso E.inv := E.isIso_inv
  let hE : Epi E.inv :=
    @CategoryTheory.IsIso.epi_of_iso C.unitOpen.toScheme.Modules _ _ _ E.inv E.isIso_inv
  exact @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections
      C.unitOpenOriginalProjection.left G) E.inv hE

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
