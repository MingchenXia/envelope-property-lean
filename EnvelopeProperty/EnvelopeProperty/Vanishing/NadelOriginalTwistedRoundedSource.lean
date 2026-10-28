import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback

/-! # The exact native source for every original base-line twist

The original Q, whole pullback and base lines remain unchanged. This
isomorphism identifies the literal source of each twisted numerator
application with the literal global-twist family used by projective
localization. No vanishing or trace is an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelOriginalTwistedRoundedSource
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

private noncomputable instance originalTwistedSourcePullbackMonoidal
    {X Y : Scheme.{u}} (μ : Y ⟶ X) :
    (Scheme.Modules.pullback μ).Monoidal := Scheme.Modules.pullbackMonoidal μ

/-- The same ordinary original twist is exactly the global projective
family on the same source, under the original pullback monoidal maps. -/
def originalTwistedSourceIso {X Y : Scheme.{u}} (μ : Y ⟶ X)
    (Q : Y.Modules) (A H : X.Modules) (m : ℕ) :
    Scheme.Modules.tensorObj Q ((pullback μ).obj (A ⊗ bundleTensorPower H m)) ≅
      Scheme.Modules.tensorObj Q ((pullback μ).obj A) ⊗
        bundleTensorPower ((pullback μ).obj H) m :=
  (ModularCurves.monoidalTensorObjIso Q
    ((pullback μ).obj (A ⊗ bundleTensorPower H m))).symm ≪≫
    (Iso.refl Q ⊗ᵢ (Functor.Monoidal.μIso (pullback μ) A (bundleTensorPower H m)).symm) ≪≫
    (Iso.refl Q ⊗ᵢ (Iso.refl ((pullback μ).obj A) ⊗ᵢ
      BundleTensorPowerPullback.pullbackIso μ H m)) ≪≫
    (α_ Q ((pullback μ).obj A) (bundleTensorPower ((pullback μ).obj H) m)).symm ≪≫
    (ModularCurves.monoidalTensorObjIso Q ((pullback μ).obj A) ⊗ᵢ Iso.refl _)

end EnvelopeProperty.Vanishing.NadelOriginalTwistedRoundedSource
