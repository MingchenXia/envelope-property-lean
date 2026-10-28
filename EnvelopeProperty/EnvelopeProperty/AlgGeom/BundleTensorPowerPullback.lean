import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-! # Actual original sheafified tensor powers and whole native pullback -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.BundleTensorPowerPullback
open Scheme.Modules CanonicalGeometry

@[instance_reducible] private noncomputable def originalSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
attribute [local instance] originalSchemeMonoidal

private noncomputable instance originalPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- Every original whole module isomorphism acts on ALL actual tensor powers. -/
def powerIso {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M) :
    (n : ℕ) → bundleTensorPower L n ≅ bundleTensorPower M n
  | 0 => Iso.refl _
  | n + 1 => bundleTensorIso (powerIso e n) e

/-- Actual iterated sheafified tensor powers give the SAME multiplied power. -/
def powerMulIso {X : Scheme.{u}} (L : X.Modules) (m : ℕ) :
    (n : ℕ) → bundleTensorPower (bundleTensorPower L m) n ≅ bundleTensorPower L (m * n)
  | 0 => Iso.refl _
  | n + 1 =>
    (ModularCurves.monoidalTensorObjIso
      (bundleTensorPower (bundleTensorPower L m) n) (bundleTensorPower L m)).symm ≪≫
    (powerMulIso L m n ⊗ᵢ Iso.refl (bundleTensorPower L m)) ≪≫
    TensorPowerBaseIdealGrading.tensorPowerAddIso L (m * n) m ≪≫
    eqToIso (congrArg (bundleTensorPower L) (Nat.mul_succ m n).symm)

/-- Genuine whole native pullback commutes with EVERY actual original tensor power. -/
def pullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback f).obj (bundleTensorPower L n) ≅
      bundleTensorPower ((Scheme.Modules.pullback f).obj L) n
  | 0 => pullbackUnitIso f
  | n + 1 =>
    (Scheme.Modules.pullback f).mapIso
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower L n) L).symm ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) (bundleTensorPower L n) L).symm ≪≫
    (pullbackIso f L n ⊗ᵢ Iso.refl ((Scheme.Modules.pullback f).obj L)) ≪≫
    ModularCurves.monoidalTensorObjIso
      (bundleTensorPower ((Scheme.Modules.pullback f).obj L) n)
      ((Scheme.Modules.pullback f).obj L)

end EnvelopeProperty.BundleTensorPowerPullback
