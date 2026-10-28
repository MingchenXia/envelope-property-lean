import EnvelopeProperty.AlgGeom.MonoidalAdjunctionBraided
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-! # Braiding of the original presheaf pullback monoidal structure -/
noncomputable section
namespace EnvelopeProperty.SchemePullbackBraided
open CategoryTheory MonoidalCategory AlgebraicGeometry
universe u v₁ v₂ u₁ u₂
set_option autoImplicit false

/-- The native factored pushforward comparison is braided: both tensor
comparison and braiding act on pure tensors by their literal scalar formulas. -/
@[implicit_reducible]
def pushforwardFactoredLaxBraided
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
      F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforwardFactored φ).LaxBraided where
  toLaxMonoidal := PresheafOfModules.pushforwardFactoredLaxMonoidal φ
  braided M N := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
    rfl

/-- The actual strong monoidal presheaf pullback, with its existing doctrinal
oplax maps and existing inverses, preserves braiding. -/
@[implicit_reducible]
def presheafPullbackBraided {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (PresheafOfModules.pullback.{u}
      (PresheafOfModules.schemeRingPresheafHom f)).Braided := by
  letI := PresheafOfModules.pullbackMonoidal f
  letI := pushforwardFactoredLaxBraided (PresheafOfModules.schemeRingPresheafHom f)
  let adj := PresheafOfModules.pullbackPushforwardFactoredAdjunction
    (PresheafOfModules.schemeRingPresheafHom f)
  haveI : adj.IsMonoidal := by
    let _ := adj.leftAdjointOplaxMonoidal
    exact inferInstanceAs adj.IsMonoidal
  exact MonoidalAdjunctionBraided.leftAdjointBraided adj

/-- This adds only the braiding proof to the original monoidal data. -/
theorem presheafPullbackBraided_toMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (presheafPullbackBraided f).toMonoidal = PresheafOfModules.pullbackMonoidal f := rfl

end EnvelopeProperty.SchemePullbackBraided
