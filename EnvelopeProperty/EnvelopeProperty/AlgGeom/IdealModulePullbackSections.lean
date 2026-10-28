/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial

/-!
# Actual sections of the canonical ideal-module pullback comparison

The original genuine adjunction unit followed by the canonical comparison
recovers the actual geometric section map on every original preimage open.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- The actual canonical comparison recovers the original entire section map
under the genuine module pullback adjunction unit. -/
theorem toModulesComapPullbackMap_unit (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app I.toModules ≫
        (Scheme.Modules.pushforward f).map (I.toModulesComapPullbackMap f) =
      I.toModulesComapPushforwardMap f := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv I.toModules
    (I.comap f).toModules).apply_symm_apply (I.toModulesComapPushforwardMap f)

/-- The unit identity holds on every actual original section and full preimage open. -/
theorem toModulesComapPullbackMap_unit_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    (W : Y.Opens) (s : Γ(I.toModules, W)) :
    (I.toModulesComapPullbackMap f).app (f ⁻¹ᵁ W)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app I.toModules).app W s) =
      (I.toModulesComapPushforwardMap f).app W s := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun q => q.app W) (I.toModulesComapPullbackMap_unit f)) s

/-- The actual included unit section is exactly its image under the original
whole scheme section map, without a flatness or affine hypothesis. -/
theorem toModulesComapPullbackMap_unit_app_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y)
    (W : Y.Opens) (s : Γ(I.toModules, W)) :
    (show (I.comap f).toSubmodule.obj (op (f ⁻¹ᵁ W)) from
      (I.toModulesComapPullbackMap f).app (f ⁻¹ᵁ W)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app I.toModules).app W s)).1 =
      (f.app W).hom (s : I.toSubmodule.obj (op W)).1 := by
  rw [I.toModulesComapPullbackMap_unit_app f W s]
  exact I.toModulesComapPushforwardMap_app f W s

end AlgebraicGeometry.Scheme.IdealSheafData
