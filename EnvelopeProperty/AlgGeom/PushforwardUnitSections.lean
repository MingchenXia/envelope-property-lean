import ModularCurves.Picard.InvertibleSheaf

/-! # Original section values of the actual pullback-unit adjunction -/

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The SAME native pullback-unit homomorphism is adjoint to the actual
original structure-ring map, as an ENTIRE original module morphism. -/
theorem pullbackUnitIso_hom_homEquiv :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom

/-- Adjointing the SAME original section agrees on the ENTIRE map with
actual pushforward after the SAME original structure-ring homomorphism. -/
theorem pushforwardUnitSection_homEquiv {N : Y.Modules} (s : unitObj Y ⟶ N) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ ((pullbackUnitIso g).hom ≫ s) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫ (pushforward g).map s := by
  rw [Adjunction.homEquiv_naturality_right, pullbackUnitIso_hom_homEquiv]

/-- Every original function is sent to the SAME original section evaluated
on its actual pullback by the original structure-ring map. -/
theorem pushforwardUnitSection_homEquiv_app {N : Y.Modules} (s : unitObj Y ⟶ N)
    (U : X.Opens) (a : Γ(X, U)) :
    ((pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackUnitIso g).hom ≫ s)).val.app (.op U) a =
        s.val.app (.op (g ⁻¹ᵁ U)) (g.app U a) := by
  exact congr($(pushforwardUnitSection_homEquiv g s).val.app (.op U) |>.hom a)

end
end AlgebraicGeometry.Scheme.Modules
