import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalNativeNaturality
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitNaturality

/-! # Every coefficient through the original native module square

The coefficient is transported by the actual upper scheme map and the
same equality comparison.  Every open and module remain original.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap
  unless (← Lean.getEnv).contains name do
    throwError "missing frozen original module square map {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `originalCoefficientSquare name :: scope.openDecls }

/-- The original equality comparison transports the same scalar and
section together on every original open. -/
theorem pushforwardCongr_hom_app_smul {Z X : Scheme.{u}}
    {a b : Z ⟶ X} (h : a = b) (M : Z.Modules) (W : X.Opens)
    (r : Γ(Z, a ⁻¹ᵁ W)) (m : Γ(M, a ⁻¹ᵁ W)) :
    ((pushforwardCongr h).hom.app M).app W (r • m) =
      (· • · : Γ(Z, b ⁻¹ᵁ W) → Γ(M, b ⁻¹ᵁ W) → Γ(M, b ⁻¹ᵁ W))
        (((pushforwardCongr h).hom.app (unitObj Z)).app W r)
        (((pushforwardCongr h).hom.app M).app W m) := by
  change M.presheaf.map _ (r • m) = Z.presheaf.map _ r • M.presheaf.map _ m
  exact M.val.map_smul _ r m

/-- The exact old native module square preserves every coefficient,
with that coefficient sent by the exact old structural square. -/
theorem originalModuleSquareMap_app_smul {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (M : Y.Modules) (W : X.Opens)
    (r : Γ(Y, p ⁻¹ᵁ W)) (m : Γ(M, p ⁻¹ᵁ W)) :
    (originalCoefficientSquare p q g s h M).app W (r • m) =
      (· • · : Γ(U, q ⁻¹ᵁ (s ⁻¹ᵁ W)) → Γ((pullback g).obj M, q ⁻¹ᵁ (s ⁻¹ᵁ W)) →
        Γ((pullback g).obj M, q ⁻¹ᵁ (s ⁻¹ᵁ W)))
        ((CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h).app W r)
        ((originalCoefficientSquare p q g s h M).app W m) := by
  let η := (pullbackPushforwardAdjunction g).unit.app M
  have hη : η.app (p ⁻¹ᵁ W) (r • m) =
      (g.app (p ⁻¹ᵁ W)) r •
        (show Γ((pullback g).obj M, g ⁻¹ᵁ (p ⁻¹ᵁ W)) from η.app (p ⁻¹ᵁ W) m) := by
    exact (η.val.app (.op (p ⁻¹ᵁ W))).hom.map_smul r m
  change ((pushforwardCongr h).hom.app ((pullback g).obj M)).app W
      (η.app (p ⁻¹ᵁ W) (r • m)) =
    (· • · : Γ(U, q ⁻¹ᵁ (s ⁻¹ᵁ W)) → Γ((pullback g).obj M, q ⁻¹ᵁ (s ⁻¹ᵁ W)) →
      Γ((pullback g).obj M, q ⁻¹ᵁ (s ⁻¹ᵁ W)))
      (((pushforwardCongr h).hom.app (unitObj U)).app W ((g.app (p ⁻¹ᵁ W)) r))
      (((pushforwardCongr h).hom.app ((pullback g).obj M)).app W
        (η.app (p ⁻¹ᵁ W) m))
  rw [hη]
  exact pushforwardCongr_hom_app_smul h ((pullback g).obj M) W _ _

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
