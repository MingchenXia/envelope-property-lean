import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNativeUnitSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceSquareCoefficients

/-! # Every coefficient of the same native unit-square identity -/
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
    { scope with openDecls := Lean.OpenDecl.explicit `weightedOriginalModuleSquare name :: scope.openDecls }

/-- The original square sends every coefficient times a native pulled
section to its actual structural image times the successive native
pulled section, on every original open. -/
theorem nativeUnit_originalModuleSquare_app_smul {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (M : X.Modules) (W : X.Opens)
    (b : Γ(Y, p ⁻¹ᵁ W)) (m : Γ(M, W)) :
    let e := (pullbackComp g p).app M ≪≫ (pullbackCongr h).app M ≪≫
      (pullbackComp q s).symm.app M
    let B := weightedOriginalModuleSquare p q g s h ((pullback p).obj M) ≫
      (pushforward s).map ((pushforward q).map e.hom)
    B.app W ((· • · : Γ(Y, p ⁻¹ᵁ W) → Γ((pullback p).obj M, p ⁻¹ᵁ W) →
        Γ((pullback p).obj M, p ⁻¹ᵁ W))
      b (((pullbackPushforwardAdjunction p).unit.app M).app W m)) =
    (· • · : Γ(U, q ⁻¹ᵁ (s ⁻¹ᵁ W)) →
      Γ((pullback q).obj ((pullback s).obj M), q ⁻¹ᵁ (s ⁻¹ᵁ W)) →
      Γ((pullback q).obj ((pullback s).obj M), q ⁻¹ᵁ (s ⁻¹ᵁ W)))
      ((CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h).app W b)
      (((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj M)).app (s ⁻¹ᵁ W)
        (((pullbackPushforwardAdjunction s).unit.app M).app W m)) := by
  let e := (pullbackComp g p).app M ≪≫ (pullbackCongr h).app M ≪≫
    (pullbackComp q s).symm.app M
  let B := weightedOriginalModuleSquare p q g s h ((pullback p).obj M) ≫
    (pushforward s).map ((pushforward q).map e.hom)
  let J := CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h
  let a := ((pullbackPushforwardAdjunction p).unit.app M).app W m
  have h0 := nativeUnit_originalModuleSquare p q g s h M
  change (pullbackPushforwardAdjunction p).unit.app M ≫ B =
    (pullbackPushforwardAdjunction s).unit.app M ≫ (pushforward s).map
      ((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj M)) at h0
  have hu := congrArg (fun f => Scheme.Modules.Hom.app (X := X) f W m) h0
  change e.hom.app (q ⁻¹ᵁ (s ⁻¹ᵁ W))
      ((weightedOriginalModuleSquare p q g s h ((pullback p).obj M)).app W a) =
    ((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj M)).app (s ⁻¹ᵁ W)
      (((pullbackPushforwardAdjunction s).unit.app M).app W m) at hu
  have hr := originalModuleSquareMap_app_smul p q g s h ((pullback p).obj M) W b a
  have he := (e.hom.val.app (.op (q ⁻¹ᵁ (s ⁻¹ᵁ W)))).hom.map_smul
    (show Γ(U, q ⁻¹ᵁ (s ⁻¹ᵁ W)) from J.app W b)
    ((weightedOriginalModuleSquare p q g s h ((pullback p).obj M)).app W a)
  change e.hom.app (q ⁻¹ᵁ (s ⁻¹ᵁ W))
    ((weightedOriginalModuleSquare p q g s h ((pullback p).obj M)).app W
      ((· • · : Γ(Y, p ⁻¹ᵁ W) → Γ((pullback p).obj M, p ⁻¹ᵁ W) →
        Γ((pullback p).obj M, p ⁻¹ᵁ W)) b a)) = _
  erw [hr]
  erw [he, hu]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
