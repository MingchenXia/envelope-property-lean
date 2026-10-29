import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceLineTraceSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericFiber

/-! # The native line square with the exact original rational wrappers

All conversions are checked with arbitrary schemes, field object and
module, before any normalized cover or canonical exterior object occurs.
The old private constructors are retained literally.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  for (short, original) in [
      (`originalBridgeLeftUnit, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`originalBridgeModuleSquare, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap),
      (`originalBridgeFieldLineTrace, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.wholeFieldLineTrace),
      (`originalBridgeSourceComparison, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.genericSourceComparison)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing exact original rational line constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem originalFieldLineTrace_square {X Y Z : Scheme.{u}}
    (K : CommRingCat.{u}) (hK : IsField K)
    (p : Y ⟶ X) (q : Z ⟶ Spec K) [IsFinite q] (g : Z ⟶ Y) (s : Spec K ⟶ X)
    (h : g ≫ p = q ≫ s) (M : X.Modules) (hM : IsInvertible M)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h ≫
        (pushforward s).map (NadelGlobalStructureTrace.fieldStructureTrace K hK q)) :
    let e := (pullbackComp g p).app M ≪≫ (pullbackCongr h).app M ≪≫
      (pullbackComp q s).symm.app M
    ((pushforward p).map (originalBridgeLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (originalBridgeLeftUnit M).hom) ≫
        (pullbackPushforwardAdjunction s).unit.app M =
      originalBridgeModuleSquare p q g s h ((pullback p).obj M) ≫
        (pushforward s).map ((pushforward q).map e.hom ≫
          originalBridgeFieldLineTrace K hK q ((pullback s).obj M) (hM.pullback s)) := by
  exact lineTrace_nativeSquare_of_structureSquare p q g s h M hM τ
    (NadelGlobalStructureTrace.fieldStructureTrace K hK q) hτ
/-- The exact old rational construction is the generic restriction of
the exact old inverse-PF line trace, for any original finite map and
invertible module whose actual structure trace has the old factor. -/
theorem originalGenericLineTrace_nativeRestriction {X Y : Scheme.{u}} [IsIntegral X]
    (π : Y ⟶ X) [IsFinite π] (M : X.Modules) (hM : IsInvertible M)
    (τ : (pushforward π).obj (unitObj Y) ⟶ unitObj X)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit
      (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom =
        NadelGlobalStructureTrace.genericRationalStructureTrace π) :
    let γ := X.fromSpecStalk (genericPoint X)
    let pη := CategoryTheory.Limits.pullback.fst π γ
    let qη := CategoryTheory.Limits.pullback.snd π γ
    ((pushforward π).map (originalBridgeLeftUnit ((pullback π).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj π M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (originalBridgeLeftUnit M).hom) ≫
        (pullbackPushforwardAdjunction γ).unit.app M =
      originalBridgeModuleSquare π qη pη γ CategoryTheory.Limits.pullback.condition
          ((pullback π).obj M) ≫
        (pushforward γ).map ((pushforward qη).map (originalBridgeSourceComparison π M).hom ≫
          originalBridgeFieldLineTrace X.functionField (Field.toIsField X.functionField) qη
            ((pullback γ).obj M) (hM.pullback γ)) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let pη := CategoryTheory.Limits.pullback.fst π γ
  let qη := CategoryTheory.Limits.pullback.snd π γ
  have hs : τ ≫ SheafOfModules.unitToPushforwardObjUnit γ.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap π qη pη γ
        CategoryTheory.Limits.pullback.condition ≫
      (pushforward γ).map
        (NadelGlobalStructureTrace.fieldStructureTrace X.functionField
          (Field.toIsField X.functionField) qη) := hτ
  have h := originalFieldLineTrace_square X.functionField (Field.toIsField X.functionField)
    π qη pη γ CategoryTheory.Limits.pullback.condition M hM τ hs
  dsimp (config := { proj := false, zetaDelta := false }) only
    [γ, pη, qη, originalBridgeSourceComparison] at h ⊢
  exact h
end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
