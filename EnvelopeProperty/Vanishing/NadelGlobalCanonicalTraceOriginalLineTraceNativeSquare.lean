import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceLineTraceSquare

/-! # The native whole line-trace square with the original unit constraints

This arbitrary-scheme interface retains the actual original inverse projection
formula and original private unit constraints. The structure-square hypothesis
is supplied internally by the whole-chart global structure-trace theorem in its
Nadel consumer.
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
      (`nativeOriginalLineLeftUnit, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`nativeOriginalLineSquare, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing original native line square constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- The exact original inverse-PF line traces inherit the entire original
structure-trace square for every scheme square and every invertible module. -/
theorem originalLineTrace_nativeSquare_of_structureSquare {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (M : X.Modules) (hM : IsInvertible M)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (ν : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h ≫ (pushforward s).map ν) :
    let e := (pullbackComp g p).app M ≪≫ (pullbackCongr h).app M ≪≫
      (pullbackComp q s).symm.app M
    let Tp := (pushforward p).map (nativeOriginalLineLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (nativeOriginalLineLeftUnit M).hom
    let Tq := (pushforward q).map
      (nativeOriginalLineLeftUnit ((pullback q).obj ((pullback s).obj M))).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q ((pullback s).obj M)
        (hM.pullback s) (unitObj U)).inv ≫
      (tensorRight ((pullback s).obj M)).map ν ≫
      (nativeOriginalLineLeftUnit ((pullback s).obj M)).hom
    Tp ≫ (pullbackPushforwardAdjunction s).unit.app M =
      nativeOriginalLineSquare p q g s h ((pullback p).obj M) ≫
        (pushforward s).map ((pushforward q).map e.hom ≫ Tq) := by
  exact lineTrace_nativeSquare_of_structureSquare p q g s h M hM τ ν hτ

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
