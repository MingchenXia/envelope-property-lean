import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceNativeSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNativeOpenSquare
import EnvelopeProperty.AlgGeom.AdjunctionSquareRestriction

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
      (`openOriginalLineLeftUnit, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`openOriginalLineSquare, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing original native line square constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- The SAME old line trace restricts to the SAME native whole-module
cartesian comparison and original pulled-base-line trace on an open square. -/
theorem originalLineTrace_nativeOpenRestriction {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion s] (H : IsPullback q g s p)
    (M : X.Modules) (hM : IsInvertible M)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (ν : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s H.w.symm ≫ (pushforward s).map ν) :
    let e := (pullbackComp g p).app M ≪≫ (pullbackCongr H.w.symm).app M ≪≫
      (pullbackComp q s).symm.app M
    let Tp := (pushforward p).map (openOriginalLineLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (openOriginalLineLeftUnit M).hom
    let Tq := (pushforward q).map
      (openOriginalLineLeftUnit ((pullback q).obj ((pullback s).obj M))).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q ((pullback s).obj M)
        (hM.pullback s) (unitObj U)).inv ≫
      (tensorRight ((pullback s).obj M)).map ν ≫
      (openOriginalLineLeftUnit ((pullback s).obj M)).hom
    (restrictFunctor s).map Tp ≫ (restrictFunctorIsoPullback s).hom.app M =
      (restrictPushforwardIsoOfIsPullbackApp p q g s H ((pullback p).obj M)).hom ≫
        (pushforward q).map ((restrictFunctorIsoPullback g).hom.app ((pullback p).obj M)) ≫
          (pushforward q).map e.hom ≫ Tq := by
  let e := (pullbackComp g p).app M ≪≫ (pullbackCongr H.w.symm).app M ≪≫
      (pullbackComp q s).symm.app M
  let Tp := (pushforward p).map (openOriginalLineLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (openOriginalLineLeftUnit M).hom
  let Tq := (pushforward q).map
      (openOriginalLineLeftUnit ((pullback q).obj ((pullback s).obj M))).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q ((pullback s).obj M)
        (hM.pullback s) (unitObj U)).inv ≫
      (tensorRight ((pullback s).obj M)).map ν ≫
      (openOriginalLineLeftUnit ((pullback s).obj M)).hom
  let J := openOriginalLineSquare p q g s H.w.symm ((pullback p).obj M)
  let K := (pushforward q).map e.hom ≫ Tq
  let α := (restrictFunctorIsoPullback s).hom.app M
  have hNative := originalLineTrace_nativeSquare_of_structureSquare
    p q g s H.w.symm M hM τ ν hτ
  have hα := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (restrictAdjunction s) (pullbackPushforwardAdjunction s) M
  change (restrictAdjunction s).homEquiv M ((pullback s).obj M) α =
    (pullbackPushforwardAdjunction s).unit.app M at hα
  have hUnit : Tp ≫ (restrictAdjunction s).homEquiv M ((pullback s).obj M) α =
      J ≫ (pushforward s).map K := by
    rw [hα]
    exact hNative
  have hr := AdjunctionSquareRestriction.square_of_unit_square
    (restrictFunctor s) (pushforward s) (restrictAdjunction s) Tp α J K hUnit
  have hBc := restrict_originalModuleSquareMap p q g s H ((pullback p).obj M)
  change (restrictFunctor s).map Tp ≫ α = _
  calc
    _ = (restrictFunctor s).map J ≫
        (restrictAdjunction s).counit.app ((pushforward q).obj ((pullback g).obj ((pullback p).obj M))) ≫ K := hr
    _ = ((restrictFunctor s).map J ≫
        (restrictFunctorAdjCounitIso s).hom.app
          ((pushforward q).obj ((pullback g).obj ((pullback p).obj M)))) ≫ K := by
      exact (Category.assoc _ _ _).symm
    _ = ((restrictPushforwardIsoOfIsPullbackApp p q g s H ((pullback p).obj M)).hom ≫
        (pushforward q).map ((restrictFunctorIsoPullback g).hom.app ((pullback p).obj M))) ≫ K :=
      congrArg (fun z => z ≫ K) hBc
    _ = _ := by simp only [K, e, Tq, Category.assoc]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
