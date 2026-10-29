import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceOpenRestriction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceNaturality
import EnvelopeProperty.AlgGeom.SchemePullbackCongrInverse

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
      (`fixedLineOriginalLeftUnit, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`fixedLineOriginalSquare, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing original native line square constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- Transporting the SAME original line trace along a specified line
isomorphism preserves the entire SAME native open cartesian comparison. -/
theorem originalLineTrace_nativeFixedLineRestriction {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion s] (H : IsPullback q g s p)
    (M : X.Modules) (hM : IsInvertible M) (N : V.Modules) (hN : IsInvertible N)
    (a : (pullback s).obj M ≅ N)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (ν : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s H.w.symm ≫ (pushforward s).map ν) :
    let c := (pullbackComp q s).app M ≪≫ (pullbackCongr H.w).app M ≪≫
      ((pullbackComp g p).app M).symm
    let eBase := (restrictFunctorIsoPullback s).app M ≪≫ a
    let eSource := (restrictPushforwardIsoOfIsPullback p q g s H).app ((pullback p).obj M) ≪≫
      (pushforward q).mapIso ((restrictFunctorIsoPullback g).app ((pullback p).obj M) ≪≫
        c.symm ≪≫ (pullback q).mapIso a)
    let Tp := (pushforward p).map (fixedLineOriginalLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (fixedLineOriginalLeftUnit M).hom
    let TN := (pushforward q).map (fixedLineOriginalLeftUnit ((pullback q).obj N)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q N hN (unitObj U)).inv ≫
      (tensorRight N).map ν ≫ (fixedLineOriginalLeftUnit N).hom
    (restrictFunctor s).map Tp ≫ eBase.hom = eSource.hom ≫ TN := by
  let c := (pullbackComp q s).app M ≪≫ (pullbackCongr H.w).app M ≪≫
      ((pullbackComp g p).app M).symm
  let eBase := (restrictFunctorIsoPullback s).app M ≪≫ a
  let eSource := (restrictPushforwardIsoOfIsPullback p q g s H).app ((pullback p).obj M) ≪≫
      (pushforward q).mapIso ((restrictFunctorIsoPullback g).app ((pullback p).obj M) ≪≫
        c.symm ≪≫ (pullback q).mapIso a)
  let Tp := (pushforward p).map (fixedLineOriginalLeftUnit ((pullback p).obj M)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj p M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (fixedLineOriginalLeftUnit M).hom
  let TN := (pushforward q).map (fixedLineOriginalLeftUnit ((pullback q).obj N)).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q N hN (unitObj U)).inv ≫
      (tensorRight N).map ν ≫ (fixedLineOriginalLeftUnit N).hom
  let e := (pullbackComp g p).app M ≪≫ (pullbackCongr H.w.symm).app M ≪≫
    (pullbackComp q s).symm.app M
  have he : e.hom = c.inv := by
    dsimp only [e, c, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
    rw [SchemePullbackCongrInverse.reverse_hom (q ≫ s) (g ≫ p) H.w M]
    simp only [Category.assoc]
    rfl
  let Tq := (pushforward q).map
      (fixedLineOriginalLeftUnit ((pullback q).obj ((pullback s).obj M))).inv ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj q ((pullback s).obj M)
        (hM.pullback s) (unitObj U)).inv ≫
      (tensorRight ((pullback s).obj M)).map ν ≫
      (fixedLineOriginalLeftUnit ((pullback s).obj M)).hom
  have hOpen := originalLineTrace_nativeOpenRestriction p q g s H M hM τ ν hτ
  have hNat := originalLineTrace_naturality q ((pullback s).obj M) N (hM.pullback s) hN ν a.hom
  change (restrictFunctor s).map Tp ≫ (restrictFunctorIsoPullback s).hom.app M =
    (restrictPushforwardIsoOfIsPullbackApp p q g s H ((pullback p).obj M)).hom ≫
      (pushforward q).map ((restrictFunctorIsoPullback g).hom.app ((pullback p).obj M)) ≫
        (pushforward q).map e.hom ≫ Tq at hOpen
  change (pushforward q).map ((pullback q).map a.hom) ≫ TN = Tq ≫ a.hom at hNat
  have h1 := congrArg (fun z => z ≫ a.hom) hOpen
  simp only [Category.assoc] at h1
  rw [← hNat] at h1
  rw [he] at h1
  dsimp only [eBase, eSource, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simpa only [Tp, TN, e, c, Functor.map_comp, Functor.mapIso_hom, Iso.app_hom,
    restrictPushforwardIsoOfIsPullback, NatIso.ofComponents_hom_app, Category.assoc] using h1

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
