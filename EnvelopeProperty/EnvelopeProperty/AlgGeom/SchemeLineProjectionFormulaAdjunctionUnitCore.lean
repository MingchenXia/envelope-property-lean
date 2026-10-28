import EnvelopeProperty.AlgGeom.MonoidalProjectionFormulaUnitTransport
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # Native-unit transport with the original braiding square

Both unit representatives are the actual structure-module sheaves.  The
projection isomorphism remains the original inverse-tensor conjugate.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open Scheme.Modules EnvelopeProperty.SchemeLineProjectionFormula
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
noncomputable local instance {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

/-- Internal support for the same native unit.  The premise is the ordinary
braiding square for the fixed original monoidal pullback, and is discharged
by the actual pullback braiding producer in the final theorem. -/
theorem lineProjectionFormulaObj_unit_of_original_braiding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L)
    (hbraid : ∀ M N : X.Modules,
      Functor.LaxMonoidal.μ (pullback g) M N ≫ (pullback g).map (β_ M N).hom =
        (β_ ((pullback g).obj M) ((pullback g).obj N)).hom ≫
          Functor.LaxMonoidal.μ (pullback g) N M) :
    (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L).inv ≫
      (tensorRight L).map (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
      (lineProjectionFormulaObj g L hL (unitObj Y)).hom ≫
      (pushforward g).map
        (transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)).hom =
      (pullbackPushforwardAdjunction g).unit.app L := by
  let : (pullback g).Braided :=
    { toMonoidal := Scheme.Modules.pullbackMonoidal g
      braided := hbraid }
  have ht : Functor.OplaxMonoidal.η (pullback g) ≫
      (ModularCurves.monoidalUnitObjIso Y).hom =
      (pullback g).map (ModularCurves.monoidalUnitObjIso X).hom ≫
        (pullbackUnitIso g).hom :=
    congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso g)
  have hs : (pullbackPushforwardAdjunction g).unit.app (unitObj X) ≫
      (pushforward g).map (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    change (pullbackPushforwardAdjunction g).homEquiv (unitObj X) (unitObj Y)
      (pullbackUnitIso g).hom = _
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      g.toRingCatSheafHom
  have h := projectionFormulaOfTensorInverse_actual_unit
    (pullback g) (pushforward g) (pullbackPushforwardAdjunction g)
    L (dualObj L) hL.monoidalEvaluationIso
    (ModularCurves.monoidalUnitObjIso X) (ModularCurves.monoidalUnitObjIso Y)
    (pullbackUnitIso g) ht
  change (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L).inv ≫
      (((pullbackPushforwardAdjunction g).unit.app (unitObj X) ≫
        (pushforward g).map (pullbackUnitIso g).hom) ▷ L) ≫
      (lineProjectionFormulaObj g L hL (unitObj Y)).hom ≫
      (pushforward g).map
        (transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)).hom = _ at h
  rw [hs] at h
  exact h

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
