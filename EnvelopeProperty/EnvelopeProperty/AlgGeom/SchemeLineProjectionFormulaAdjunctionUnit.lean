import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaAdjunctionUnitCore
import EnvelopeProperty.AlgGeom.SchemePullbackBraided
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # The native adjunction unit of the original line projection formula

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

/-- The actual original projection formula, with the actual structural
unit and actual structure-sheaf left unitors, is the native adjunction unit. -/
theorem lineProjectionFormulaObj_adjunction_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L) :
    (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L).inv ≫
      (tensorRight L).map (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
      (lineProjectionFormulaObj g L hL (unitObj Y)).hom ≫
      (pushforward g).map
        (transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)).hom =
      (pullbackPushforwardAdjunction g).unit.app L := by
  apply lineProjectionFormulaObj_unit_of_original_braiding g L hL
  intro M N
  let : (pullback g).Braided := SchemePullbackBraided.pullbackBraided g
  exact Functor.LaxBraided.braided (F := pullback g) M N

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
