import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGeneric
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartTrace
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericFiber

/-! # Actual complete chart fibers are the SAME original generic fiber

The original germ map supplies the coefficient-field map. The actual
whole-chart cartesian square supplies the entire generic-fiber isomorphism
and both projection identities, without incoming matching data.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

/-- The actual original germ map gives the original coefficient-field map. -/
def genericBaseMap : Spec X.functionField ⟶ Spec Γ(X, C.base.1) :=
  Spec.map (X.germToFunctionField C.base.1)

/-- The whole original generic field point is retained, with no supplied
chart/generic-point matching certificate. -/
theorem genericBaseMap_over_original :
    C.genericBaseMap ≫ C.base.2.fromSpec = X.fromSpecStalk (genericPoint X) := by
  change C.base.2.fromSpecStalk (genericPoint_mem_nonempty_open C.base.1) = _
  exact C.base.2.fromSpecStalk_eq_fromSpecStalk _

private theorem actualGenericSquare :
    IsPullback
      (pullback.fst C.scalarMap C.genericBaseMap ≫ C.sourceMap)
      (pullback.snd C.scalarMap C.genericBaseMap) π
      (X.fromSpecStalk (genericPoint X)) := by
  have h := (IsPullback.of_hasPullback C.scalarMap C.genericBaseMap).paste_horiz
    C.isPullback.flip
  simpa only [genericBaseMap_over_original] using h

/-- The ACTUAL ENTIRE chart base change is the SAME original generic
fiber, including every component and its original projections. -/
def genericFiberIso :
    pullback C.scalarMap C.genericBaseMap ≅
      pullback π (X.fromSpecStalk (genericPoint X)) :=
  C.actualGenericSquare.isoPullback

/-- The original source projection is literally preserved by the actual
whole generic-fiber comparison. -/
theorem genericFiberIso_fst :
    C.genericFiberIso.hom ≫ pullback.fst π (X.fromSpecStalk (genericPoint X)) =
      pullback.fst C.scalarMap C.genericBaseMap ≫ C.sourceMap :=
  C.actualGenericSquare.isoPullback_hom_fst

/-- The actual generic field structure is preserved by the SAME whole
fiber comparison, rather than supplied as matching data. -/
theorem genericFiberIso_snd :
    C.genericFiberIso.hom ≫ pullback.snd π (X.fromSpecStalk (genericPoint X)) =
      pullback.snd C.scalarMap C.genericBaseMap :=
  C.actualGenericSquare.isoPullback_hom_snd

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
