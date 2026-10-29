import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartGenericFiber
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-! # Native restriction of the SAME original generic target to a whole chart

The actual chart generic map and identity on the SAME original generic
scheme form a pullback square, because the chart is an open immersion
and its original generic triangle is proved. Native open base change
therefore compares the generic target for every module, without a new
chart field or a restriction-to-identity coherence assertion.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

private theorem genericTarget_actualSquare :
    IsPullback C.genericBaseMap (𝟙 (Spec X.functionField)) C.base.2.fromSpec
      (X.fromSpecStalk (genericPoint X)) := by
  apply IsPullback.of_vert_isIso_mono
  exact ⟨by simpa only [Category.id_comp] using C.genericBaseMap_over_original⟩

/-- Native restriction of EVERY original generic pushforward to the
actual whole chart is the pushforward by its SAME original generic map.
The module on the right is restricted along the identity of the SAME
Spec X.functionField; no replacement field or chosen component occurs. -/
def genericTargetRestrictionIso :
    pushforward (X.fromSpecStalk (genericPoint X)) ⋙ restrictFunctor C.base.2.fromSpec ≅
      restrictFunctor (𝟙 (Spec X.functionField)) ⋙ pushforward C.genericBaseMap :=
  restrictPushforwardIsoOfIsPullback (X.fromSpecStalk (genericPoint X))
    C.genericBaseMap (𝟙 (Spec X.functionField)) C.base.2.fromSpec C.genericTarget_actualSquare

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
