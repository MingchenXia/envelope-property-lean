import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaAdjunctionUnit
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericCanonicalLine

/-! # The original generic canonical inclusion is the native adjunction unit -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The SAME original generic canonical inclusion is the native unit;
no frame, scalar matching condition or normalization is supplied. -/
theorem genericCanonicalInclusion_eq_adjunction_unit
    {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    genericCanonicalInclusion f n =
      (pullbackPushforwardAdjunction (X.fromSpecStalk (genericPoint X))).unit.app
        (canonicalLineSheaf f n) :=
  SchemeLineProjectionFormulaUnit.lineProjectionFormulaObj_adjunction_unit
    (X.fromSpecStalk (genericPoint X)) (canonicalLineSheaf f n)
    (canonicalLineSheaf_isInvertible f n)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
