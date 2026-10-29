import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericFiber
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility

/-! # The actual original canonical line embeds in its generic pushforward

The inclusion is constructed from the genuine original generic structural
unit, invertible tensoring and the existing whole line projection formula.
It is not an inverse to the ramified canonical differential. Equality with
the native adjunction-unit spelling is not asserted here.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private def actualLeftUnit {X : Scheme.{u}} (M : X.Modules) : unitObj X ⊗ M ≅ M :=
  ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

private def genericLineInclusion {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) :
    L ⟶ (pushforward (X.fromSpecStalk (genericPoint X))).obj
      ((pullback (X.fromSpecStalk (genericPoint X))).obj L) :=
  let γ := X.fromSpecStalk (genericPoint X)
  (actualLeftUnit L).inv ≫
    (tensorRight L).map (SheafOfModules.unitToPushforwardObjUnit γ.toRingCatSheafHom) ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj γ L hL
        (unitObj (Spec X.functionField))).hom ≫
      ((pushforward γ).mapIso (actualLeftUnit ((pullback γ).obj L))).hom

private theorem genericLineInclusion_mono {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) : Mono (genericLineInclusion L hL) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let : Mono (SheafOfModules.unitToPushforwardObjUnit γ.toRingCatSheafHom) :=
    NadelGlobalStructureTrace.genericStructuralUnit_mono X
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  dsimp only [genericLineInclusion]
  infer_instance

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual original canonical-line inclusion into the pushforward of its
actual generic pullback, constructed internally by the genuine line PF. -/
def genericCanonicalInclusion :
    canonicalLineSheaf f n ⟶
      (pushforward (X.fromSpecStalk (genericPoint X))).obj
        ((pullback (X.fromSpecStalk (genericPoint X))).obj (canonicalLineSheaf f n)) :=
  genericLineInclusion (canonicalLineSheaf f n) (canonicalLineSheaf_isInvertible f n)

/-- The SAME actual original canonical-line inclusion is a monomorphism;
no frame, generic comparison or desired injectivity is supplied. -/
theorem genericCanonicalInclusion_mono : Mono (genericCanonicalInclusion f n) :=
  genericLineInclusion_mono (canonicalLineSheaf f n) (canonicalLineSheaf_isInvertible f n)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
