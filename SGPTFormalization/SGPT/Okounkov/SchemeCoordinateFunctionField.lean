import SGPT.Okounkov.SchemeCoordinateGermInjective
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The actual scheme function field embeds in the analytic coordinate field

Native integral-scheme fraction-ring machinery extends the already proved
original stalk injection. The target can be much larger than the actual
global function field; only a genuine injective map is constructed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy Filter
open TranscendentalNakamaye.Pending

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) [IsIntegral X]

/-- The genuine global scheme function field maps into the larger analytic
local fraction field by the actual native original-stalk fraction-ring lift. -/
def schemeCoordinateFunctionFieldGerm :
    X.functionField →+* FractionRing (HolGerm (Fin n → ℂ)) :=
  IsFractionRing.lift
    (g := (algebraMap (HolGerm (Fin n → ℂ)) (FractionRing (HolGerm (Fin n → ℂ)))).comp
      (schemeCoordinateStalkRegularGerm f n p))
    ((IsFractionRing.injective (HolGerm (Fin n → ℂ))
      (FractionRing (HolGerm (Fin n → ℂ)))).comp
        (schemeCoordinateStalkRegularGerm_injective f n p))

/-- The actual original function-field map is injective. -/
theorem schemeCoordinateFunctionFieldGerm_injective :
    Function.Injective (schemeCoordinateFunctionFieldGerm f n p) :=
  (schemeCoordinateFunctionFieldGerm f n p).injective

/-- Whole restriction on every actual original scheme stalk element. -/
theorem schemeCoordinateFunctionFieldGerm_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    schemeCoordinateFunctionFieldGerm f n p (algebraMap _ X.functionField a) =
      algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
        (schemeCoordinateStalkRegularGerm f n p a) :=
  IsFractionRing.lift_algebraMap _ a

/-- An actual affine regular function, read in the actual global function field
through the already produced original-stalk equivalence. -/
def schemeCoordinateRegularFunctionField (a : SchemeCoordinateAffineRing f n p) :
    X.functionField :=
  algebraMap (X.presheaf.stalk (schemeComplexPointImage f p)) X.functionField
    (schemeCoordinateStalkEquiv f n p
      (algebraMap _ (SchemeCoordinateLocalRing f n p) a))

/-- Every actual regular element has its proved original analytic germ. -/
theorem schemeCoordinateFunctionFieldGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeCoordinateFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p a) =
      algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
        (schemeCoordinateRegularGerm f n p a) := by
  rw [schemeCoordinateRegularFunctionField, schemeCoordinateFunctionFieldGerm_stalk,
    schemeCoordinateStalkRegularGerm_regular]

/-- The actual centered algebraic coordinate in K(X) maps to the literal
coordinate germ; this is a readback, not a global flag/rank assertion. -/
theorem schemeCoordinateFunctionFieldGerm_centered (i : Fin n) :
    schemeCoordinateFunctionFieldGerm f n p
      (schemeCoordinateRegularFunctionField f n p (schemeCoordinateCenteredFreeGenerator f n p i)) =
      algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
        (HolGerm.mk (fun z : Fin n → ℂ => z i)
          (Eventually.of_forall fun _ =>
            (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).differentiableAt)) := by
  rw [schemeCoordinateFunctionFieldGerm_regular, schemeCoordinateCenteredFreeGenerator_germ]

/-- Exact quotient readback on every genuine original-stalk fraction. -/
theorem schemeCoordinateFunctionFieldGerm_mk'
    (a : X.presheaf.stalk (schemeComplexPointImage f p))
    (s : nonZeroDivisors (X.presheaf.stalk (schemeComplexPointImage f p))) :
    schemeCoordinateFunctionFieldGerm f n p (IsLocalization.mk' X.functionField a s) =
      algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
          (schemeCoordinateStalkRegularGerm f n p a) /
        algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
          (schemeCoordinateStalkRegularGerm f n p s) :=
  IsFractionRing.lift_mk' _ a s

end SGPT.Okounkov
