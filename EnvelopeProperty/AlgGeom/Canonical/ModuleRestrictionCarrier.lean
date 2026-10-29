import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic

/-! # Identity carriers of the original restriction of scalars

The coefficient map and module are the same original parameters.
Only the presentation of the same underlying element changes.
-/
noncomputable section
namespace EnvelopeProperty.CanonicalGeometry.ModuleRestrictionCarrier
universe u
set_option autoImplicit false

/-- Forget only the presentation of the original restricted scalar action. -/
def toUnderlying (R S : CommRingCat.{u}) (β : R →+* S)
    (M : ModuleCat.{u} S) (w : (ModuleCat.restrictScalars β).obj M) : M := w

/-- Present the same element with the original restricted scalar action. -/
def fromUnderlying (R S : CommRingCat.{u}) (β : R →+* S)
    (M : ModuleCat.{u} S) (w : M) : (ModuleCat.restrictScalars β).obj M := w

/-- Reading the original restricted presentation after forgetting it. -/
theorem fromUnderlying_toUnderlying (R S : CommRingCat.{u}) (β : R →+* S)
    (M : ModuleCat.{u} S) (w : (ModuleCat.restrictScalars β).obj M) :
    fromUnderlying R S β M (toUnderlying R S β M w) = w := rfl

/-- Reading the underlying original element after restricting its action. -/
theorem toUnderlying_fromUnderlying (R S : CommRingCat.{u}) (β : R →+* S)
    (M : ModuleCat.{u} S) (w : M) :
    toUnderlying R S β M (fromUnderlying R S β M w) = w := rfl

end EnvelopeProperty.CanonicalGeometry.ModuleRestrictionCarrier
