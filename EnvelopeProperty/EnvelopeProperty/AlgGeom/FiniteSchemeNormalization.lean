/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import EnvelopeProperty.Berkovich.SchemeFiniteNormalization
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite and proper actual normalization of original finite-type integral models -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable (F : Type u) [Field F]
variable (X : Scheme.{u}) [IsIntegral X]

/-- The ACTUAL original normalization projection is FINITE for an original
integral scheme locally of finite type over an original field. -/
theorem projection_isFinite (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] :
    IsFinite (projection X) := by
  exact projection_isFinite_of_locallyOfFiniteType f

/-- The SAME ACTUAL original normalization projection is proper, with
finiteness derived from the ORIGINAL arbitrary-field finite-type structure. -/
theorem projection_isProper (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] :
    IsProper (projection X) := by
  have := projection_isFinite F X f
  infer_instance

/-- The SAME ACTUAL original finite normalization remains proper over
EVERY original proper model base, without a new properness certificate. -/
theorem projection_comp_isProper (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    {S : Scheme.{u}} (p : X ⟶ S) [IsProper p] : IsProper (projection X ≫ p) := by
  have := projection_isProper F X f
  infer_instance

end EnvelopeProperty.IntegralSchemeNormalization
