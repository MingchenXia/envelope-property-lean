import EnvelopeProperty.AlgGeom.NativeRealPicard

/-! # Actual tensor/dual/isomorphism operations in SAME original native real Picard spaces -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealPicard
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The SAME original native Picard unit gives zero in its genuine real scalar extension. -/
@[simp]
theorem picardClass_one (X : Scheme.{u}) : picardClass X 1 = 0 := by
  change (1 : ℝ) ⊗ₜ[ℤ] (0 : Additive X.Pic) = 0
  exact TensorProduct.tmul_zero (Additive X.Pic) (1 : ℝ)

/-- The SAME original native Picard multiplication gives genuine addition of real classes. -/
theorem picardClass_mul {X : Scheme.{u}} (a b : X.Pic) :
    picardClass X (a * b) = picardClass X a + picardClass X b :=
  TensorProduct.tmul_add _ _ _

/-- The SAME original native Picard inverse gives the genuine negative real class. -/
theorem picardClass_inv {X : Scheme.{u}} (a : X.Pic) :
    picardClass X a⁻¹ = -picardClass X a :=
  TensorProduct.tmul_neg _ _

/-- WHOLE original actual line isomorphisms preserve their SAME original real Picard class. -/
theorem lineClass_eq_of_iso {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (e : L ≅ M) :
    lineClass L hL = lineClass M hM :=
  congrArg (picardClass X) (ProjectiveGeneratedLineClasses.lineClass_eq_of_iso hL hM e)

/-- The SAME actual original unit line has zero real Picard class. -/
@[simp]
theorem lineClass_unit (X : Scheme.{u}) : lineClass (unitObj X) (isInvertible_unit (X := X)) = 0 := by
  rw [lineClass, ProjectiveGeneratedLineClasses.lineClass_unit, picardClass_one]

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- SAME actual original tensor product of lines is the SUM of their true real Picard classes. -/
theorem lineClass_tensor {X : Scheme.{u}} (L M : X.Modules)
    (hL : IsInvertible L) (hM : IsInvertible M) :
    lineClass (L ⊗ M) (tensorInvertible hL hM) = lineClass L hL + lineClass M hM := by
  rw [lineClass, ProjectiveGeneratedLineClasses.lineClass_tensor, picardClass_mul]
  rfl

/-- SAME actual original dual with actual evaluation is the NEGATIVE real Picard class. -/
theorem lineClass_dual {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L) :
    lineClass (dualObj L) hL.dual = -lineClass L hL := by
  rw [lineClass, ProjectiveGeneratedLineClasses.lineClass_dual, picardClass_inv]
  rfl

/-- A WHOLE original actual quotient-of-lines isomorphism gives EXACT subtraction in the
SAME genuine real Picard space, without a supplied class/numerical comparison. -/
theorem lineClass_quotient {X : Scheme.{u}} {L M T : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (hT : IsInvertible T)
    (e : L ≅ M ⊗ dualObj T) : lineClass L hL = lineClass M hM - lineClass T hT := by
  rw [lineClass_eq_of_iso hL (tensorInvertible hM hT.dual) e,
    lineClass_tensor M (dualObj T) hM hT.dual, lineClass_dual, sub_eq_add_neg]

end EnvelopeProperty.NativeRealPicard
