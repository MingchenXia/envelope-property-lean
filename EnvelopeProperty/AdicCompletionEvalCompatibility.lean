/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Actual original quotient compatibility of the genuine adic completion evaluations -/
noncomputable section
namespace EnvelopeProperty.AdicCompletionEvalCompatibility
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- EVERY genuine completion coordinate obeys the ORIGINAL quotient factor, including order zero. -/
theorem factorPow_eval {n m : ℕ} (h : n≤m) (a : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I m a)=AdicCompletion.evalₐ I n a := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I a (le_of_eq (Ideal.mul_top _)),
    ← AdicCompletion.factor_eval_eq_evalₐ I a (le_of_eq (Ideal.mul_top _))]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
    (Submodule.factor (le_of_eq (Ideal.mul_top (I^m))) (a.val m))=
      Submodule.factor (le_of_eq (Ideal.mul_top (I^n))) (a.val n)
  rw [← a.property h]
  induction a.val m using Quotient.inductionOn' with
  | _ x => rfl

/-- The ENTIRE original quotient factor square commutes as actual RingHoms. -/
theorem factorPow_comp_eval {n m : ℕ} (h : n≤m) :
    (Ideal.Quotient.factorPow I h).comp (AdicCompletion.evalₐ I m).toRingHom=
      (AdicCompletion.evalₐ I n).toRingHom := by
  ext a
  exact factorPow_eval I h a

end EnvelopeProperty.AdicCompletionEvalCompatibility
