/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ValuationCompletion

/-! # Genuine isometric completion of an original valuation-preserving field equivalence -/
open scoped NNReal
noncomputable section
namespace EnvelopeProperty.Valuation
variable {K L : Type*} [Field K] [Field L]
variable (v : _root_.Valuation K ℝ≥0) (w : _root_.Valuation L ℝ≥0)
  (e : K ≃+* L) (he : ∀ a, w (e a) = v a)

include he in
private theorem norm_withAbsCongr (a : WithAbs (toRealAbs v)) :
    ‖WithAbs.congr (toRealAbs v) (toRealAbs w) e a‖ = ‖a‖ :=
  congrArg ((↑) : ℝ≥0 → ℝ) (he a.ofAbs)

include he in
private theorem norm_withAbsCongr_symm (a : WithAbs (toRealAbs w)) :
    ‖(WithAbs.congr (toRealAbs v) (toRealAbs w) e).symm a‖ = ‖a‖ := by
  change (v (e.symm a.ofAbs) : ℝ) = (w a.ofAbs : ℝ)
  rw [← he, RingEquiv.apply_symm_apply]

/-- The ACTUAL field equivalence extends to both genuine completions, preserving whole residue elements. -/
def completionCongr : (toRealAbs v).Completion ≃+* (toRealAbs w).Completion :=
  UniformSpace.Completion.mapRingEquiv (WithAbs.congr (toRealAbs v) (toRealAbs w) e)
    (AddMonoidHomClass.isometry_of_norm _ (norm_withAbsCongr v w e he)).continuous
    (AddMonoidHomClass.isometry_of_norm _ (norm_withAbsCongr_symm v w e he)).continuous

/-- Every ORIGINAL completed-field norm is retained by the actual completion equivalence. -/
theorem norm_completionCongr (a : (toRealAbs v).Completion) :
    ‖completionCongr v w e he a‖ = ‖a‖ :=
  EnvelopeProperty.UniformSpace.Completion.norm_mapRingHom
    (WithAbs.congr (toRealAbs v) (toRealAbs w) e).toRingHom (norm_withAbsCongr v w e he) a

/-- Every original residue element follows the SAME actual field equivalence. -/
theorem completionCongr_coe (a : K) :
    completionCongr v w e he (WithAbs.toAbs (toRealAbs v) a) =
      (WithAbs.toAbs (toRealAbs w) (e a) : (toRealAbs w).Completion) :=
  UniformSpace.Completion.mapRingHom_coe
    (AddMonoidHomClass.isometry_of_norm _ (norm_withAbsCongr v w e he)).continuous
    (WithAbs.toAbs (toRealAbs v) a)

/-- The entire actual completed-field equivalence is isometric. -/
theorem isometry_completionCongr : Isometry (completionCongr v w e he) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_completionCongr v w e he)

end EnvelopeProperty.Valuation
