import EnvelopeProperty.AlgGeom.NativeAmpleModelFubiniStudy
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionNormDetection

/-! # Genuine whole original FS nonvanishing, independently of a chosen ample model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionNormDetection

private theorem weightedFiniteEval_ne_bot_iff {α : Type*} (m : ℕ) (hm : 0 < m)
    (T : Finset α) (z : α → ℝ≥0) (w : α → ℝ) :
    (((m : ℝ)⁻¹ : ℝ) : EReal)*T.sup (fun q => ENNReal.log (z q : ℝ≥0∞)+(w q : EReal)) ≠ ⊥ ↔
      ∃ q ∈ T,z q ≠ 0 := by
  have hinv : 0 < (m : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hm)
  have hterm (q : α) : ENNReal.log (z q : ℝ≥0∞)+(w q : EReal) ≠ ⊥ ↔ z q ≠ 0 := by
    rw [Ne,EReal.add_eq_bot_iff,not_or,ENNReal.log_eq_bot_iff,ENNReal.coe_eq_zero]
    exact and_iff_left (EReal.coe_ne_bot _)
  constructor
  · intro h
    by_contra hc
    apply h
    have hs : T.sup (fun q => ENNReal.log (z q : ℝ≥0∞)+(w q : EReal)) = ⊥ := by
      rw [Finset.sup_eq_bot_iff]
      intro q hq
      by_contra hz
      exact hc ⟨q,hq,(hterm q).mp hz⟩
    rw [hs]
    exact EReal.coe_mul_bot_of_pos hinv
  · rintro ⟨q,hq,hz⟩
    exact ne_bot_of_le_ne_bot (ProjBerk.ereal_coe_mul_ne_bot hinv.le ((hterm q).mpr hz))
      (ProjBerk.ereal_coe_mul_monotone hinv.le
        (Finset.le_sup (f := fun q => ENNReal.log (z q : ℝ≥0∞)+(w q : EReal)) hq))

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
  (L : X.Modules) (hL : IsInvertible L) {a : ℚ}

/-- Actual original FS functions use finite weighted ENTIRE original global sections, not all zero. -/
def IsFS (a : ℚ) (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  ∃ D : FSData L a,(∃ q ∈ D.terms,q.1 ≠ 0) ∧ ∀ y,φ y = D.eval p hL y

/-- At EVERY native point, the actual original weighted evaluation is not negative
infinity EXACTLY when one actual original section has nonzero TRUE norm there. -/
theorem FSData.eval_ne_bot_iff_exists_norm_ne_zero (D : FSData L a)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    D.eval p hL y ≠ ⊥ ↔ ∃ q ∈ D.terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
      (bundleTensorPower L D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 ≠ 0 :=
  weightedFiniteEval_ne_bot_iff D.m D.m_pos D.terms
    (fun q => globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1) (fun q => q.2)

variable [IsIntegral X]

/-- The actual original finite family is not all zero EXACTLY when its TRUE
weighted evaluation is not negative infinity somewhere on the ENTIRE original native space. -/
theorem FSData.nonzero_iff_exists_eval_ne_bot (D : FSData L a) :
    (∃ q ∈ D.terms,q.1 ≠ 0) ↔
      ∃ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,D.eval p hL y ≠ ⊥ := by
  constructor
  · rintro ⟨q,hq,hq0⟩
    obtain ⟨y,hy⟩ := exists_globalSectionNorm_ne_zero p (bundleTensorPower L D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 hq0
    exact ⟨y,(D.eval_ne_bot_iff_exists_norm_ne_zero p L hL y).mpr ⟨q,hq,hy⟩⟩
  · rintro ⟨y,hy⟩
    obtain ⟨q,hq,hq0⟩ := (D.eval_ne_bot_iff_exists_norm_ne_zero p L hL y).mp hy
    refine ⟨q,hq,fun hz => hq0 ?_⟩
    rw [hz,globalSectionNorm_zero p (bundleTensorPower L D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) y]

/-- Actual original finite rational FS functions are genuine original FS functions,
derived from actual nonvanishing at a true original point, with no nonzero-family premise. -/
theorem IsFinFS.isFS {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFinFS p L hL a φ) : IsFS p L hL a φ := by
  obtain ⟨D,_hD,hNZ,hEq⟩ := hφ
  obtain ⟨q,hq,hq0⟩ := hNZ (trivialPoint p (genericPoint X))
  refine ⟨D,⟨q,hq,fun hz => hq0 ?_⟩,hEq⟩
  rw [hz,globalSectionNorm_zero p (bundleTensorPower L D.deg)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) (trivialPoint p (genericPoint X))]

end EnvelopeProperty.NativeLineFubiniStudy
