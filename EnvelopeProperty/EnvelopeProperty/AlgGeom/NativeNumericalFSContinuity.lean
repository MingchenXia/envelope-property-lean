import EnvelopeProperty.AlgGeom.SchemeGlobalSectionNormContinuity
import EnvelopeProperty.AlgGeom.NativeNumericalCurveWeakPSH

/-! # Genuine varying-line numerical FS continuity and FS inclusion in curve-WEAK psh

The true arbitrary original whole-section norm continuity is geometrically
derived; no norm/model/section/USC or nontriviality comparison certificate.
Paper finite-dimensional topology compatibility and general PSH2 remain open.
-/
open AlgebraicGeometry CategoryTheory Scheme.Modules Topology Filter
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeNumericalFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
private local instance projectiveProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- EVERY actual original rational-line datum has continuous true whole evaluation,
even for zero families, arbitrary real weights and common zeroes. -/
theorem FSData.continuous_eval (D : FSData X) : Continuous (D.eval p) := by
  have hm : (D.m : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.ne_of_gt D.m_pos)
  apply (ProjBerk.continuous_ereal_coe_mul hm).comp
  apply Continuous.finset_sup_apply
  intro q _
  exact (ProjBerk.continuous_ereal_add_coe q.2).comp
    (ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp
      (SchemeGlobalSectionNormContinuity.continuous_globalSectionNorm p D.line D.invertible q.1)))

/-- EVERY actual numerical FS function is continuous on the SAME entire original native space. -/
theorem IsFS.continuous {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsFS p θ φ) : Continuous φ := by
  obtain ⟨D,_,_,he⟩ := h
  exact (D.continuous_eval p).congr (fun y => (he y).symm)

/-- Actual rational numerical FS retains genuine entire original continuity. -/
theorem IsRationalFS.continuous {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsRationalFS p θ φ) : Continuous φ := (h.isFS p).continuous p

/-- Numerical FS genuinely belongs to its actual curve-weak psh class; USC and
nontriviality are derived internally from the actual original data. -/
theorem IsFS.isCurveWeakPSH {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsFS p θ φ) : IsCurveWeakPSH p θ φ := by
  have hfin := h.exists_ne_bot p
  have husc := (h.continuous p).upperSemicontinuous
  obtain ⟨D,hD,rfl,he⟩ := h
  refine ⟨hfin,husc,PUnit, inferInstance,inferInstance,inferInstance,
    (fun _ => D),(fun _ => hD),tendsto_const_nhds,(fun _ => antitone_const),?_⟩
  intro y
  simpa only [iInf_const] using he y

/-- The same true FS inclusion applies to actual original rational weights. -/
theorem IsRationalFS.isCurveWeakPSH {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsRationalFS p θ φ) : IsCurveWeakPSH p θ φ := (h.isFS p).isCurveWeakPSH p

/-- EVERY actual nonzero original datum gives genuine curve-weak numerical psh in
its TRUE original rational-line class, without a supplied FS or USC certificate. -/
theorem FSData.isCurveWeakPSH (D : FSData X) (hD : D.Nonzero) :
    IsCurveWeakPSH p (D.numericalClass p) (D.eval p) :=
  IsFS.isCurveWeakPSH p ⟨D,hD,rfl,(fun _ => rfl)⟩

end EnvelopeProperty.NativeNumericalFubiniStudy
