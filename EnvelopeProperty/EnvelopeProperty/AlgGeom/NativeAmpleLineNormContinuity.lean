import EnvelopeProperty.AlgGeom.NativeAmpleModelFubiniStudy
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-! # Original geometric ampleness derives true whole-section norm continuity -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Scheme.Modules
open DeJongAlterations
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry NativePulledProjectiveLineFrames
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
open NativeAmpleModelFubiniStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- Actual geometric ampleness internally constructs the WHOLE native homeomorphism
and true weighted norm comparison, deriving continuity for EVERY original datum. -/
theorem FSData.continuous_eval_of_isAmple (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L) {a : ℚ} (D : FSData L a) :
    Continuous (D.eval p hA.isInvertible) := by
  obtain ⟨hL,r,hr,n,f,hf,hfp,⟨e⟩⟩ := hA
  subst p
  let : IsClosedImmersion f := hf
  have hx : f (genericPoint X) ∈ ⨆ i : Fin (n+1),coordinateOpen (R := k) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  let : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i) := ⟨⟨genericPoint X,hi⟩⟩
  let := (f ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  have hc := ((toModelData f i L r e hr D).continuous_eval).comp
    (nativeModelHomeomorph f i).continuous
  exact hc.congr (fun y => (eval_eq_modelEval f i L r e hr hL D y).symm)

end EnvelopeProperty.NativeLineFubiniStudy

namespace EnvelopeProperty.SchemeGlobalSectionNormContinuity
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeModuleIsoGlobalSections NativeLineFubiniStudy
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- EVERY actual whole section of an original geometrically ample line has a
continuous true proper-model norm, including its original zero locus. -/
theorem continuous_of_isAmple (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L) (s : Γ(L,⊤)) :
    Continuous (fun y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p =>
      globalSectionNorm _root_.Valuation.one_apply_le_one y L hA.isInvertible s) := by
  let e : bundleTensorPower L 1 ≅ L := bundleTensorLeftUnitIso L
  let t := (moduleIsoTopEquiv e).symm s
  let D : NativeLineFubiniStudy.FSData L 1 := {
    m := 1
    m_pos := Nat.zero_lt_one
    deg := 1
    deg_eq := by norm_num
    terms := {(t,0)} }
  have he (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
      D.eval p hA.isInvertible y = ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y L hA.isInvertible s : ℝ≥0∞) := by
    have hn := globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible 1) hA.isInvertible e t
    simp only [t,LinearEquiv.apply_symm_apply] at hn
    simp only [NativeLineFubiniStudy.FSData.eval,weightedNormEval,D,Nat.cast_one,inv_one,EReal.coe_one,one_mul,
      Finset.sup_singleton,EReal.coe_zero,add_zero]
    rw [hn]
  have hc : Continuous (fun y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p =>
      ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y L hA.isInvertible s : ℝ≥0∞)) :=
    (D.continuous_eval_of_isAmple p L hA).congr he
  apply ENNReal.continuous_coe_iff.mp
  simpa only [Function.comp_def,ENNReal.exp_log] using ENNReal.continuous_exp.comp hc

end EnvelopeProperty.SchemeGlobalSectionNormContinuity
