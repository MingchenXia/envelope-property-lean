import EnvelopeProperty.AlgGeom.NativeNumericalCurveTopology
import EnvelopeProperty.AlgGeom.NativeNumericalFubiniStudy
import EnvelopeProperty.AlgGeom.NativeAmpleModelPSHComparison

/-! # Actual varying original-line psh nets in the curve-WEAK numerical topology

This uses the SAME actual curve-degree quotient and genuinely varying
original rational-line data. Finite-dimensional Euclidean compatibility,
general original/model PSH comparison and ample regularization remain open.
The distinct older fixed-L-ray predicate is only mapped INTO this class.
-/
open AlgebraicGeometry CategoryTheory Scheme.Modules Filter Topology
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeNumericalFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Scheme.{u}}

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- True original whole section norms are finite; hence every actual weighted FS value avoids positive infinity. -/
theorem FSData.eval_ne_top (D : FSData X) (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) : D.eval p y ≠ ⊤ := by
  apply ProjBerk.ereal_coe_mul_ne_top (inv_nonneg.mpr (Nat.cast_nonneg D.m))
  apply lt_top_iff_ne_top.mp
  apply (Finset.sup_lt_iff bot_lt_top).mpr
  intro q _
  apply lt_top_iff_ne_top.mpr
  apply EReal.add_ne_top _ (EReal.coe_ne_top q.2)
  rw [Ne,ENNReal.log_eq_top_iff]
  exact ENNReal.coe_ne_top

variable (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- BJ-shaped actual varying-original-line psh nets with EXPLICIT curve-WEAK numerical convergence.
Agreement with the paper's finite-dimensional topology is NOT assumed or asserted. -/
def IsCurveWeakPSH [IsIntegral X] (θ : NativeRealNumericalClasses.Space p)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  (∃ y,φ y ≠ ⊥) ∧ UpperSemicontinuous φ ∧
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (D : J → FSData X), (∀ j,(D j).Nonzero) ∧
      Tendsto (fun j => (D j).numericalClass p) atTop (𝓝 θ) ∧
      (∀ y,Antitone fun j => (D j).eval p y) ∧ ∀ y,φ y = ⨅ j,(D j).eval p y

variable [IsIntegral X]

/-- Genuine generic finiteness is retained in the actual numerical psh definition. -/
theorem IsCurveWeakPSH.exists_ne_bot {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsCurveWeakPSH p θ φ) : ∃ y,φ y ≠ ⊥ := h.1

/-- Upper semicontinuity is on the SAME entire actual original native point space. -/
theorem IsCurveWeakPSH.upperSemicontinuous {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsCurveWeakPSH p θ φ) : UpperSemicontinuous φ := h.2.1

/-- Positive infinity is excluded internally by actual whole-FS bounds and nonempty original nets. -/
theorem IsCurveWeakPSH.ne_top {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsCurveWeakPSH p θ φ) (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    φ y ≠ ⊤ := by
  obtain ⟨_,_,J,hJ,_,hN,D,_,_,_,he⟩ := h
  let := hJ
  let := hN
  let j : J := Classical.choice hN
  rw [he y]
  exact ne_top_of_le_ne_top ((D j).eval_ne_top p y) (iInf_le _ j)

/-- Actual class convergence can equivalently be tested by EVERY true full-Euler original curve degree. -/
theorem isCurveWeakPSH_iff_degreewise (θ : NativeRealNumericalClasses.Space p)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsCurveWeakPSH p θ φ ↔
      (∃ y,φ y ≠ ⊥) ∧ UpperSemicontinuous φ ∧
      ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
        (D : J → FSData X), (∀ j,(D j).Nonzero) ∧
        (∀ C : NativeClosedCurveDegrees.ClosedIntegralCurve X,
          Tendsto (fun j => NativeRealNumericalClasses.curveDegree p C ((D j).numericalClass p))
            atTop (𝓝 (NativeRealNumericalClasses.curveDegree p C θ))) ∧
        (∀ y,Antitone fun j => (D j).eval p y) ∧ ∀ y,φ y = ⨅ j,(D j).eval p y := by
  simp only [IsCurveWeakPSH,NativeRealNumericalClasses.tendsto_iff_curveDegree]

/-- EVERY original fixed-L-ray psh net maps to the SAME function in its genuine curve-weak numerical class. -/
theorem isCurveWeakPSH_of_ray (L : X.Modules) (hL : IsInvertible L) {a : ℝ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : NativeLineFubiniStudy.IsPSH p L hL a φ) :
    IsCurveWeakPSH p (a • NativeRealNumericalClasses.lineClass p L hL) φ := by
  obtain ⟨hfin,husc,J,hJ,hdir,hN,b,v,hv,hb,hanti,he⟩ := h
  let := hJ
  let := hdir
  let := hN
  choose D hD hEval using hv
  refine ⟨hfin,husc,J,hJ,hdir,hN,(fun j => FSData.ofRay L hL (D j)),hD,?_,?_,?_⟩
  · simpa only [FSData.ofRay_numericalClass] using
      hb.smul_const (NativeRealNumericalClasses.lineClass p L hL)
  · intro y i j hij
    simpa only [FSData.ofRay_eval,← hEval] using hanti y hij
  · intro y
    simpa only [FSData.ofRay_eval,← hEval] using he y

/-- Actual whole closed-curve degree equality identifies genuine numerical psh target classes.
This is NOT arbitrary-line invariance of the different fixed-ray predicate. -/
theorem isCurveWeakPSH_iff_of_curveDegrees_eq (θ η : NativeRealNumericalClasses.Space p)
    (h : ∀ C : NativeClosedCurveDegrees.ClosedIntegralCurve X,
      NativeRealNumericalClasses.curveDegree p C θ = NativeRealNumericalClasses.curveDegree p C η)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsCurveWeakPSH p θ φ ↔ IsCurveWeakPSH p η φ := by
  rw [NativeRealNumericalClasses.ext p θ η h]

end EnvelopeProperty.NativeNumericalFubiniStudy
