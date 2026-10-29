import EnvelopeProperty.AlgGeom.NativeNumericalAmpleDomination
import EnvelopeProperty.AlgGeom.NativeLineFubiniStudyNonvanishing

/-! # Actual varying original rational-line FS data and their genuine numerical classes

Every datum carries an ACTUAL original invertible module and ENTIRE global
sections. The original line can vary. This does not assert arbitrary
numerical invariance of the older fixed-line FS/ray predicates.
-/
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeNumericalFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeGlobalSectionNormDetection
variable {k : Type u} [Field k] {X : Scheme.{u}}

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Actual whole original rational-line data M/m, with finite REAL weighted sections. -/
structure FSData (X : Scheme.{u}) where
  line : X.Modules
  invertible : IsInvertible line
  m : ℕ
  m_pos : 0 < m
  terms : Finset (Γ(line,⊤) × ℝ)

/-- The true original numerical class of the ACTUAL rational line M/m. -/
def FSData.numericalClass (D : FSData X) (p : X ⟶ Spec (.of k)) [IsProjective p] :
    NativeRealNumericalClasses.Space p :=
  (D.m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p D.line D.invertible

/-- Whole evaluation by true original proper-model norms at the SAME original native points. -/
def FSData.eval (D : FSData X) (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) : EReal :=
  weightedNormEval _root_.Valuation.one_apply_le_one y D.m D.line D.invertible D.terms

/-- Actual original sections are not all zero; common zeroes remain allowed. -/
def FSData.Nonzero (D : FSData X) : Prop := ∃ q ∈ D.terms, q.1 ≠ 0

/-- Rationality is a property of the ACTUAL finite weights, independent of their true evaluation. -/
def FSData.IsRational (D : FSData X) : Prop := ∀ q ∈ D.terms, ∃ a : ℚ, q.2 = a

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

/-- At EVERY actual native point, genuine FS nontriviality is detected by true original section norms. -/
theorem FSData.eval_ne_bot_iff (D : FSData X) (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    D.eval p y ≠ ⊥ ↔ ∃ q ∈ D.terms,
      globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1 ≠ 0 :=
  weightedFiniteEval_ne_bot_iff D.m D.m_pos D.terms
    (fun q => globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1) (fun q => q.2)

/-- On an integral actual original scheme, actual nonzero data is EXACTLY genuine generic finiteness. -/
theorem FSData.nonzero_iff_exists_eval_ne_bot [IsIntegral X] (D : FSData X)
    (p : X ⟶ Spec (.of k)) [IsProper p] :
    D.Nonzero ↔ ∃ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p, D.eval p y ≠ ⊥ := by
  constructor
  · rintro ⟨q,hq,hq0⟩
    obtain ⟨y,hy⟩ := exists_globalSectionNorm_ne_zero p D.line D.invertible q.1 hq0
    exact ⟨y,(D.eval_ne_bot_iff p y).mpr ⟨q,hq,hy⟩⟩
  · rintro ⟨y,hy⟩
    obtain ⟨q,hq,hq0⟩ := (D.eval_ne_bot_iff p y).mp hy
    refine ⟨q,hq,fun hz => hq0 ?_⟩
    rw [hz,globalSectionNorm_zero p D.line D.invertible y]

/-- Numerical FS uses ACTUAL varying original rational lines and entire original norms. -/
def IsFS (p : X ⟶ Spec (.of k)) [IsProjective p] (θ : NativeRealNumericalClasses.Space p)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  ∃ D : FSData X, D.Nonzero ∧ D.numericalClass p = θ ∧ ∀ y, φ y = D.eval p y

/-- Actual rational weights form a separately specified subcollection of the SAME numerical FS data. -/
def IsRationalFS (p : X ⟶ Spec (.of k)) [IsProjective p] (θ : NativeRealNumericalClasses.Space p)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  ∃ D : FSData X, D.IsRational ∧ D.Nonzero ∧ D.numericalClass p = θ ∧ ∀ y, φ y = D.eval p y

/-- Numerical FS's actual defining family internally derives generic finiteness. -/
theorem IsFS.exists_ne_bot [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal} (h : IsFS p θ φ) :
    ∃ y, φ y ≠ ⊥ := by
  obtain ⟨D,hD,_,he⟩ := h
  obtain ⟨y,hy⟩ := (D.nonzero_iff_exists_eval_ne_bot p).mp hD
  exact ⟨y,by rw [he]; exact hy⟩

/-- Forgetting actual rationality retains the SAME line, true class, whole sections and evaluation. -/
theorem IsRationalFS.isFS (p : X ⟶ Spec (.of k)) [IsProjective p]
    {θ : NativeRealNumericalClasses.Space p}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal} (h : IsRationalFS p θ φ) :
    IsFS p θ φ := by
  obtain ⟨D,_,hD,hθ,he⟩ := h
  exact ⟨D,hD,hθ,he⟩

/-- Keep the literal whole power line, all original sections, denominator and weights of ANY ray datum. -/
def FSData.ofRay (L : X.Modules) (hL : IsInvertible L) {a : ℚ}
    (D : NativeLineFubiniStudy.FSData L a) : FSData X where
  line := bundleTensorPower L D.deg
  invertible := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg
  m := D.m
  m_pos := D.m_pos
  terms := D.terms

/-- Every ray datum's ENTIRE true original function is literally retained. -/
theorem FSData.ofRay_eval (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) (hL : IsInvertible L) {a : ℚ} (D : NativeLineFubiniStudy.FSData L a)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (FSData.ofRay L hL D).eval p y = D.eval p hL y := rfl

/-- Actual tensor-power classes and the original degree equation derive the TRUE numerical ray class. -/
theorem FSData.ofRay_numericalClass (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) {a : ℚ} (D : NativeLineFubiniStudy.FSData L a) :
    (FSData.ofRay L hL D).numericalClass p = (a : ℝ) • NativeRealNumericalClasses.lineClass p L hL := by
  change (D.m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p (bundleTensorPower L D.deg) _ = _
  rw [NativeRealNumericalClasses.lineClass_tensorPower,smul_smul]
  have hd : (D.deg : ℝ) = (D.m : ℝ) * (a : ℝ) := by exact_mod_cast D.deg_eq
  rw [hd,inv_mul_cancel_left₀ (by exact_mod_cast Nat.ne_of_gt D.m_pos)]

/-- Existing fixed-line FS embeds into genuine varying-line numerical FS with its ACTUAL class. -/
theorem isFS_of_ray (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : NativeLineFubiniStudy.IsFS p L hL a φ) :
    IsFS p ((a : ℝ) • NativeRealNumericalClasses.lineClass p L hL) φ := by
  obtain ⟨D,hD,he⟩ := h
  exact ⟨FSData.ofRay L hL D,hD,FSData.ofRay_numericalClass p L hL D,he⟩

end EnvelopeProperty.NativeNumericalFubiniStudy
