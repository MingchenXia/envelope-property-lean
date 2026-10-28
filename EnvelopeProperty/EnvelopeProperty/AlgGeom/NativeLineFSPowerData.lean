import EnvelopeProperty.AlgGeom.NativeLineFSIsometries
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorPowerNorms

/-! # Genuine whole original FS data for every positive tensor power of ANY actual original line -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry BundleTensorPowerPullback SchemeModuleIsoGlobalSections
open SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionTensorPowerNorms
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual positive power of EVERY whole original section, in the SAME original power-line module. -/
def powerLineSection (L : X.Modules) (d r : ℕ) (s : Γ(bundleTensorPower L d,⊤)) :
    Γ(bundleTensorPower (bundleTensorPower L r) d,⊤) :=
  moduleIsoTopEquiv
    ((eqToIso (congrArg (bundleTensorPower L) (Nat.mul_comm d r))) ≪≫ (powerMulIso L r d).symm)
    (blockPowerSection L d s r)

variable (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L)

theorem powerLineSection_norm (d r : ℕ) (s : Γ(bundleTensorPower L d,⊤))
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower (bundleTensorPower L r) d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) d) (powerLineSection L d r s) =
      globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L d)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) s ^ r := by
  unfold powerLineSection
  rw [← globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (d*r))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) d)
    ((eqToIso (congrArg (bundleTensorPower L) (Nat.mul_comm d r))) ≪≫ (powerMulIso L r d).symm)]
  exact globalSectionNorm_blockPowerSection _root_.Valuation.one_apply_le_one y L hL d s r

/-- EVERY true original whole-section FS family gives actual original power-line FS data,
with positive denominator multiplied by r, real weights multiplied by r, and coefficient divided by r. -/
def FSData.toPowerLine {a : ℚ} (D : FSData L a) (r : ℕ) (hr : 0 < r) :
    FSData (bundleTensorPower L r) (a/(r : ℚ)) where
  m := D.m*r
  m_pos := Nat.mul_pos D.m_pos hr
  deg := D.deg
  deg_eq := by rw [D.deg_eq,Nat.cast_mul];field_simp [Nat.ne_of_gt hr]
  terms := D.terms.image fun q => (powerLineSection L D.deg r q.1,(r : ℝ)*q.2)

/-- ENTIRE original weighted evaluations are unchanged by the actual section-power construction. -/
theorem FSData.toPowerLine_eval {a : ℚ} (D : FSData L a) (r : ℕ) (hr : 0 < r)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.toPowerLine L r hr).eval p (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) y =
      D.eval p hL y := by
  have hs : (D.toPowerLine L r hr).terms.sup (fun q => ENNReal.log
      (globalSectionNorm _root_.Valuation.one_apply_le_one y
        (bundleTensorPower (bundleTensorPower L r) (D.toPowerLine L r hr).deg)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (D.toPowerLine L r hr).deg) q.1 : ℝ≥0∞)+(q.2 : EReal)) =
      ((r : ℝ) : EReal)*D.terms.sup (fun q => ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L D.deg)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 : ℝ≥0∞)+(q.2 : EReal)) := by
    change (D.terms.image _).sup _ = _
    rw [Finset.sup_image,ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast hr)]
    apply Finset.sup_congr rfl
    intro q hq
    change ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y
      (bundleTensorPower (bundleTensorPower L r) D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) D.deg)
      (powerLineSection L D.deg r q.1) : ℝ≥0∞)+(((r : ℝ)*q.2 : ℝ) : EReal) =
        ((r : ℝ) : EReal)*(ENNReal.log
          (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L D.deg)
            (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 : ℝ≥0∞)+(q.2 : EReal))
    rw [powerLineSection_norm p L hL,ENNReal.coe_pow,ENNReal.log_pow,
      ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg r),EReal.coe_mul]
    rfl
  change ((((D.m*r : ℕ) : ℝ)⁻¹ : ℝ) : EReal)*(D.toPowerLine L r hr).terms.sup _ =
    (((D.m : ℝ)⁻¹ : ℝ) : EReal)*D.terms.sup _
  rw [hs,ProjBerk.ereal_coe_mul_coe_mul]
  have he : ((D.m*r : ℕ) : ℝ)⁻¹*(r : ℝ) = (D.m : ℝ)⁻¹ := by
    rw [Nat.cast_mul,mul_inv_rev];field_simp [Nat.ne_of_gt hr]
  rw [he]

/-- Original rational weights remain rational under actual original positive section powers. -/
theorem FSData.IsRational.toPowerLine {a : ℚ} {D : FSData L a}
    (hD : D.IsRational) (r : ℕ) (hr : 0 < r) : (D.toPowerLine L r hr).IsRational := by
  intro q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb⟩ := hD t ht
  exact ⟨(r : ℚ)*b,by simp only [hb,Rat.cast_mul,Rat.cast_natCast]⟩

/-- EVERY actual whole power-line FS family is realized by true whole original line sections,
with SAME denominator/weights and original coefficient multiplied by r. -/
def FSData.fromPowerLine (r : ℕ) {b : ℚ} (D : FSData (bundleTensorPower L r) b) :
    FSData L ((r : ℚ)*b) where
  m := D.m
  m_pos := D.m_pos
  deg := r*D.deg
  deg_eq := by rw [Nat.cast_mul,D.deg_eq];ring
  terms := D.terms.image fun q => (moduleIsoTopEquiv (powerMulIso L r D.deg) q.1,q.2)

/-- EVERY actual whole power-line family retains its TRUE original entire evaluation on realization. -/
theorem FSData.fromPowerLine_eval (r : ℕ) {b : ℚ} (D : FSData (bundleTensorPower L r) b)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.fromPowerLine L r).eval p hL y =
      D.eval p (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) y := by
  exact (weightedNormEval_moduleIso _root_.Valuation.one_apply_le_one y D.m
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) D.deg)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (r*D.deg))
    (powerMulIso L r D.deg) D.terms).symm

/-- Original power-line realization retains the actual unchanged rational weights. -/
theorem FSData.IsRational.fromPowerLine (r : ℕ) {b : ℚ}
    {D : FSData (bundleTensorPower L r) b} (hD : D.IsRational) :
    (D.fromPowerLine L r).IsRational := by
  intro q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  exact hD t ht
end EnvelopeProperty.NativeLineFubiniStudy
