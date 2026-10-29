import EnvelopeProperty.AlgGeom.NativeAmpleModelPoweredSections
import EnvelopeProperty.Global.ModelPSH

/-! # Actual finite weighted whole-section FS families of an arbitrary original ample line -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open Alterations Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Independent finite FS data made of ENTIRE actual original tensor-power global sections. -/
structure FSData (L : X.Modules) (a : ℚ) where
  m : ℕ
  m_pos : 0 < m
  deg : ℕ
  deg_eq : (deg : ℚ) = m * a
  terms : Finset (Γ(bundleTensorPower L deg,⊤) × ℝ)

/-- Actual entire weighted evaluation using TRUE original proper-model line norms. -/
def FSData.eval {L : X.Modules} {a : ℚ} (D : FSData L a)
    (p : X ⟶ Spec (.of k)) [IsProper p] (hL : IsInvertible L)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) : EReal :=
  weightedNormEval _root_.Valuation.one_apply_le_one y D.m (bundleTensorPower L D.deg)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) D.terms

/-- Rationality of the literal original finite weights. -/
def FSData.IsRational {L : X.Modules} {a : ℚ} (D : FSData L a) : Prop :=
  ∀ q ∈ D.terms,∃ b : ℚ,q.2 = b

/-- Finite rational FS functions of the ACTUAL original line: original rational
weights and genuine original section norms with no common zero on the WHOLE native point space. -/
def IsFinFS (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L) (a : ℚ)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  ∃ D : FSData L a,D.IsRational ∧
    (∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,
      ∃ q ∈ D.terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
      (bundleTensorPower L D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 ≠ 0) ∧
    ∀ y,φ y = D.eval p hL y

end EnvelopeProperty.NativeLineFubiniStudy

namespace EnvelopeProperty.NativeAmpleModelFubiniStudy
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry NativeLineFubiniStudy
open NativePulledProjectiveLineFrames NativeAmpleModelPoweredSections
open SchemeGlobalSectionModelNormIsometries
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1))
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  (L : X.Modules) (r : ℕ) (e : line f (0 : Fin (m + 1)) 1 ≅ bundleTensorPower L r)

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- Actual original section powers, reciprocal denominator and unchanged normalized
function give genuine model FS data in the exact original class a/r. -/
def toModelData (hr : 0 < r) {a : ℚ} (D : NativeLineFubiniStudy.FSData L a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).FSData (fun _ => a / (r : ℚ)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  refine {
    m := D.m*r
    m_pos := Nat.mul_pos D.m_pos hr
    deg := fun _ => (D.deg : ℤ)
    deg_eq := ?_
    terms := D.terms.image (fun q => ((poweredSection f i L r e D.deg q.1 : X.functionField),(r : ℝ)*q.2))
    mem_sections := ?_ }
  · intro c
    rw [Int.cast_natCast,D.deg_eq,Nat.cast_mul]
    field_simp [Nat.ne_of_gt hr]
  · intro q hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact (poweredSection f i L r e D.deg t.1).property

/-- EVERY original finite weighted family retains its ENTIRE true original
function under the SAME native homeomorphism, including all zero sections and norms. -/
theorem eval_eq_modelEval (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    (D : NativeLineFubiniStudy.FSData L a)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    D.eval (f ≫ projectiveSpaceStructure k m) hL y =
      (toModelData f i L r e hr D).eval (nativeModelHomeomorph f i y) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have hsup : (toModelData f i L r e hr D).terms.sup
      (fun q => (fullFieldModel f i).termVal (fun _ => (D.deg : ℤ)) q (nativeModelHomeomorph f i y)) =
        ((r : ℝ) : EReal) * D.terms.sup (fun q =>
          ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L D.deg)
            (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 : ℝ≥0∞) + (q.2 : EReal)) := by
    rw [ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast hr)]
    change (D.terms.image _).sup _ = _
    rw [Finset.sup_image]
    apply Finset.sup_congr rfl
    intro q hq
    change (fullFieldModel f i).logSecAbs (nativeModelHomeomorph f i y).1
        (fun _ => (D.deg : ℤ)) (poweredSection f i L r e D.deg q.1) +
          (((r : ℝ)*q.2 : ℝ) : EReal) = _
    rw [poweredSection_logNorm f i L r e hL D.deg q.1 y,
      ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg r),EReal.coe_mul]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup _ =
    ((((D.m*r : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      (toModelData f i L r e hr D).terms.sup
        (fun q => (fullFieldModel f i).termVal (fun _ => (D.deg : ℤ)) q (nativeModelHomeomorph f i y))
  rw [hsup,ProjBerk.ereal_coe_mul_coe_mul]
  have hc : (((D.m*r : ℕ) : ℝ)⁻¹ : ℝ) * (r : ℝ) = (D.m : ℝ)⁻¹ := by
    rw [Nat.cast_mul,mul_inv_rev]
    field_simp [Nat.ne_of_gt hr]
  rw [hc]

/-- Actual rational weights remain rational under genuine original integer exponent scaling. -/
theorem toModelData_isRational (hr : 0 < r) {a : ℚ}
    (D : NativeLineFubiniStudy.FSData L a) (hD : D.IsRational) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (toModelData f i L r e hr D).IsRational := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ q ∈ (toModelData f i L r e hr D).terms,∃ b : ℚ,q.2 = b
  intro q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb⟩ := hD t ht
  refine ⟨(r : ℚ)*b,?_⟩
  simpa only [Rat.cast_mul,Rat.cast_natCast] using congrArg (fun z : ℝ => (r : ℝ)*z) hb

/-- Positive actual original section powers retain EXACTLY the true no-common-zero
condition on BOTH ENTIRE native point spaces. -/
theorem toModelData_noCommonZero_iff (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    (D : NativeLineFubiniStudy.FSData L a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (∀ v : (fullFieldModel f i).an,∃ q ∈ (toModelData f i L r e hr D).terms,
      (fullFieldModel f i).secAbs v.1 (fun _ => (D.deg : ℤ)) q.1 ≠ 0) ↔
    (∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m),
      ∃ q ∈ D.terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
      (bundleTensorPower L D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 ≠ 0) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · intro h y
    obtain ⟨q,hq,hq0⟩ := h (nativeModelHomeomorph f i y)
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨t,ht,(poweredSection_norm_ne_zero_iff f i L r e hr hL D.deg t.1 y).mp hq0⟩
  · intro h v
    obtain ⟨y,rfl⟩ := (nativeModelHomeomorph f i).surjective v
    obtain ⟨t,ht,ht0⟩ := h y
    exact ⟨_,Finset.mem_image.mpr ⟨t,ht,rfl⟩,
      (poweredSection_norm_ne_zero_iff f i L r e hr hL D.deg t.1 y).mpr ht0⟩

include e in
/-- Genuine original finite rational FS functions of the original ample line
transport to genuine finite model FS functions of the exact class a/r. -/
theorem isFinFS_transport (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hφ : NativeLineFubiniStudy.IsFinFS (f ≫ projectiveSpaceStructure k m) L hL a φ) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).IsFinFS (fun _ => a/(r : ℚ))
      (fun v => φ ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  obtain ⟨D,hD,hNZ,hEq⟩ := hφ
  refine ⟨toModelData f i L r e hr D,toModelData_isRational f i L r e hr D hD,
    (toModelData_noCommonZero_iff f i L r e hr hL D).mpr hNZ,?_⟩
  intro v
  change φ ((nativeModelHomeomorph f i).symm v) = (toModelData f i L r e hr D).eval v
  rw [hEq,eval_eq_modelEval f i L r e hr hL D,Homeomorph.apply_symm_apply]

end EnvelopeProperty.NativeAmpleModelFubiniStudy
