import EnvelopeProperty.AlgGeom.NativeLineFubiniStudyNonvanishing
import EnvelopeProperty.AlgGeom.NativeAmpleModelFSRealization

/-! # Entire genuine original FS comparison for an arbitrary actual ample line -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open Alterations Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeAmpleModelFubiniStudyComparison
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry NativeLineFubiniStudy
open NativePulledProjectiveLineFrames NativeAmpleModelPoweredSections NativeAmpleModelFubiniStudy
open NativeAmpleModelFSRealization SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionNormDetection
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m+1))
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  (L : X.Modules) (r : ℕ) (e : line f (0 : Fin (m+1)) 1 ≅ bundleTensorPower L r)

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- Genuine actual positive original section powers are zero EXACTLY when the
SAME actual original global section is zero; no nonvanishing certificate is supplied. -/
theorem poweredSection_eq_zero_iff (hr : 0 < r) (hL : IsInvertible L) (d : ℕ)
    (s : Γ(bundleTensorPower L d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (poweredSection f i L r e d s : X.functionField) = 0 ↔ s = 0 := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · intro hs
    by_contra h0
    obtain ⟨y,hy⟩ := exists_globalSectionNorm_ne_zero (f ≫ projectiveSpaceStructure k m)
      (bundleTensorPower L d) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) s h0
    have hn := poweredSection_norm f i L r e hL d s y
    rw [hs,MultiModel.secAbs_zero] at hn
    exact (pow_ne_zero r hy) hn.symm
  · intro hs
    subst s
    by_contra h0
    let y := (nativeModelHomeomorph f i).symm (fullFieldModel f i).triv
    have hn := poweredSection_norm f i L r e hL d 0 y
    rw [globalSectionNorm_zero (f ≫ projectiveSpaceStructure k m) (bundleTensorPower L d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) y] at hn
    have ht := (fullFieldModel f i).secAbs_triv (poweredSection f i L r e d 0).property h0
    have hz : (fullFieldModel f i).secAbs (fullFieldModel f i).triv.1 (fun _ => (d : ℤ))
        (poweredSection f i L r e d 0) = 0 := by
      simpa only [y,Homeomorph.apply_symm_apply,zero_pow (Nat.ne_of_gt hr)] using hn
    exact one_ne_zero (ht.symm.trans hz)

/-- Actual original whole-section nonzero finite families correspond EXACTLY to
the true powered coefficient families, including families with common zeroes. -/
theorem toModelData_nonzero_iff (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    (D : NativeLineFubiniStudy.FSData L a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (∃ q ∈ (toModelData f i L r e hr D).terms,q.1 ≠ 0) ↔ (∃ q ∈ D.terms,q.1 ≠ 0) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · rintro ⟨q,hq,hq0⟩
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨t,ht,fun hz => hq0 ((poweredSection_eq_zero_iff f i L r e hr hL D.deg t.1).mpr hz)⟩
  · rintro ⟨q,hq,hq0⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,
      fun hz => hq0 ((poweredSection_eq_zero_iff f i L r e hr hL D.deg q.1).mp hz)⟩

include e in
/-- EVERY actual original FS function, including genuine common-zero families,
transports to true model FS of class a/r under the SAME entire homeomorphism. -/
theorem isFS_transport (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hφ : NativeLineFubiniStudy.IsFS (f ≫ projectiveSpaceStructure k m) L hL a φ) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).IsFS (fun _ => a/(r : ℚ)) (fun v => φ ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  obtain ⟨D,hNZ,hEq⟩ := hφ
  refine ⟨toModelData f i L r e hr D,(toModelData_nonzero_iff f i L r e hr hL D).mpr hNZ,?_⟩
  intro v
  change φ ((nativeModelHomeomorph f i).symm v) = (toModelData f i L r e hr D).eval v
  rw [hEq,eval_eq_modelEval f i L r e hr hL D,Homeomorph.apply_symm_apply]

/-- Actual ENTIRE section realization of every true nonzero model family is itself
not all zero, derived from genuine original norm detection and the whole evaluation identity. -/
theorem ofModelData_nonzero (hr : 0 < r) (hL : IsInvertible L) {a : ℚ} (ha : 0 ≤ a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),(∃ q ∈ D.terms,q.1 ≠ 0) →
      ∃ q ∈ (ofModelData f i L r e hr ha D).terms,q.1 ≠ 0 := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),(∃ q ∈ D.terms,q.1 ≠ 0) → _
  intro D hD
  apply (NativeLineFubiniStudy.FSData.nonzero_iff_exists_eval_ne_bot
    (f ≫ projectiveSpaceStructure k m) L hL (ofModelData f i L r e hr ha D)).mpr
  refine ⟨(nativeModelHomeomorph f i).symm (fullFieldModel f i).triv,?_⟩
  rw [ofModelData_eval f i L r e hr ha hL,Homeomorph.apply_symm_apply]
  exact D.eval_triv_ne_bot_iff.mpr hD

include e in
/-- EVERY nonnegative actual original ample-line rational FS class agrees EXACTLY
with genuine model FS class a/r, on the ENTIRE same original native point space. -/
theorem isFS_iff (hr : 0 < r) (hL : IsInvertible L) {a : ℚ} (ha : 0 ≤ a)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    NativeLineFubiniStudy.IsFS (f ≫ projectiveSpaceStructure k m) L hL a φ ↔
      (fullFieldModel f i).IsFS (fun _ => a/(r : ℚ)) (fun v => φ ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · exact isFS_transport f i L r e hr hL
  · rintro ⟨D,hNZ,hEq⟩
    refine ⟨ofModelData f i L r e hr ha D,ofModelData_nonzero f i L r e hr hL ha D hNZ,?_⟩
    intro y
    have hy : φ y = D.eval (nativeModelHomeomorph f i y) := by
      simpa only [Homeomorph.symm_apply_apply] using hEq (nativeModelHomeomorph f i y)
    exact hy.trans (ofModelData_eval f i L r e hr ha hL D y).symm

include i e in
/-- EVERY actual original whole-section FS function is continuous on the ENTIRE
native space, with true original model norms and no common-zero exclusion. -/
theorem isFS_continuous (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hφ : NativeLineFubiniStudy.IsFS (f ≫ projectiveSpaceStructure k m) L hL a φ) : Continuous φ := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have hh := (isFS_transport f i L r e hr hL hφ).continuous.comp (nativeModelHomeomorph f i).continuous
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh

end EnvelopeProperty.NativeAmpleModelFubiniStudyComparison
