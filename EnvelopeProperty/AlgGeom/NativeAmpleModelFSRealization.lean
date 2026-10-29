import EnvelopeProperty.AlgGeom.NativeAmpleModelFubiniStudy

/-! # EVERY genuine finite model FS family lifts through actual original ample-line exponent blocks -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open Alterations Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeAmpleModelFSRealization
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry NativeLineFubiniStudy
open NativePulledProjectiveLineFrames NativeAmpleModelSectionBlocks NativeAmpleModelFubiniStudy
open SchemeGlobalSectionModelNormIsometries
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem realSupAttach {α : Type*} (T : Finset α) (F : α → EReal) :
    T.attach.sup (fun q => F q.val) = T.sup F :=
  Finset.sup_attach T F

variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1))
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  (L : X.Modules) (r : ℕ) (e : line f (0 : Fin (m + 1)) 1 ≅ bundleTensorPower L r)
  {a : ℚ}

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

private theorem degree_eq_nat (hr : 0 < r) (ha : 0 ≤ a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),∀ c,
      ((D.deg 0).toNat : ℤ) = D.deg c := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),∀ c,
    ((D.deg 0).toNat : ℤ) = D.deg c
  intro D c
  have hn : 0 ≤ D.deg 0 := by
    have h := D.deg_eq 0
    have hp : (0 : ℚ) ≤ D.m * (a/(r : ℚ)) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg ha (Nat.cast_pos.mpr hr).le)
    rw [← h] at hp
    exact_mod_cast hp
  have hc : c = 0 := Subsingleton.elim c 0
  subst c
  exact Int.toNat_of_nonneg hn

private def realizedSection (hr : 0 < r) (ha : 0 ≤ a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) →
    {q // q ∈ D.terms} → Γ(bundleTensorPower L (r*(D.deg 0).toNat),⊤) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) →
    {q // q ∈ D.terms} → Γ(bundleTensorPower L (r*(D.deg 0).toNat),⊤)
  intro D q
  refine (sectionBlockEquiv f i L r e (D.deg 0).toNat).symm ⟨q.val.1,?_⟩
  have hd : (fun _ : Fin 1 => ((D.deg 0).toNat : ℤ)) = D.deg := funext (degree_eq_nat f i r hr ha D)
  rw [hd]
  exact D.mem_sections q.val q.property

private theorem realizedSection_norm (hr : 0 < r) (ha : 0 ≤ a) (hL : IsInvertible L) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) (q : {q // q ∈ D.terms})
      (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)),
      globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L (r*(D.deg 0).toNat))
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL _) (realizedSection f i L r e hr ha D q) =
          (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 D.deg q.val.1 := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) (q : {q // q ∈ D.terms})
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)),_
  intro D q y
  rw [sectionBlockNorm f i L r e hL (D.deg 0).toNat y]
  have he : (sectionBlockEquiv f i L r e (D.deg 0).toNat
      (realizedSection f i L r e hr ha D q) : X.functionField) = q.val.1 :=
    congrArg Subtype.val ((sectionBlockEquiv f i L r e (D.deg 0).toNat).apply_symm_apply _)
  rw [he,funext (degree_eq_nat f i r hr ha D)]

/-- EVERY genuine model datum of nonnegative original class lifts to ENTIRE
actual original L^(r*d) sections, with SAME original denominator and SAME weights. -/
def ofModelData (hr : 0 < r) (ha : 0 ≤ a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)) → NativeLineFubiniStudy.FSData L a := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)) → NativeLineFubiniStudy.FSData L a
  intro D
  refine {
    m := D.m
    m_pos := D.m_pos
    deg := r*(D.deg 0).toNat
    deg_eq := ?_
    terms := D.terms.attach.image (fun q => (realizedSection f i L r e hr ha D q,q.val.2)) }
  rw [Nat.cast_mul]
  have hq : (((D.deg 0).toNat : ℕ) : ℚ) = (D.deg 0 : ℚ) :=
    congrArg (fun z : ℤ => (z : ℚ)) (degree_eq_nat f i r hr ha D 0)
  rw [hq,D.deg_eq 0]
  field_simp [Nat.ne_of_gt hr]

/-- Every genuine model finite weighted datum retains its ENTIRE true evaluation
on EVERY original native point after actual whole-section realization. -/
theorem ofModelData_eval (hr : 0 < r) (ha : 0 ≤ a) (hL : IsInvertible L) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) y,
      (ofModelData f i L r e hr ha D).eval (f ≫ projectiveSpaceStructure k m) hL y =
        D.eval (nativeModelHomeomorph f i y) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ (D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ))) y,_
  intro D y
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
    (D.terms.attach.image (fun q => (realizedSection f i L r e hr ha D q,q.val.2))).sup _ =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup _
  rw [Finset.sup_image]
  apply congrArg (fun z : EReal => (((D.m : ℝ)⁻¹ : ℝ) : EReal)*z)
  calc
    _ = D.terms.attach.sup (fun q => (fullFieldModel f i).termVal D.deg q.val (nativeModelHomeomorph f i y)) := by
      apply Finset.sup_congr rfl
      intro q hq
      change ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y
        (bundleTensorPower L (r*(D.deg 0).toNat))
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL _)
        (realizedSection f i L r e hr ha D q) : ℝ≥0∞) + (q.val.2 : EReal) = _
      rw [realizedSection_norm f i L r e hr ha hL D q y]
      rfl
    _ = _ := realSupAttach D.terms
      (fun q => (fullFieldModel f i).termVal D.deg q (nativeModelHomeomorph f i y))

/-- Literal original model rational weights remain the SAME rational weights in the actual original family. -/
theorem ofModelData_isRational (hr : 0 < r) (ha : 0 ≤ a) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),D.IsRational →
      (ofModelData f i L r e hr ha D).IsRational := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),D.IsRational →
    (ofModelData f i L r e hr ha D).IsRational
  intro D hD q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  exact hD t.val t.property

/-- Actual WHOLE section realization retains EXACTLY the no-common-zero
condition on both ENTIRE original point spaces, without a finite-family lift certificate. -/
theorem ofModelData_noCommonZero_iff (hr : 0 < r) (ha : 0 ≤ a) (hL : IsInvertible L) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),
      (∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m),
        ∃ q ∈ (ofModelData f i L r e hr ha D).terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
          (bundleTensorPower L (ofModelData f i L r e hr ha D).deg)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL _) q.1 ≠ 0) ↔
      (∀ v : (fullFieldModel f i).an,∃ q ∈ D.terms,(fullFieldModel f i).secAbs v.1 D.deg q.1 ≠ 0) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  change ∀ D : (fullFieldModel f i).FSData (fun _ => a/(r : ℚ)),_
  intro D
  constructor
  · intro h v
    obtain ⟨y,rfl⟩ := (nativeModelHomeomorph f i).surjective v
    obtain ⟨q,hq,hq0⟩ := h y
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨t.val,t.property,fun hz => hq0 ((realizedSection_norm f i L r e hr ha hL D t y).trans hz)⟩
  · intro h y
    obtain ⟨q,hq,hq0⟩ := h (nativeModelHomeomorph f i y)
    refine ⟨_,Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_attach _ _,rfl⟩,?_⟩
    exact fun hz => hq0 ((realizedSection_norm f i L r e hr ha hL D ⟨q,hq⟩ y).symm.trans hz)

include e in
/-- Genuine finite rational FS functions of every nonnegative original ample-line
class agree EXACTLY with genuine model finite FS of class a/r under SAME whole homeomorphism. -/
theorem isFinFS_iff (hr : 0 < r) (ha : 0 ≤ a) (hL : IsInvertible L)
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal} :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    NativeLineFubiniStudy.IsFinFS (f ≫ projectiveSpaceStructure k m) L hL a φ ↔
      (fullFieldModel f i).IsFinFS (fun _ => a/(r : ℚ))
        (fun v => φ ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · exact isFinFS_transport f i L r e hr hL
  · rintro ⟨D,hD,hNZ,hEq⟩
    refine ⟨ofModelData f i L r e hr ha D,ofModelData_isRational f i L r e hr ha D hD,
      (ofModelData_noCommonZero_iff f i L r e hr ha hL D).mpr hNZ,?_⟩
    intro y
    have hy : φ y = D.eval (nativeModelHomeomorph f i y) := by
      simpa only [Homeomorph.symm_apply_apply] using hEq (nativeModelHomeomorph f i y)
    exact hy.trans (ofModelData_eval f i L r e hr ha hL D y).symm

end EnvelopeProperty.NativeAmpleModelFSRealization
