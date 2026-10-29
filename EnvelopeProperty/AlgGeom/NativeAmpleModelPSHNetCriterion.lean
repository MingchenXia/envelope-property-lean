import EnvelopeProperty.AlgGeom.NativeAmpleModelFSRealization

/-! # Actual original whole-section finite FS decreasing nets and genuine model psh -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial Filter
open Alterations Scheme.Modules
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Independent original finite-rational-FS net criterion, retaining actual whole
original sections, genuine norms, original rational classes and genuine pointwise infimum. -/
def IsFiniteFSNetLimit (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L)
    (θ : ℝ) (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  (∃ y,u y ≠ ⊥) ∧ UpperSemicontinuous u ∧
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (a : J → ℚ) (v : J → RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal),
      (∀ j,IsFinFS p L hL (a j) (v j)) ∧ Tendsto (fun j => (a j : ℝ)) atTop (𝓝 θ) ∧
      (∀ y,Antitone fun j => v j y) ∧ ∀ y,u y = ⨅ j,v j y
end EnvelopeProperty.NativeLineFubiniStudy

namespace EnvelopeProperty.NativeAmpleModelPSHNetCriterion
open Berkovich CanonicalGeometry NativeLineFubiniStudy
open NativePulledProjectiveLineFrames NativeAmpleModelFubiniStudy NativeAmpleModelFSRealization
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

include i e in
/-- Every genuine original finite rational whole-section FS function is continuous
on the ENTIRE original native point space, from true norms and the SAME whole homeomorphism. -/
theorem isFinFS_continuous (hr : 0 < r) (hL : IsInvertible L) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hφ : NativeLineFubiniStudy.IsFinFS (f ≫ projectiveSpaceStructure k m) L hL a φ) : Continuous φ := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have hh := (isFinFS_transport f i L r e hr hL hφ).isFS.continuous.comp (nativeModelHomeomorph f i).continuous
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh

include e in
/-- Every true original directed decreasing finite FS net yields genuine model psh,
with actual original classes scaled by r and exactly the SAME original pointwise infimum. -/
theorem isPSH_of_finiteFSNetLimit (hr : 0 < r) (hL : IsInvertible L) {θ : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hu : IsFiniteFSNetLimit (f ≫ projectiveSpaceStructure k m) L hL θ u) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).IsPSH (fun _ => θ/(r : ℝ))
      (fun v => u ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  obtain ⟨hfin,_husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hu
  let : Preorder J := hJ
  let : IsDirected J (· ≤ ·) := hdir
  let : Nonempty J := hn
  have hf : ∃ z : (fullFieldModel f i).an,u ((nativeModelHomeomorph f i).symm z) ≠ ⊥ := by
    obtain ⟨y,hy⟩ := hfin
    exact ⟨nativeModelHomeomorph f i y,by simpa only [Homeomorph.symm_apply_apply] using hy⟩
  have hclass : Tendsto (fun j => ((a j/(r : ℚ) : ℚ) : ℝ)) atTop (𝓝 (θ/(r : ℝ))) := by
    simpa only [Rat.cast_div,Rat.cast_natCast] using ha.div_const (r : ℝ)
  exact FSSystemC.isPSH_of_iInf (F := (fullFieldModel f i).fsSystem) hf
    (fun j _ => a j/(r : ℚ)) (fun j z => v j ((nativeModelHomeomorph f i).symm z))
    (fun j => (isFinFS_transport f i L r e hr hL (hv j)).isFS)
    (tendsto_pi_nhds.mpr (fun _ => hclass))
    (fun z => hanti ((nativeModelHomeomorph f i).symm z))
    (fun z => hlim ((nativeModelHomeomorph f i).symm z))

include e in
/-- For every nonnegative REAL original ample-ray coefficient, the explicit
independent actual whole-section finite-FS net criterion is EXACTLY genuine model psh. -/
theorem isPSH_iff_finiteFSNetLimit (hr : 0 < r) (hL : IsInvertible L) {θ : ℝ} (hθ : 0 ≤ θ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    IsFiniteFSNetLimit (f ≫ projectiveSpaceStructure k m) L hL θ u ↔
      (fullFieldModel f i).IsPSH (fun _ => θ/(r : ℝ))
        (fun v => u ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · exact isPSH_of_finiteFSNetLimit f i L r e hr hL
  · intro hu
    have hnef : (fun _ : Fin 1 => θ/(r : ℝ)) ∈ (fullFieldModel f i).nefCone :=
      (fullFieldModel f i).mem_nefCone_of_nonneg (fun _ => div_nonneg hθ (Nat.cast_nonneg r))
    obtain ⟨J,hJ,hdir,hn,a,v,hv,hgt,ha,hanti,hlim⟩ := hu.exists_isFinFS_net_gt hnef
    let : Preorder J := hJ
    let : IsDirected J (· ≤ ·) := hdir
    let : Nonempty J := hn
    let b (j : J) : ℚ := (r : ℚ)*a j 0
    have hbpos (j : J) : 0 ≤ b j := by
      have h := (div_nonneg hθ (Nat.cast_nonneg r)).trans_lt (hgt j 0)
      have hq : (0 : ℚ) ≤ a j 0 := by exact_mod_cast h.le
      exact mul_nonneg (Nat.cast_nonneg _) hq
    have hclass (j : J) : (fun _ : Fin 1 => b j/(r : ℚ)) = a j := by
      funext c
      have hc : c = 0 := Subsingleton.elim c 0
      subst c
      dsimp [b]
      field_simp [Nat.ne_of_gt hr]
    let w (j : J) (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (f ≫ projectiveSpaceStructure k m)) := v j (nativeModelHomeomorph f i y)
    have hw (j : J) : NativeLineFubiniStudy.IsFinFS (f ≫ projectiveSpaceStructure k m) L hL (b j) (w j) := by
      apply (isFinFS_iff f i L r e hr (hbpos j) hL).mpr
      simpa only [hclass j,w,Homeomorph.apply_symm_apply] using hv j
    have hscale : (r : ℝ)*(θ/(r : ℝ)) = θ := by field_simp [Nat.ne_of_gt hr]
    have hb : Tendsto (fun j => (b j : ℝ)) atTop (𝓝 θ) := by
      have hh : Tendsto (fun j : J => (r : ℝ)*(a j 0 : ℝ)) atTop (𝓝 ((r : ℝ)*(θ/(r : ℝ)))) :=
        tendsto_const_nhds.mul ((tendsto_pi_nhds.mp ha) 0)
      simpa only [b,Rat.cast_mul,Rat.cast_natCast,hscale] using hh
    have hf : ∃ y,u y ≠ ⊥ := by
      obtain ⟨z,hz⟩ := hu.1
      exact ⟨(nativeModelHomeomorph f i).symm z,hz⟩
    have hl (y) : u y = ⨅ j,w j y := by
      simpa only [Homeomorph.symm_apply_apply,w] using hlim (nativeModelHomeomorph f i y)
    refine ⟨hf,?_,J,hJ,hdir,hn,b,w,hw,hb,(fun y => hanti (nativeModelHomeomorph f i y)),hl⟩
    rw [show u = fun y => ⨅ j,w j y from funext hl]
    exact upperSemicontinuous_iInf fun j => (isFinFS_continuous f i L r e hr hL (hw j)).upperSemicontinuous

end EnvelopeProperty.NativeAmpleModelPSHNetCriterion
