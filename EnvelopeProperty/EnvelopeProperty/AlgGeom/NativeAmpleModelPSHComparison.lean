import EnvelopeProperty.AlgGeom.NativeAmpleModelFubiniStudyComparison
import EnvelopeProperty.AlgGeom.NativeAmpleModelPSHNetCriterion

/-! # Actual original whole-section psh of an arbitrary original ample line and SAME model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial Filter
open DeJongAlterations Scheme.Modules
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Independently defined ORIGINAL psh by actual whole original FS section-norm nets,
including FS families with common zeroes and arbitrary original real weights. -/
def IsPSH (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L)
    (θ : ℝ) (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) : Prop :=
  (∃ y,u y ≠ ⊥) ∧ UpperSemicontinuous u ∧
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (a : J → ℚ) (v : J → RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal),
      (∀ j,IsFS p L hL (a j) (v j)) ∧ Tendsto (fun j => (a j : ℝ)) atTop (𝓝 θ) ∧
      (∀ y,Antitone fun j => v j y) ∧ ∀ y,u y = ⨅ j,v j y
end EnvelopeProperty.NativeLineFubiniStudy

namespace EnvelopeProperty.NativeAmpleModelPSHComparison
open Berkovich CanonicalGeometry NativeLineFubiniStudy
open NativePulledProjectiveLineFrames NativeAmpleModelFubiniStudyComparison
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

include e in
/-- EVERY genuine ORIGINAL psh net transports with its actual class scaling,
true whole FS sections, original order and exact pointwise infimum to genuine model psh. -/
theorem isPSH_transport (hr : 0 < r) (hL : IsInvertible L) {θ : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal}
    (hu : NativeLineFubiniStudy.IsPSH (f ≫ projectiveSpaceStructure k m) L hL θ u) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).IsPSH (fun _ => θ/(r : ℝ)) (fun v => u ((nativeModelHomeomorph f i).symm v)) := by
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
    (fun j => isFS_transport f i L r e hr hL (hv j))
    (tendsto_pi_nhds.mpr (fun _ => hclass))
    (fun z => hanti ((nativeModelHomeomorph f i).symm z))
    (fun z => hlim ((nativeModelHomeomorph f i).symm z))

include e in
/-- For EVERY nonnegative REAL coefficient, independently defined actual original
whole-section psh is EXACTLY genuine model psh under THE SAME whole native homeomorphism. -/
theorem isPSH_iff (hr : 0 < r) (hL : IsInvertible L) {θ : ℝ} (hθ : 0 ≤ θ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    NativeLineFubiniStudy.IsPSH (f ≫ projectiveSpaceStructure k m) L hL θ u ↔
      (fullFieldModel f i).IsPSH (fun _ => θ/(r : ℝ)) (fun v => u ((nativeModelHomeomorph f i).symm v)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  constructor
  · exact isPSH_transport f i L r e hr hL
  · intro hu
    have hc := (NativeAmpleModelPSHNetCriterion.isPSH_iff_finiteFSNetLimit f i L r e hr hL hθ u).mpr hu
    obtain ⟨hfin,husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hc
    let : Preorder J := hJ
    let : IsDirected J (· ≤ ·) := hdir
    let : Nonempty J := hn
    exact ⟨hfin,husc,J,hJ,hdir,hn,a,v,(fun j => NativeLineFubiniStudy.IsFinFS.isFS (f ≫ projectiveSpaceStructure k m) L hL (hv j)),
      ha,hanti,hlim⟩

include i e in
/-- On the original nonnegative ample ray, full ORIGINAL FS decreasing nets and
actual original finite rational FS decreasing nets yield the SAME original psh class. -/
theorem isPSH_iff_finiteFSNetLimit (hr : 0 < r) (hL : IsInvertible L) {θ : ℝ} (hθ : 0 ≤ θ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) → EReal) :
    NativeLineFubiniStudy.IsPSH (f ≫ projectiveSpaceStructure k m) L hL θ u ↔
      IsFiniteFSNetLimit (f ≫ projectiveSpaceStructure k m) L hL θ u := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact (isPSH_iff f i L r e hr hL hθ u).trans
    (NativeAmpleModelPSHNetCriterion.isPSH_iff_finiteFSNetLimit f i L r e hr hL hθ u).symm

end EnvelopeProperty.NativeAmpleModelPSHComparison
