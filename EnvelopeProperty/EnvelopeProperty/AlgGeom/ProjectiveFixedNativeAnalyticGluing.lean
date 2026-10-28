import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticOverlap
import Mathlib.Topology.IsLocalHomeomorph

/-! # The whole original native analytic space is ONE fixed native-function-field model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open DeJongAlterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeAnalyticGluing
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticCharts
open ProjectiveFixedNativeAnalyticSupport ProjectiveFixedNativeAnalyticOverlap
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)]

omit [IsIntegral X] [IsClosedImmersion f] in
private theorem exists_nativeChart
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    ∃ j : Fin (m + 1), y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j := by
  have h : f y.1.point ∈ ⨆ j : Fin (m + 1), MvPolynomial.coordinateOpen (R := k) j := by
    rw [MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp h
  exact ⟨j,hj⟩

/-- The whole actual original native analytic map into ONE fixed whole-K(X) model,
constructed using actual native support charts and their proved overlap identities. -/
def nativeToModel
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).an := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let j := (exists_nativeChart f y).choose
  have hy : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j :=
    (exists_nativeChart f y).choose_spec
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) := ⟨⟨y.1.point,hy⟩⟩
  exact (nativeChartHomeomorph f i j ⟨y,hy⟩ : (fullFieldModel f i).an)

/-- The actual global map is the whole actual native chart map on EVERY original chart. -/
theorem nativeToModel_on_chart (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hy : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    nativeToModel f i y = (nativeChartHomeomorph f i j ⟨y,hy⟩ : (fullFieldModel f i).an) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let a := (exists_nativeChart f y).choose
  have ha : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) a :=
    (exists_nativeChart f y).choose_spec
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) a) := ⟨⟨y.1.point,ha⟩⟩
  change (nativeChartHomeomorph f i a ⟨y,ha⟩ : (fullFieldModel f i).an) = _
  exact nativeChartHomeomorph_eq_on_overlap f i a j y ha hy

/-- The whole global map preserves EXACTLY every actual original coordinate support open. -/
theorem nativeToModel_mem_chartDomain_iff
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (j : Fin (m + 1)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    nativeToModel f i y ∈ (fullFieldModel f i).chartDomain (fun _ => j) ↔
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let a := (exists_nativeChart f y).choose
  have ha : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) a :=
    (exists_nativeChart f y).choose_spec
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) a) := ⟨⟨y.1.point,ha⟩⟩
  exact nativeChartHomeomorph_mem_chartDomain_iff f i a ⟨y,ha⟩ j

/-- Equality of whole fixed-model images forces equality of the original native points. -/
theorem nativeToModel_injective : Function.Injective (nativeToModel f i) := by
  intro y z he
  obtain ⟨j,hy⟩ := exists_nativeChart f y
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) := ⟨⟨y.1.point,hy⟩⟩
  have hz : z.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j := by
    apply (nativeToModel_mem_chartDomain_iff f i z j).mp
    rw [← he]
    exact (nativeToModel_mem_chartDomain_iff f i y j).mpr hy
  rw [nativeToModel_on_chart f i j y hy, nativeToModel_on_chart f i j z hz] at he
  have h := (nativeChartHomeomorph f i j).injective (Subtype.ext he)
  exact congrArg Subtype.val h

/-- Every whole model point comes from an actual original native point; nonempty
original charts follow internally from the model's actual nonzero coordinates. -/
theorem nativeToModel_surjective : Function.Surjective (nativeToModel f i) := by
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  intro v
  obtain ⟨a,ha,hv⟩ := P.exists_chartIndex v
  let j := a 0
  have hcoord : coordinate f i j ≠ 0 := ha 0
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) :=
    (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty f i j).mp hcoord
  have hdom : v ∈ P.chartDomain (fun _ => j) := by
    apply P.mem_chartDomain_iff.mpr
    intro c
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    rw [hv 0]
    exact one_ne_zero
  let w : P.chartDomain (fun _ => j) := ⟨v,hdom⟩
  let y := (nativeChartHomeomorph f i j).symm w
  refine ⟨y.1,?_⟩
  rw [nativeToModel_on_chart f i j y.1 y.2]
  exact congrArg Subtype.val ((nativeChartHomeomorph f i j).apply_symm_apply w)

/-- On a genuine open neighborhood of EVERY original native point, the actual
global map is an original chart homeomorphism followed by an actual open inclusion. -/
theorem nativeToModel_isLocalHomeomorph : IsLocalHomeomorph (nativeToModel f i) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro y
  obtain ⟨j,hy⟩ := exists_nativeChart f y
  let : Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) := ⟨⟨y.1.point,hy⟩⟩
  let U := RelativeSchemeValuedPoint.supportOpens (1 : _root_.Valuation k ℝ≥0)
    (f ≫ projectiveSpaceStructure k m) (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  refine ⟨U,U.isOpen.mem_nhds hy,?_⟩
  have hEq : (U : Set _).domRestrict (nativeToModel f i) =
      fun z => (nativeChartHomeomorph f i j z : (fullFieldModel f i).an) := by
    funext z
    exact nativeToModel_on_chart f i j z.1 z.2
  rw [hEq]
  exact ((fullFieldModel f i).isOpen_chartDomain (fun _ => j)).isOpenEmbedding_subtypeVal.comp
    (nativeChartHomeomorph f i j).isOpenEmbedding

/-- The WHOLE independently defined original native analytic space is genuinely
homeomorphic to ONE SAME original homogeneous model over ALL actual native K(X). -/
def nativeModelHomeomorph :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) ≃ₜ
      (fullFieldModel f i).an :=
  (nativeToModel_isLocalHomeomorph f i).toHomeomorphOfBijective
    ⟨nativeToModel_injective f i,nativeToModel_surjective f i⟩

end EnvelopeProperty.ProjectiveFixedNativeAnalyticGluing
