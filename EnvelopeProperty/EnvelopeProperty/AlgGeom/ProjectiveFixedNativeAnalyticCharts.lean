import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeModelCharts
import EnvelopeProperty.AlgGeom.ProjectiveNativeCoordinateChartSupport
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SchemeAffinePaperConvexity

/-! # Whole original native analytic charts on ONE SAME fixed reconstructed homogeneous model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeAnalyticCharts
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def relativeIsoHomeomorph {R : Type u} [CommRing R] (v : _root_.Valuation R ℝ≥0)
    {Y Z : Scheme.{u}} (e : Y ≅ Z) {p : Y ⟶ Spec (.of R)} {q : Z ⟶ Spec (.of R)}
    (he : e.hom ≫ q = p) : RelativeSchemeValuedPoint v p ≃ₜ RelativeSchemeValuedPoint v q :=
  (SchemeValuedPoint.isoHomeomorph e).subtype (fun y => by
    change (SchemeValuedPoint.map p y = SchemeValuedPoint.basePoint v) ↔
      (SchemeValuedPoint.map q (SchemeValuedPoint.map e.hom y) = SchemeValuedPoint.basePoint v)
    rw [← SchemeValuedPoint.map_comp,he])

variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i j : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]

/-- The WHOLE original native support-open valued-point space is the actual affine
Berkovich spectrum of its corresponding chart in ONE SAME fixed reconstructed model. -/
def nativeAffineChartHomeomorph :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    {y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) //
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j} ≃ₜ
        Berk k ((fullFieldModel f i).chartAlg (fun _ => j)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact ((RelativeSchemeValuedPoint.restrictionHomeomorph (v := (1 : _root_.Valuation k ℝ≥0))
    (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) (f ≫ projectiveSpaceStructure k m)).symm.trans
      (relativeIsoHomeomorph (1 : _root_.Valuation k ℝ≥0) (nativeChartIsoAt f i j)
        (nativeChartIsoAt_structure f i j))).trans RelativeSchemeValuedPoint.affineBerkHomeomorph

/-- The actual ENTIRE native analytic coordinate domain is homeomorphic to its
corresponding domain of ONE SAME original reconstructed whole-native-field model. -/
def nativeChartHomeomorph :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    {y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) //
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j} ≃ₜ
        (fullFieldModel f i).chartDomain (fun _ => j) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have hNZ (c : Fin 1) : (fullFieldModel f i).coord c j ≠ 0 :=
    ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j
  exact (nativeAffineChartHomeomorph f i j).trans
    ((fullFieldModel f i).chartHomeomorph (fun _ => j) hNZ).symm

/-- The entire original native chart point, including ALL original regular-function
values, commutes with the actual model affine chart and true native spectrum map. -/
theorem nativeChartHomeomorph_affine
    (y : {y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) //
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j}) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).chartHomeomorph (fun _ => j)
        (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
        (nativeChartHomeomorph f i j y) = nativeAffineChartHomeomorph f i j y := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact ((fullFieldModel f i).chartHomeomorph (fun _ => j)
    (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)).apply_symm_apply _

end EnvelopeProperty.ProjectiveFixedNativeAnalyticCharts
