import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticGluing
import EnvelopeProperty.AlgGeom.GeneratedLineFamilyProjectiveEmbedding
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.Berkovich.SchemeCenterAffine

/-! # Actual original proper line norms under the SAME whole native model homeomorphism -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial
open Alterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveNativeModelLineMetrics
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticCharts ProjectiveFixedNativeAnalyticValues
open ProjectiveFixedNativeAnalyticGluing RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- EVERY whole original regular section retains its exact original value under
THE SAME global native analytic homeomorphism, in every actual original chart. -/
theorem nativeModelHomeomorph_chart_val (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hy : y.1.point ∈ f ⁻¹ᵁ coordinateOpen (R := k) j)
    (s : Γ(X,f ⁻¹ᵁ coordinateOpen (R := k) j)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    ((fullFieldModel f i).chartHomeomorph (fun _ => j)
      (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
      ⟨nativeModelHomeomorph f i y,(nativeToModel_mem_chartDomain_iff f i y j).mpr hy⟩).val
        (nativeSectionsEquivModelChartAt f i j s) = SchemeValuedPoint.eval y.1 _ hy s := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  have he : (⟨nativeModelHomeomorph f i y,(nativeToModel_mem_chartDomain_iff f i y j).mpr hy⟩ :
      (fullFieldModel f i).chartDomain (fun _ => j)) = nativeChartHomeomorph f i j ⟨y,hy⟩ :=
    Subtype.ext (nativeToModel_on_chart f i j y hy)
  rw [he,nativeChartHomeomorph_affine]
  exact nativeAffineChartHomeomorph_val f i j ⟨y,hy⟩ s

/-- Actual model coordinate value one DERIVES chart membership of the original
proper-model center by bounding EVERY original affine section, without center matching. -/
theorem center_mem_of_model_coordinate_eq_one (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hval : let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
      (nativeModelHomeomorph f i y).1.val ((fullFieldModel f i).coordElem ⟨0,j⟩) = 1) :
    center _root_.Valuation.one_apply_le_one y ∈ f ⁻¹ᵁ coordinateOpen (R := k) j := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  let P := fullFieldModel f i
  let v := nativeModelHomeomorph f i y
  have hv : v ∈ P.chartDomain (fun _ => j) := by
    apply P.mem_chartDomain_iff.mpr
    intro c
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    rw [hval]
    exact one_ne_zero
  have hy := (nativeToModel_mem_chartDomain_iff f i y j).mp hv
  apply center_mem_of_bounded_affine _root_.Valuation.one_apply_le_one y
    ⟨f ⁻¹ᵁ coordinateOpen (R := k) j,(coordinateOpen_isAffineOpen j).preimage f⟩ hy
  intro s
  rw [← nativeModelHomeomorph_chart_val f i j y hy s, P.chartHomeomorph_apply]
  let a := nativeSectionsEquivModelChartAt f i j s
  obtain ⟨d,g,hg,ha⟩ := (P.mem_chartAlg_iff
    (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)).mp a.property
  rw [P.chartMap_val_eq _ (P.mem_chartDomain_iff.mp hv) a hg ha]
  have hd : v.1.val (P.chartMono (fun _ => j) d) = 1 := by
    rw [P.val_chartMono]
    rw [Fin.prod_univ_one]
    have hvone : v.1.val (P.coordElem ⟨0,j⟩) = 1 := hval
    rw [hvone,one_pow]
  rw [hd,div_one]
  exact v.property.2.val_le_one _

/-- The TRUE norm of the SAME actual pulled-back whole original O(d) section
is its genuine fixed-model chart value under THE SAME global homeomorphism. -/
theorem modelLineNorm_homogeneousSection_eq_chartValue (j t : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hy : y.1.point ∈ f ⁻¹ᵁ coordinateOpen (R := k) j)
    (hval : let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
      (nativeModelHomeomorph f i y).1.val ((fullFieldModel f i).coordElem ⟨0,j⟩) = 1)
    (d : ℕ) (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    modelLineNorm _root_.Valuation.one_apply_le_one y
      ((coordinateHyperplanePoleSheafPower_isInvertible (R := k) t d).pullback f)
      (fibreSection y (SchemeLineSectionEvaluation.pullbackSectionHom f
        (ProjectiveHomogeneousSections.sectionHom t d F hF))) =
      ((fullFieldModel f i).chartHomeomorph (fun _ => j)
        (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
        ⟨nativeModelHomeomorph f i y,(nativeToModel_mem_chartDomain_iff f i y j).mpr hy⟩).val
        (nativeSectionsEquivModelChartAt f i j
          (f.app (coordinateOpen (R := k) j) (ProjectiveHomogeneousSections.coefficient j d F hF))) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  let M := coordinateHyperplanePoleSheafPower (R := k) t d
  let U : (projectiveSpace k m).affineOpens := ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d
  have hc := center_mem_of_model_coordinate_eq_one f i j y hval
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection t d F hF) =
      ProjectiveHomogeneousSections.coefficient j d F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient j t d F hF)
  have hr := SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection t d F hF)
  rw [hcoeff] at hr
  exact (modelLineNorm_pullbackSection_eq_localEval _root_.Valuation.one_apply_le_one y f
    (coordinateHyperplanePoleSheafPower_isInvertible (R := k) t d) U.1 hc
    (Scheme.Modules.pullbackIsoOfRestrictIso M U.1 e)
    (ProjectiveHomogeneousSections.sectionHom t d F hF)
    (ProjectiveHomogeneousSections.coefficient j d F hF) hr).trans
      (nativeModelHomeomorph_chart_val f i j y hy _).symm

end EnvelopeProperty.ProjectiveNativeModelLineMetrics
