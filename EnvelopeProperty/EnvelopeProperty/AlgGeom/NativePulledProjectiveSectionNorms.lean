import EnvelopeProperty.AlgGeom.NativePulledProjectiveModelSections

/-! # EVERY original pulled-line global section has its true SAME model graded norm -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial Opposite
open DeJongAlterations Scheme.Modules
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativePulledProjectiveSectionNorms
open Berkovich CanonicalGeometry NativePulledProjectiveLineFrames NativePulledProjectiveModelSections
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticGluing ProjectiveNativeModelLineMetrics RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i t : Fin (m + 1)) (d : ℕ)
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- The actual original generic coefficient retains the actual zero global section. -/
theorem coefficient_zero : coefficient f i t d 0 = 0 := by
  rw [coefficient_eq_sectionRatio]
  exact map_zero _

/-- Nonzero ACTUAL original global sections are precisely nonzero actual model coefficients. -/
theorem coefficient_ne_zero_iff (s : Γ(line f t d,⊤)) :
    coefficient f i t d s ≠ 0 ↔ s ≠ 0 := by
  rw [← coefficient_zero f i t d,ne_eq,(coefficient_injective f i t d).eq_iff,ne_eq]

/-- The genuine WHOLE original global-section / whole genuine model-section equivalence. -/
def sectionEquiv :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    Γ(line f t d,⊤) ≃ (fullFieldModel f i).sections (fun _ => (d : ℤ)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  apply Equiv.ofBijective (fun s => ⟨coefficient f i t d s,coefficient_mem_sections f i t d s⟩)
  constructor
  · intro s v h
    exact coefficient_injective f i t d (congrArg Subtype.val h)
  · intro g
    obtain ⟨s,hs⟩ := coefficient_surjective f i t d g
    exact ⟨s,Subtype.ext hs⟩

/-- The entire section equivalence's forward map is the SAME literal original generic coefficient. -/
theorem sectionEquiv_apply (s : Γ(line f t d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionEquiv f i t d s : X.functionField) = coefficient f i t d s := rfl

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- The TRUE proper-model norm of an arbitrary ACTUAL whole original global section. -/
def sectionNorm
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (s : Γ(line f t d,⊤)) : ℝ≥0 :=
  modelLineNorm _root_.Valuation.one_apply_le_one y (line_isInvertible f t d)
    (fibreSection y (SchemeModuleGlobalSections.sectionHom (line f t d) s))

/-- EVERY actual whole original global section retains its true norm as the whole
original chart coefficient value under THE SAME global native homeomorphism. -/
theorem sectionNorm_eq_chartValue (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hy : y.1.point ∈ f ⁻¹ᵁ coordinateOpen (R := k) j)
    (hval : let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
      (nativeModelHomeomorph f i y).1.val ((fullFieldModel f i).coordElem ⟨0,j⟩) = 1)
    (s : Γ(line f t d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    sectionNorm f t d y s =
      ((fullFieldModel f i).chartHomeomorph (fun _ => j)
        (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
        ⟨nativeModelHomeomorph f i y,(nativeToModel_mem_chartDomain_iff f i y j).mpr hy⟩).val
        (nativeSectionsEquivModelChartAt f i j (chartCoefficient f t d j s)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  let U : X.affineOpens := ⟨f ⁻¹ᵁ coordinateOpen (R := k) j,(coordinateOpen_isAffineOpen j).preimage f⟩
  have hc := center_mem_of_model_coordinate_eq_one f i j y hval
  have hn := modelLineNorm_fibreSection_eq_localEval _root_.Valuation.one_apply_le_one y
    (line_isInvertible f t d) U.1 hc
    (pullbackIsoOfRestrictIso (line f t d) U.1 (chartFrame f t d j))
    (SchemeModuleGlobalSections.sectionHom (line f t d) s) (chartCoefficient f t d j s)
    (SchemeLineSectionEvaluation.sectionHom_localScalar (line f t d) U (chartFrame f t d j) s)
  exact hn.trans (nativeModelHomeomorph_chart_val f i j y hy (chartCoefficient f t d j s)).symm

/-- At EVERY original native point, EVERY actual whole original global pulled-line
section has exactly the genuine secAbs of its SAME literal actual native model coefficient. -/
theorem sectionNorm_eq_secAbs
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (s : Γ(line f t d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    sectionNorm f t d y s =
      (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ))
        (coefficient f i t d s) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  let v := nativeModelHomeomorph f i y
  obtain ⟨a,ha,hv⟩ := P.exists_chartIndex v
  let j := a 0
  let : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j) :=
    (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty f i j).mp (ha 0)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  have hdom : v ∈ P.chartDomain (fun _ => j) := by
    apply P.mem_chartDomain_iff.mpr
    intro c
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    rw [hv 0]
    exact one_ne_zero
  have hy := (nativeToModel_mem_chartDomain_iff f i y j).mp hdom
  rw [sectionNorm_eq_chartValue f i t d j y hy (hv 0) s,P.chartHomeomorph_apply,
    MultiModel.secAbs_eq_chartMap v.property.2
      (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
      (P.mem_chartDomain_iff.mp hdom) (coefficient_mem_sections f i t d s)]
  have hd : P.chartDenZ (fun _ => j) (fun _ => (d : ℤ)) = coordinate f i j ^ d := by
    rw [MultiModel.chartDenZ,Fin.prod_univ_one]
    exact zpow_natCast _ _
  have he : nativeSectionsEquivModelChartAt f i j (chartCoefficient f t d j s) =
      (⟨coefficient f i t d s / P.chartDenZ (fun _ => j) (fun _ => (d : ℤ)),
        P.div_chartDenZ_mem_chartAlg
          (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j)
          (coefficient_mem_sections f i t d s)⟩ : P.chartAlg (fun _ => j)) := by
    apply Subtype.ext
    change (nativeSectionsEquivModelChartAt f i j (chartCoefficient f t d j s) : X.functionField) =
      coefficient f i t d s / P.chartDenZ (fun _ => j) (fun _ => (d : ℤ))
    rw [nativeSectionsEquivModelChartAt_apply,hd,coefficient_chart_fraction]
  rw [← he,Fin.prod_univ_one]
  have hval : v.1.val (P.coordElem ⟨0,j⟩) = 1 := hv 0
  rw [hval,one_zpow,mul_one]

end EnvelopeProperty.NativePulledProjectiveSectionNorms
