import EnvelopeProperty.AlgGeom.PositiveDiagonalChartValuations
import EnvelopeProperty.AlgGeom.OriginalProjectiveWholeTensorModelSections
import EnvelopeProperty.AlgGeom.ProjectiveNativeModelLineMetrics

/-! # Actual original simultaneous chart values and proper centers -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open DeJongAlterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectiveFamilyNativeChartValues
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticGluing RelativeSchemeValuedPoint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ c,X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]

private abbrev f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
private abbrev b := f q p hp ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
private abbrev hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
private abbrev pivot := FiniteProjectiveNativeFieldModels.pivot q
private abbrev hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
private local instance fClosed : IsClosedImmersion (f q p hp) :=
  FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
private local instance pivotNonempty : Nonempty (f q p hp ⁻¹ᵁ coordinateOpen (R := k)
    (FiniteSegreOriginalProjectiveMaps.index d (pivot q))) :=
  FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp (pivot q) (hU q)
private abbrev P := letI := (b q p hp).stalkAlgebra (genericPoint X); FiniteProjectiveNativeFieldModels.model q (b q p hp) (hb q p hp)
private abbrev Z := letI := (b q p hp).stalkAlgebra (genericPoint X); fullFieldModel (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))
private abbrev hs := OriginalProjectivePositiveDiagonalAlgebra.model_positiveDiagonal_eq_actualSegreAlgebra q p hp
private abbrev H := letI := (b q p hp).stalkAlgebra (genericPoint X); PositiveDiagonalChartValuations.homeomorph (P q p hp)
  (OriginalProjectiveDiagonalNativeComparison.oneDegree_pos r) (Z q p hp) (hs q p hp)

/-- The actual Segre-base whole analytic homeomorphism, with exactly the fixed original diagonal map. -/
def homeomorph :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp) ≃ₜ (P q p hp).an := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  exact (nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))).trans (H q p hp)

/-- The original global homeomorphism uses THIS SAME actual point map after the derived base equality. -/
theorem originalHomeomorph_apply (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    OriginalProjectiveDiagonalNativeComparison.originalNativeSegreBaseModelHomeomorph q p hp y =
      homeomorph q p hp ((Homeomorph.setCongr
        (by rw [show b q p hp = p from FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp])) y) := rfl

private theorem coord_den (j : ∀ c,Fin (d c+1)) :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    (Z q p hp).coord 0 (FiniteSegreOriginalProjectiveMaps.index d j) =
      (P q p hp).chartDen j (OriginalProjectivePositiveDiagonalAlgebra.oneDegree (r+1)) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  rw [show (Z q p hp).coord 0 (FiniteSegreOriginalProjectiveMaps.index d j) =
      ∏ c,(P q p hp).coord c (j c) from
    FiniteSegreNativeCoordinateAlgebra.coordinate_product d q p hp (pivot q) (hU q) j,
    MultiModel.chartDen]
  apply Finset.prod_congr rfl
  intro c _
  change (P q p hp).coord c (j c) = (P q p hp).coord c (j c) ^ 1
  rw [pow_one]

private theorem coord_nonzero (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    ∀ c,(P q p hp).coord c (j c) ≠ 0 := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  change ∀ c,(P q p hp).coord c (j c) ≠ 0
  intro c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot q c)) := hU q c
  let := hj c
  exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c) (pivot q c) (j c)

/-- The actual corresponding Segre coordinate retains the product of ALL original factor coordinate values. -/
theorem coordinate_val (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (j : ∀ c,Fin (d c+1)) :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    (nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y).1.val
      ((Z q p hp).coordElem ⟨0,FiniteSegreOriginalProjectiveMaps.index d j⟩) =
      ∏ c,(homeomorph q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  rw [PositiveDiagonalChartValuations.coordinate_val (P q p hp)
    (OriginalProjectiveDiagonalNativeComparison.oneDegree_pos r) (Z q p hp) (hs q p hp) _ j
    (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) (coord_den q p hp j),MultiModel.val_chartMono]
  apply Finset.prod_congr rfl
  intro c _
  change _ ^ 1 = _
  rw [pow_one]
  rfl

private local instance baseProper : IsProper (b q p hp) := by
  let : IsProper (projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => FiniteSegreOriginalProjectiveMaps.dimension d) 0).isProper
  infer_instance

/-- Original factor coordinate values one DERIVE chart membership of the genuine proper-model center. -/
theorem center_mem (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (hv : letI := (b q p hp).stalkAlgebra (genericPoint X); ∀ c,(homeomorph q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) = 1) :
    center _root_.Valuation.one_apply_le_one y ∈
      f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj
  apply ProjectiveNativeModelLineMetrics.center_mem_of_model_coordinate_eq_one (f q p hp)
    (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) (FiniteSegreOriginalProjectiveMaps.index d j) y
  rw [coordinate_val q p hp y j]
  simp only [hv,Finset.prod_const_one]

/-- EVERY original regular joint-chart function retains its value under the SAME whole homeomorphism. -/
theorem chart_val (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (hv : letI := (b q p hp).stalkAlgebra (genericPoint X); ∀ c,(homeomorph q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) ≠ 0)
    (s : Γ(X,f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))) :
    let := (b q p hp).stalkAlgebra (genericPoint X)
    let := (b q p hp).sectionsAlgebra (f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    (P q p hp).chartMap (coord_nonzero q p hp j hj) (homeomorph q p hp y).1 hv |>.val
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj s) =
      SchemeValuedPoint.eval y.1 _ (by
        let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj
        apply (nativeToModel_mem_chartDomain_iff (f q p hp)
          (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y _).mp
        apply (Z q p hp).mem_chartDomain_iff.mpr
        intro c
        have hc : c = 0 := Subsingleton.elim _ _
        subst c
        change (nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y).1.val
          ((Z q p hp).coordElem ⟨0,FiniteSegreOriginalProjectiveMaps.index d j⟩) ≠ 0
        rw [coordinate_val q p hp y j]
        exact Finset.prod_ne_zero_iff.mpr (fun c _ => hv c)) s := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj
  let := (b q p hp).sectionsAlgebra (f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  let z := nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y
  have hy : y.1.point ∈ f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j) := by
    apply (nativeToModel_mem_chartDomain_iff (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y _).mp
    apply (Z q p hp).mem_chartDomain_iff.mpr
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    change (nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y).1.val
      ((Z q p hp).coordElem ⟨0,FiniteSegreOriginalProjectiveMaps.index d j⟩) ≠ 0
    rw [coordinate_val q p hp y j]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => hv c)
  have h := PositiveDiagonalChartValuations.chartMap_val (P q p hp)
    (OriginalProjectiveDiagonalNativeComparison.oneDegree_pos r) (Z q p hp) (hs q p hp) z j
    (coord_nonzero q p hp j hj) (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) (coord_den q p hp j)
    hv (nativeSectionsEquivModelChartAt (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))
      (FiniteSegreOriginalProjectiveMaps.index d j) s)
  have he : (Subalgebra.equivOfEq _ _
      (PositiveDiagonalChartValuations.chartAlg_eq (P q p hp)
        (OriginalProjectiveDiagonalNativeComparison.oneDegree_pos r) (Z q p hp) (hs q p hp) j
        (coord_nonzero q p hp j hj) (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) (coord_den q p hp j)))
      (nativeSectionsEquivModelChartAt (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))
        (FiniteSegreOriginalProjectiveMaps.index d j) s) =
      OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj s := Subtype.ext rfl
  rw [he] at h
  refine h.symm.trans ?_
  exact ProjectiveNativeModelLineMetrics.nativeModelHomeomorph_chart_val (f q p hp)
    (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) (FiniteSegreOriginalProjectiveMaps.index d j) y hy s

open Scheme.Modules FiniteOriginalProjectivePowerFrames

private abbrev jointChart (j : ∀ c,Fin (d c+1)) : X.affineOpens :=
  ⟨f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j),
    (coordinateOpen_isAffineOpen (FiniteSegreOriginalProjectiveMaps.index d j)).preimage (f q p hp)⟩

omit [IsIntegral X] in
private theorem joint_le (j : ∀ c,Fin (d c+1)) (c : Fin (r+1)) :
    (jointChart q p hp j).1 ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (j c) := by
  change f q p hp ⁻¹ᵁ coordinateOpen (R := k) _ ≤ _
  rw [OriginalProjectiveFamilyChartAlgebras.morphism_preimage_coordinateOpen]
  exact iInf_le _ c

private abbrev lineFrame (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ) (j : ∀ c,Fin (d c+1)) :=
  OriginalProjectiveTensorPivotCoefficients.chartFrame d q t n j (jointChart q p hp j) (joint_le q p hp j)

private abbrev localCoefficient (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ) (j : ∀ c,Fin (d c+1))
    (s : Γ(projectiveLine d q t n,⊤)) :=
  OriginalProjectiveTensorPivotCoefficients.coefficient d q t n j (jointChart q p hp j) (joint_le q p hp j) s

/-- The genuine proper-model norm of EVERY original whole finite tensor-line section. -/
def sectionNorm (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (s : Γ(projectiveLine d q t n,⊤)) : ℝ≥0 :=
  modelLineNorm _root_.Valuation.one_apply_le_one y (projectiveLine_isInvertible d q t n)
    (fibreSection y (SchemeModuleGlobalSections.sectionHom (projectiveLine d q t n) s))

/-- EVERY whole original tensor-line section has its true chart coefficient norm under THIS SAME homeomorphism. -/
theorem sectionNorm_eq_chartValue (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (j : ∀ c,Fin (d c+1)) (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (hv : letI := (b q p hp).stalkAlgebra (genericPoint X);
      ∀ c,(homeomorph q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) = 1)
    (s : Γ(projectiveLine d q t n,⊤)) :
    letI := (b q p hp).stalkAlgebra (genericPoint X)
    letI := (b q p hp).sectionsAlgebra (f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    sectionNorm q p hp t n y s =
      ((P q p hp).chartMap (coord_nonzero q p hp j hj) (homeomorph q p hp y).1
        (fun c => by rw [hv c]; exact one_ne_zero)).val
          (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj
            (localCoefficient q p hp t n j s)) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let := (b q p hp).sectionsAlgebra (f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  have hc := center_mem q p hp y j hj hv
  have hn := modelLineNorm_fibreSection_eq_localEval _root_.Valuation.one_apply_le_one y
    (projectiveLine_isInvertible d q t n) (jointChart q p hp j).1 hc
    (pullbackIsoOfRestrictIso (projectiveLine d q t n) (jointChart q p hp j).1 (lineFrame q p hp t n j))
    (SchemeModuleGlobalSections.sectionHom (projectiveLine d q t n) s) (localCoefficient q p hp t n j s)
    (SchemeLineSectionEvaluation.sectionHom_localScalar (projectiveLine d q t n)
      (jointChart q p hp j) (lineFrame q p hp t n j) s)
  exact hn.trans (chart_val q p hp y j hj (fun c => by rw [hv c]; exact one_ne_zero)
    (localCoefficient q p hp t n j s)).symm

/-- EVERY actual whole original tensor-line section has EXACTLY the genuine multigraded secAbs at the SAME whole native point. -/
theorem sectionNorm_eq_secAbs (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (s : Γ(projectiveLine d q t n,⊤)) :
    letI := (b q p hp).stalkAlgebra (genericPoint X)
    sectionNorm q p hp t n y s =
      (P q p hp).secAbs (homeomorph q p hp y).1 (fun c => (n c : ℤ))
        (OriginalProjectiveWholeTensorModelSections.coefficient d q t n s) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let v := homeomorph q p hp y
  obtain ⟨j,hj,hv⟩ := (P q p hp).exists_chartIndex v
  have hJ : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := by
    intro c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot q c)) := hU q c
    exact (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty (q c)
      (pivot q c) (j c)).mp (hj c)
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
  let := (b q p hp).sectionsAlgebra (f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  rw [sectionNorm_eq_chartValue q p hp t n y j hJ hv s,
    MultiModel.secAbs_eq_chartMap v.property.2 (coord_nonzero q p hp j hJ)
      (fun c => by rw [hv c]; exact one_ne_zero)
      (OriginalProjectiveWholeTensorModelSections.coefficient_mem_sections d q (b q p hp) (hb q p hp) t n s)]
  have he : OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ
      (localCoefficient q p hp t n j s) =
      (⟨OriginalProjectiveWholeTensorModelSections.coefficient d q t n s /
        (P q p hp).chartDenZ j (fun c => (n c : ℤ)),
        (P q p hp).div_chartDenZ_mem_chartAlg (coord_nonzero q p hp j hJ)
          (OriginalProjectiveWholeTensorModelSections.coefficient_mem_sections d q (b q p hp) (hb q p hp) t n s)⟩ :
          (P q p hp).chartAlg j) := by
    apply Subtype.ext
    rw [OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv_apply]
    exact (OriginalProjectiveWholeTensorModelSections.coefficient_chart_fraction d q p hp t n j hJ s).symm
  rw [he]
  have hu : (∏ c,v.1.val ((P q p hp).coordElem ⟨c,j c⟩) ^ (n c : ℤ)) = 1 := by
    simp only [hv,one_zpow,Finset.prod_const_one]
  rw [hu,mul_one]

omit [IsIntegral X] in
include hp in
private theorem originalProper : IsProper p := by
  rw [← FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp]
  exact baseProper q p hp

private def modelBaseHomeomorph (b' : X ⟶ Spec (.of k))
    (hb' : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = b') (h : b' = p) :
    (letI := b'.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b' hb').an) ≃ₜ
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).an) := by
  cases h
  exact Homeomorph.refl _

private theorem modelBase_secAbs (b' : X ⟶ Spec (.of k))
    (hb' : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = b') (h : b' = p)
    (v : (letI := b'.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b' hb').an))
    (a : Fin (r+1) → ℤ) (g : X.functionField) :
    (letI := b'.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b' hb').secAbs v.1 a g) =
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).secAbs
        (modelBaseHomeomorph q p hp b' hb' h v).1 a g) := by
  cases h
  rfl

private def pointBaseHomeomorph (b' : X ⟶ Spec (.of k)) (h : b' = p) :
    RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p ≃ₜ
      RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) b' := Homeomorph.setCongr (by rw [h])

omit [IsIntegral X] in
private theorem properBase_norm (b' : X ⟶ Spec (.of k)) (h : b' = p) [IsProper b']
    (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (s : Γ(projectiveLine d q t n,⊤)) :
    letI := originalProper q p hp
    modelLineNorm _root_.Valuation.one_apply_le_one y (projectiveLine_isInvertible d q t n)
      (fibreSection y (SchemeModuleGlobalSections.sectionHom (projectiveLine d q t n) s)) =
    modelLineNorm _root_.Valuation.one_apply_le_one (pointBaseHomeomorph p b' h y) (projectiveLine_isInvertible d q t n)
      (fibreSection (pointBaseHomeomorph p b' h y)
        (SchemeModuleGlobalSections.sectionHom (projectiveLine d q t n) s)) := by
  let := originalProper q p hp
  cases h
  rfl

/-- The genuine norm is taken over the literal ORIGINAL structure morphism p. -/
def originalSectionNorm (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (s : Γ(projectiveLine d q t n,⊤)) : ℝ≥0 := by
  let := originalProper q p hp
  exact modelLineNorm _root_.Valuation.one_apply_le_one y (projectiveLine_isInvertible d q t n)
    (fibreSection y (SchemeModuleGlobalSections.sectionHom (projectiveLine d q t n) s))

/-- The ENTIRE originally p-based homeomorphism preserves the true norm of EVERY whole original tensor-line section. -/
theorem originalSectionNorm_eq_secAbs (t : ∀ c,Fin (d c+1)) (n : Fin (r+1) → ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (s : Γ(projectiveLine d q t n,⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    originalSectionNorm q p hp t n y s =
      (FiniteProjectiveNativeFieldModels.model q p hp).secAbs
        (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y).1
        (fun c => (n c : ℤ)) (OriginalProjectiveWholeTensorModelSections.coefficient d q t n s) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let e := FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp
  let yb := pointBaseHomeomorph p (b q p hp) e y
  have hpoint : OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y =
      modelBaseHomeomorph q p hp (b q p hp) (hb q p hp) e (homeomorph q p hp yb) := rfl
  calc
    originalSectionNorm q p hp t n y s = sectionNorm q p hp t n yb s :=
      properBase_norm q p hp (b q p hp) e t n y s
    _ = (P q p hp).secAbs (homeomorph q p hp yb).1 (fun c => (n c : ℤ))
        (OriginalProjectiveWholeTensorModelSections.coefficient d q t n s) :=
      sectionNorm_eq_secAbs q p hp t n yb s
    _ = (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).secAbs
        (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y).1
        (fun c => (n c : ℤ)) (OriginalProjectiveWholeTensorModelSections.coefficient d q t n s)) := by
      rw [modelBase_secAbs q p hp (b q p hp) (hb q p hp) e,← hpoint]

end EnvelopeProperty.OriginalProjectiveFamilyNativeChartValues
