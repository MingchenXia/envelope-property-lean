import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticSupport
import EnvelopeProperty.AlgGeom.NativeGenericSectionValueRelations

/-! # Original native analytic chart maps agree on every actual overlap -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeAnalyticOverlap
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticCharts ProjectiveFixedNativeAnalyticValues
open ProjectiveFixedNativeAnalyticSupport
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)]

private theorem germ_equiv_symm (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]
    (a : let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
      (fullFieldModel f i).chartAlg (fun _ => j)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
    X.germToFunctionField (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
      ((nativeSectionsEquivModelChartAt f i j).symm a) = (a : X.functionField) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  let e := nativeSectionsEquivModelChartAt f i j
  exact (nativeSectionsEquivModelChartAt_apply f i j (e.symm a)).symm.trans
    (congrArg Subtype.val (e.apply_symm_apply a))

/-- The actual whole original chart maps into ONE SAME fixed homogeneous model
agree on EVERY original native overlap, including nongeneric support points. -/
theorem nativeChartHomeomorph_eq_on_overlap (j l : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]
    [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l)]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (hyj : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
    (hyl : y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (nativeChartHomeomorph f i j ⟨y,hyj⟩ : (fullFieldModel f i).an) =
      (nativeChartHomeomorph f i l ⟨y,hyl⟩ : (fullFieldModel f i).an) := by
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l)
  let P := fullFieldModel f i
  let vj := nativeChartHomeomorph f i j ⟨y,hyj⟩
  let vl := nativeChartHomeomorph f i l ⟨y,hyl⟩
  have hj (c : Fin 1) : P.coord c j ≠ 0 :=
    ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j
  have hl (c : Fin 1) : P.coord c l ≠ 0 :=
    ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i l
  have hvlj : (vl : P.an) ∈ P.chartDomain (fun _ => j) :=
    (nativeChartHomeomorph_mem_chartDomain_iff f i l ⟨y,hyl⟩ j).mpr hyj
  let wj : P.chartDomain (fun _ => j) := ⟨vl,hvlj⟩
  suffices he : vj = wj by exact congrArg Subtype.val he
  apply (P.chartHomeomorph (fun _ => j) hj).injective
  apply Berk.ext_val
  intro a
  obtain ⟨d,g,hg,ha⟩ := (P.mem_chartAlg_iff hj).mp a.property
  let b : P.chartAlg (fun _ => l) := ⟨g / P.chartDen (fun _ => l) d, P.div_chartDen_mem_chartAlg hg⟩
  let r : P.chartAlg (fun _ => l) := ⟨P.chartDen (fun _ => j) d / P.chartDen (fun _ => l) d,
    P.div_chartDen_mem_chartAlg (P.chartDen_mem_piece (fun _ => j) d)⟩
  let ej := nativeSectionsEquivModelChartAt f i j
  let el := nativeSectionsEquivModelChartAt f i l
  have hfield : X.germToFunctionField (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) (ej.symm a) *
      X.germToFunctionField (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l) (el.symm r) =
      X.germToFunctionField (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l) (el.symm b) := by
    rw [germ_equiv_symm, germ_equiv_symm, germ_equiv_symm, ha]
    exact div_mul_div_cancel₀ (P.chartDen_ne_zero hj d)
  have hn := SchemeValuedPoint.eval_mul_of_genericGerm_mul _ _ y.1 hyj hyl
    (ej.symm a) (el.symm r) (el.symm b) hfield
  have hvj (q : P.chartAlg (fun _ => j)) :
      (nativeAffineChartHomeomorph f i j ⟨y,hyj⟩).val q =
        SchemeValuedPoint.eval y.1 (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) hyj (ej.symm q) := by
    have h := nativeAffineChartHomeomorph_val f i j ⟨y,hyj⟩ (ej.symm q)
    change (nativeAffineChartHomeomorph f i j ⟨y,hyj⟩).val (ej (ej.symm q)) = _ at h
    simpa only [ej.apply_symm_apply] using h
  have hvl (q : P.chartAlg (fun _ => l)) :
      (nativeAffineChartHomeomorph f i l ⟨y,hyl⟩).val q =
        SchemeValuedPoint.eval y.1 (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l) hyl (el.symm q) := by
    have h := nativeAffineChartHomeomorph_val f i l ⟨y,hyl⟩ (el.symm q)
    change (nativeAffineChartHomeomorph f i l ⟨y,hyl⟩).val (el (el.symm q)) = _ at h
    simpa only [el.apply_symm_apply] using h
  rw [← hvj, ← hvl, ← hvl] at hn
  have hb := P.chartMap_val_div hl (P.mem_chartDomain_iff.mp vl.property) hg
  have hr := P.chartMap_val_div hl (P.mem_chartDomain_iff.mp vl.property)
    (P.chartDen_mem_piece (fun _ => j) d)
  change (P.chartHomeomorph (fun _ => l) hl vl).val b = _ at hb
  change (P.chartHomeomorph (fun _ => l) hl vl).val r = _ at hr
  rw [nativeChartHomeomorph_affine] at hb hr
  have hjd := P.val_chartMono_ne_zero (P.mem_chartDomain_iff.mp hvlj) d
  have hld := P.val_chartMono_ne_zero (P.mem_chartDomain_iff.mp vl.property) d
  have hrNZ : (nativeAffineChartHomeomorph f i l ⟨y,hyl⟩).val r ≠ 0 := by
    rw [hr]
    exact div_ne_zero hjd hld
  have hw : (P.chartHomeomorph (fun _ => j) hj wj).val a *
      (nativeAffineChartHomeomorph f i l ⟨y,hyl⟩).val r =
        (nativeAffineChartHomeomorph f i l ⟨y,hyl⟩).val b := by
    rw [P.chartHomeomorph_apply, P.chartMap_val_eq hj (P.mem_chartDomain_iff.mp hvlj) a hg ha, hr, hb]
    exact div_mul_div_cancel₀ hjd
  have he := mul_right_cancel₀ hrNZ (hn.trans hw.symm)
  rw [nativeChartHomeomorph_affine]
  exact he

end EnvelopeProperty.ProjectiveFixedNativeAnalyticOverlap
