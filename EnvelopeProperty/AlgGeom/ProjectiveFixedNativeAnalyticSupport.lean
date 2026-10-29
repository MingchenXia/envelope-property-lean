import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticValues

/-! # Whole original native chart support is retained by the fixed-model analytic comparison -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeAnalyticSupport
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticCharts ProjectiveFixedNativeAnalyticValues
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i j : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]

/-- EVERY original alternative chart support is retained by the whole analytic
comparison to ONE SAME fixed original model; no alternative nonempty/matching premise. -/
theorem nativeChartHomeomorph_mem_chartDomain_iff
    (y : {y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) //
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j}) (l : Fin (m + 1)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (nativeChartHomeomorph f i j y : (fullFieldModel f i).an) ∈
        (fullFieldModel f i).chartDomain (fun _ => l) ↔
      y.1.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l := by
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  let P := fullFieldModel f i
  let v := nativeChartHomeomorph f i j y
  have hNZ (c : Fin 1) : P.coord c j ≠ 0 :=
    ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j
  let r : Γ(X,f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) :=
    f.app (MvPolynomial.coordinateOpen (R := k) j)
      (ProjectiveHomogeneousSections.coefficient j 1 (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X k l))
  let q : P.chartAlg (fun _ => j) :=
    ⟨P.coord 0 l / P.coord 0 j, P.coord_div_mem_chartAlg (fun _ => j) 0 l⟩
  have hq : q = nativeSectionsEquivModelChartAt f i j r := by
    apply Subtype.ext
    rw [nativeSectionsEquivModelChartAt_apply]
    exact ProjectiveChartGenericTransitions.coordinate_div f i j l
  have hvden : v.1.1.val (P.coordElem ⟨0,j⟩) ≠ 0 := (P.mem_chartDomain_iff.mp v.2) 0
  have he : SchemeValuedPoint.eval y.1.1 (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) y.2 r =
      v.1.1.val (P.coordElem ⟨0,l⟩) / v.1.1.val (P.coordElem ⟨0,j⟩) := by
    have h := P.chartMap_val_coord_div hNZ (P.mem_chartDomain_iff.mp v.2) 0 l
    change (P.chartHomeomorph (fun _ => j) hNZ v).val q = _ at h
    rw [nativeChartHomeomorph_affine, hq, nativeAffineChartHomeomorph_val] at h
    exact h
  have hopen : X.basicOpen r = (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) ⊓
      (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l) := by
    change X.basicOpen (f.app (MvPolynomial.coordinateOpen (R := k) j)
      (ProjectiveHomogeneousSections.coefficient j 1 (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X k l))) = _
    rw [← Scheme.preimage_basicOpen, ProjectiveHomogeneousSections.coefficient_X,
      MvPolynomial.coordinateHyperplaneLocalEquation_basicOpen, MvPolynomial.coordinateOpenOverlap_eq]
    rfl
  have hs : SchemeValuedPoint.eval y.1.1 (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) y.2 r ≠ 0 ↔
      y.1.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) l := by
    rw [ne_eq, SchemeValuedPoint.eval_eq_zero_iff, not_not, hopen]
    exact ⟨fun h => h.2, fun h => ⟨y.2,h⟩⟩
  have hm : (v : P.an) ∈ P.chartDomain (fun _ => l) ↔ v.1.1.val (P.coordElem ⟨0,l⟩) ≠ 0 := by
    rw [P.mem_chartDomain_iff]
    constructor
    · intro h
      exact h 0
    · intro h c
      have hc : c = 0 := Subsingleton.elim c 0
      subst c
      exact h
  change (v : P.an) ∈ P.chartDomain (fun _ => l) ↔ _
  rw [hm, ← hs, he]
  constructor
  · intro h
    exact div_ne_zero h hvden
  · intro h hz
    apply h
    rw [hz, zero_div]

end EnvelopeProperty.ProjectiveFixedNativeAnalyticSupport
