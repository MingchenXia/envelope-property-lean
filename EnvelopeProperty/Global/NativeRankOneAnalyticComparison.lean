import EnvelopeProperty.Global.NativeRankOneRelativeCharts
import EnvelopeProperty.Global.NativeRankOneCoordinateCover
import EnvelopeProperty.Berkovich.SchemeHausdorff
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # The WHOLE original rank-one analytic space is its SAME native scheme's valued-point space -/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The SAME original affine chart over the SAME trivial coefficient seminorm. -/
def nativeRankOneOriginalRelativeChart (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.chartDomain j ≃ₜ RelativeSpectrum (1 : Valuation k ℝ≥0) (X.chartAlg j) :=
  (X.chartHomeomorph j hj).trans Berk.relativeSpectrumHomeomorph

/-- The true original projective-stalk residue point is the WHOLE actual original relative chart inverse. -/
theorem nativeRankOnePoint_eq_chart_inverse (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (x : X.chartDomain j) :
    X.nativeRankOnePoint x.1 =
      ((X.nativeRankOneRelativeChartHomeomorph j hj).symm
        (X.nativeRankOneOriginalRelativeChart j hj x)).1.1 := by
  let y := (X.nativeRankOneRelativeChartHomeomorph j hj).symm
    (X.nativeRankOneOriginalRelativeChart j hj x)
  have hx := (X.nativeRankOneSupport_mem_coordinateOpen x.1 (j 0)).mpr
    ((mem_chartDomain_iff.mp x.2) 0)
  have h := (X.nativeRankOneAbsoluteChartHomeomorph j hj).injective
    (show X.nativeRankOneAbsoluteChartHomeomorph j hj ⟨X.nativeRankOnePoint x.1, hx⟩ =
      X.nativeRankOneAbsoluteChartHomeomorph j hj ⟨y.1.1, y.2⟩ from by
      apply Spectrum.ext_val
      intro a
      rw [X.nativeRankOneAbsoluteChartHomeomorph_val_apply,
        X.nativeRankOnePoint_eval_originalChart,
        X.nativeRankOneAbsoluteChartHomeomorph_val_apply]
      exact X.nativeRankOneRelativeChartHomeomorph_symm_val j hj
        (X.nativeRankOneOriginalRelativeChart j hj x) a)
  exact congrArg Subtype.val h

/-- The true original projective residue point lies over the SAME WHOLE original trivial-base point. -/
theorem nativeRankOnePoint_mem_relativeLocus (x : X.an) :
    X.nativeRankOnePoint x ∈ SchemeValuedPoint.relativeLocus
      (1 : Valuation k ℝ≥0) X.nativeRankOneStructure := by
  obtain ⟨j, hj, hv⟩ := X.exists_chartIndex x
  have hx : x ∈ X.chartDomain j := mem_chartDomain_iff.mpr fun c => by
    rw [hv c]
    exact one_ne_zero
  rw [X.nativeRankOnePoint_eq_chart_inverse j hj ⟨x, hx⟩]
  exact ((X.nativeRankOneRelativeChartHomeomorph j hj).symm
    (X.nativeRankOneOriginalRelativeChart j hj ⟨x, hx⟩)).1.property

/-- The SAME original whole projective-stalk residue point over its exact original base point. -/
def nativeRankOneRelativePoint (x : X.an) :
    RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeRankOneStructure :=
  ⟨X.nativeRankOnePoint x, X.nativeRankOnePoint_mem_relativeLocus x⟩

/-- The canonical whole original point map is the actual original relative chart inverse on EVERY original chart. -/
theorem nativeRankOneRelativePoint_onChart (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (x : X.chartDomain j) :
    X.nativeRankOneRelativePoint x.1 =
      ((X.nativeRankOneRelativeChartHomeomorph j hj).symm
        (X.nativeRankOneOriginalRelativeChart j hj x)).1 :=
  Subtype.ext (X.nativeRankOnePoint_eq_chart_inverse j hj x)

private theorem rankOne_chartDomain_of_support {x : X.an} (j : X.ChartIndex)
    (hx : X.nativeRankOneSupport x ∈ X.nativeRankOneCoordinateOpen (j 0)) :
    x ∈ X.chartDomain j := by
  apply mem_chartDomain_iff.mpr
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  exact (X.nativeRankOneSupport_mem_coordinateOpen x (j 0)).mp hx

/-- Actual whole original native points distinguish the ENTIRE original seminorm. -/
theorem nativeRankOneRelativePoint_injective : Function.Injective X.nativeRankOneRelativePoint := by
  intro x y h
  obtain ⟨j, hj, hxv⟩ := X.exists_chartIndex x
  have hx : x ∈ X.chartDomain j := mem_chartDomain_iff.mpr fun c => by
    rw [hxv c]
    exact one_ne_zero
  have hp : X.nativeRankOneSupport x = X.nativeRankOneSupport y :=
    congrArg (fun z => z.1.point) h
  have hy : y ∈ X.chartDomain j := by
    apply X.rankOne_chartDomain_of_support j
    rw [← hp]
    exact (X.nativeRankOneSupport_mem_coordinateOpen x (j 0)).mpr
      ((mem_chartDomain_iff.mp hx) 0)
  have he : (X.nativeRankOneRelativeChartHomeomorph j hj).symm
      (X.nativeRankOneOriginalRelativeChart j hj ⟨x, hx⟩) =
    (X.nativeRankOneRelativeChartHomeomorph j hj).symm
      (X.nativeRankOneOriginalRelativeChart j hj ⟨y, hy⟩) := by
    apply Subtype.ext
    exact (X.nativeRankOneRelativePoint_onChart j hj ⟨x, hx⟩).symm.trans
      (h.trans (X.nativeRankOneRelativePoint_onChart j hj ⟨y, hy⟩))
  exact congrArg Subtype.val ((X.nativeRankOneOriginalRelativeChart j hj).injective
    ((X.nativeRankOneRelativeChartHomeomorph j hj).symm.injective he))

/-- EVERY actual native point over the SAME original base is recovered from a genuine original affine chart. -/
theorem nativeRankOneRelativePoint_surjective : Function.Surjective X.nativeRankOneRelativePoint := by
  intro y
  have hcov : y.1.point ∈ ⨆ i : Fin (X.M 0 + 1), X.nativeRankOneCoordinateOpen i := by
    rw [X.nativeRankOne_iSup_coordinateOpen]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hci : X.coord 0 i ≠ 0 := by
    intro hz
    have he : X.coordElem ⟨0, i⟩ = 0 := Subtype.ext (by simp [hz])
    change X.coordElem ⟨0, i⟩ ∉ y.1.point.asHomogeneousIdeal at hi
    exact hi (he ▸ zero_mem y.1.point.asHomogeneousIdeal.toIdeal)
  let j : X.ChartIndex := fun c => (Subsingleton.elim (0 : Fin 1) c) ▸ i
  have hj : ∀ c, X.coord c (j c) ≠ 0 := by
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    exact hci
  have hy : y.1.point ∈ X.nativeRankOneCoordinateOpen (j 0) := hi
  let x := (X.nativeRankOneOriginalRelativeChart j hj).symm
    (X.nativeRankOneRelativeChartHomeomorph j hj ⟨y, hy⟩)
  refine ⟨x.1, ?_⟩
  rw [X.nativeRankOneRelativePoint_onChart j hj x]
  simp only [x, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- Actual canonical whole original points are continuous, by their genuine original covering chart maps. -/
@[fun_prop]
theorem continuous_nativeRankOneRelativePoint : Continuous X.nativeRankOneRelativePoint := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj, hxv⟩ := X.exists_chartIndex x
  have hx : x ∈ X.chartDomain j := mem_chartDomain_iff.mpr fun c => by
    rw [hxv c]
    exact one_ne_zero
  have hc : Continuous fun z : X.chartDomain j => X.nativeRankOneRelativePoint z.1 := by
    have ht : Continuous fun z : X.chartDomain j =>
        ((X.nativeRankOneRelativeChartHomeomorph j hj).symm
          (X.nativeRankOneOriginalRelativeChart j hj z)).1 :=
      continuous_subtype_val.comp ((X.nativeRankOneRelativeChartHomeomorph j hj).symm.continuous.comp
        (X.nativeRankOneOriginalRelativeChart j hj).continuous)
    exact ht.congr (fun z => (X.nativeRankOneRelativePoint_onChart j hj z).symm)
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt
    ((X.isOpen_chartDomain j).mem_nhds hx)

private local instance nativeRankOneStructure_separated : IsSeparated X.nativeRankOneStructure := by
  unfold nativeRankOneStructure
  infer_instance

/-- The WHOLE original rank-one analytic space is the genuine valued-point space of its SAME original native scheme. -/
def nativeRankOneAnalyticHomeomorph : X.an ≃ₜ
    RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeRankOneStructure :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective X.nativeRankOneRelativePoint
      ⟨X.nativeRankOneRelativePoint_injective, X.nativeRankOneRelativePoint_surjective⟩)
        X.continuous_nativeRankOneRelativePoint

/-- The actual whole homeomorphism retains the SAME original true projective-stalk residue point. -/
theorem nativeRankOneAnalyticHomeomorph_val (x : X.an) :
    (X.nativeRankOneAnalyticHomeomorph x).1 = X.nativeRankOnePoint x := rfl

/-- The whole original comparison preserves the SAME original prime valuation kernel. -/
theorem nativeRankOneAnalyticHomeomorph_support (x : X.an) :
    (X.nativeRankOneAnalyticHomeomorph x).1.point.asHomogeneousIdeal.toIdeal = x.1.val.supp := rfl

/-- The actual whole original homeomorphism retains EVERY original affine chart as a whole-point map. -/
theorem nativeRankOneAnalyticHomeomorph_onChart (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (x : X.chartDomain j) :
    X.nativeRankOneAnalyticHomeomorph x.1 =
      ((X.nativeRankOneRelativeChartHomeomorph j hj).symm
        (X.nativeRankOneOriginalRelativeChart j hj x)).1 :=
  X.nativeRankOneRelativePoint_onChart j hj x

end EnvelopeProperty.MultiModel
