import SGPT.Okounkov.SchemeCoordinateModelTransport
import BingWangEntropy.SchemeAnalyticManifold
import BingWangEntropy.SchemeAnalyticSeparation
import BingWangEntropy.SchemeAnalyticCountability

/-!
# Actual separated quasi-compact smooth schemes are TN complex manifolds

The SAME native scheme charts are postcomposed with the actual PiLp linear
equivalence. Their actual analytic transitions are conjugates of the already
proved BWE transitions. Actual source separatedness and quasi-compactness
produce Hausdorffness and second countability through existing native mothers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy Manifold
open TranscendentalNakamaye.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance tnSchemeCoordinateTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

/-- The SAME actual coordinate chart with its actual Euclidean TN target. -/
def schemeAnalyticTNChart (p : SchemeComplexPoint f) :
    OpenPartialHomeomorph (SchemeComplexPoint f) (ComplexModel n) :=
  (schemeAnalyticCoordinateChart f n p).trans
    (schemeCoordinateModelEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The actual transported chart has exactly the original source. -/
theorem schemeAnalyticTNChart_source (p : SchemeComplexPoint f) :
    (schemeAnalyticTNChart f n p).source = (schemeAnalyticCoordinateChart f n p).source := by
  simp only [schemeAnalyticTNChart, mfld_simps]

/-- The actual target is the genuine linear preimage of the old target. -/
theorem schemeAnalyticTNChart_target (p : SchemeComplexPoint f) :
    (schemeAnalyticTNChart f n p).target =
      (schemeCoordinateModelEquiv n) ⁻¹' (schemeAnalyticCoordinateChart f n p).target := by
  simp only [schemeAnalyticTNChart, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm]

/-- The original chart-point coordinate is transported by the actual inverse. -/
theorem schemeAnalyticTNChart_point (p : SchemeComplexPoint f) :
    schemeAnalyticTNChart f n p p =
      (schemeCoordinateModelEquiv n).symm (schemeCoordinateCenter f n p) :=
  rfl

/-- The original chart cover internally gives the actual TN-model atlas. -/
@[instance_reducible] def schemeAnalyticTNChartedSpace :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) where
  atlas := Set.range (schemeAnalyticTNChart f n)
  chartAt := schemeAnalyticTNChart f n
  mem_chart_source p := by
    rw [schemeAnalyticTNChart_source]
    exact schemeAnalyticCoordinateChart_point_mem_source f n p
  chart_mem_atlas p := ⟨p, rfl⟩

/-- The literal native transition of the actual transported charts. -/
def schemeAnalyticTNTransition (p q : SchemeComplexPoint f) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  (schemeAnalyticTNChart f n p).symm.trans (schemeAnalyticTNChart f n q)

/-- Whole function readback as the genuine conjugate of the old transition. -/
theorem schemeAnalyticTNTransition_apply (p q : SchemeComplexPoint f) (z : ComplexModel n) :
    schemeAnalyticTNTransition f n p q z =
      (schemeCoordinateModelEquiv n).symm
        (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)) :=
  rfl

/-- The actual transported overlap sends its point to the SAME old overlap. -/
theorem schemeAnalyticTNTransition_source (p q : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticTNTransition f n p q).source) :
    schemeCoordinateModelEquiv n z ∈ (schemeAnalyticCoordinateTransition f n p q).source := by
  simpa only [schemeAnalyticTNTransition, schemeAnalyticTNChart,
    schemeAnalyticCoordinateTransition, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm] using hz

/-- Existing actual overlap analyticity and the genuine linear maps produce
the full transported transition analyticity on its true source. -/
theorem schemeAnalyticTNTransition_analyticOnNhd (p q : SchemeComplexPoint f) :
    AnalyticOnNhd ℂ (schemeAnalyticTNTransition f n p q)
      (schemeAnalyticTNTransition f n p q).source := by
  intro z hz
  have hOld := schemeAnalyticCoordinateTransition_analyticOnNhd f n p q
    (schemeCoordinateModelEquiv n z) (schemeAnalyticTNTransition_source f n p q z hz)
  have hL : AnalyticAt ℂ (schemeCoordinateModelEquiv n) z :=
    (schemeCoordinateModelEquiv n).toContinuousLinearMap.analyticAt z
  have hInv : AnalyticAt ℂ (schemeCoordinateModelEquiv n).symm
      (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)) :=
    (schemeCoordinateModelEquiv n).symm.toContinuousLinearMap.analyticAt _
  change AnalyticAt ℂ (fun w : ComplexModel n =>
    (schemeCoordinateModelEquiv n).symm
      (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n w))) z
  exact AnalyticAt.comp
    (f := fun w : ComplexModel n =>
      schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n w))
    (g := ((schemeCoordinateModelEquiv n).symm : (Fin n → ℂ) → ComplexModel n))
    (x := z) hInv
    (AnalyticAt.comp (f := (schemeCoordinateModelEquiv n : ComplexModel n → (Fin n → ℂ)))
      (g := (schemeAnalyticCoordinateTransition f n p q : (Fin n → ℂ) → (Fin n → ℂ)))
      (x := z) hOld hL)

/-- The genuine analytic transition is smooth on its actual open source. -/
theorem schemeAnalyticTNTransition_contDiffOn (p q : SchemeComplexPoint f)
    (k : WithTop ℕ∞) :
    ContDiffOn ℂ k (schemeAnalyticTNTransition f n p q)
      (schemeAnalyticTNTransition f n p q).source :=
  (schemeAnalyticTNTransition_analyticOnNhd f n p q).contDiffOn
    (schemeAnalyticTNTransition f n p q).open_source.uniqueDiffOn

/-- The actual reverse chart transition is the true native inverse. -/
theorem schemeAnalyticTNTransition_symm (p q : SchemeComplexPoint f) :
    (schemeAnalyticTNTransition f n p q).symm = schemeAnalyticTNTransition f n q p :=
  rfl

/-- Both actual directions lie in the native smooth groupoid. -/
theorem schemeAnalyticTNTransition_mem_contDiffGroupoid
    (p q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    schemeAnalyticTNTransition f n p q ∈ contDiffGroupoid k 𝓘(ℂ, ComplexModel n) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      schemeAnalyticTNTransition_contDiffOn f n p q k
  · have h := schemeAnalyticTNTransition_contDiffOn f n q p k
    have ht : (schemeAnalyticTNTransition f n p q).target =
        (schemeAnalyticTNTransition f n q p).source :=
      congrArg (fun e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) => e.source)
        (schemeAnalyticTNTransition_symm f n p q)
    simpa only [contDiffPregroupoid, mfld_simps, schemeAnalyticTNTransition_symm, ht] using h

/-- The SAME actual atlas satisfies native TN-model compatibility. -/
theorem schemeAnalyticTN_hasGroupoid (k : WithTop ℕ∞) :
    letI := schemeAnalyticTNChartedSpace f n
    HasGroupoid (SchemeComplexPoint f) (contDiffGroupoid k 𝓘(ℂ, ComplexModel n)) := by
  let := schemeAnalyticTNChartedSpace f n
  constructor
  intro e e' he he'
  change e ∈ Set.range (schemeAnalyticTNChart f n) at he
  change e' ∈ Set.range (schemeAnalyticTNChart f n) at he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  exact schemeAnalyticTNTransition_mem_contDiffGroupoid f n p q k

/-- Native manifold structure is derived for the actual transported atlas. -/
theorem schemeAnalyticTN_isManifold (k : WithTop ℕ∞) :
    letI := schemeAnalyticTNChartedSpace f n
    IsManifold 𝓘(ℂ, ComplexModel n) k (SchemeComplexPoint f) := by
  let := schemeAnalyticTNChartedSpace f n
  let := schemeAnalyticTN_hasGroupoid f n k
  exact IsManifold.mk' 𝓘(ℂ, ComplexModel n) k (SchemeComplexPoint f)

/-- Actual ORIGINAL source separatedness and quasi-compactness manufacture the
full TN complex manifold, including genuine T2 and second-countability. -/
theorem schemeAnalyticTN_isComplexManifold [IsSeparated f] [QuasiCompact f] :
    letI := schemeAnalyticTNChartedSpace f n
    IsComplexManifold n (SchemeComplexPoint f) := by
  let := schemeAnalyticTNChartedSpace f n
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : T2Space (SchemeComplexPoint f) := schemeAnalyticPoint_t2Space f
  let : SecondCountableTopology (SchemeComplexPoint f) := schemeAnalyticPoint_secondCountable f
  let : IsManifold 𝓘(ℂ, ComplexModel n) ∞ (SchemeComplexPoint f) :=
    schemeAnalyticTN_isManifold f n ∞
  exact {}

end SGPT.Okounkov
