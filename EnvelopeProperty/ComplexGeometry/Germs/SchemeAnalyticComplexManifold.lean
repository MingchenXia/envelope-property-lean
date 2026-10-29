import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateModelTransport
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticManifold
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticSeparation
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticCountability

/-!
# Actual separated quasi-compact smooth schemes are the complex manifolds

The SAME native scheme charts are postcomposed with the actual PiLp linear
equivalence. Their actual analytic transitions are conjugates of the already
proved transitions. Actual source separatedness and quasi-compactness
produce Hausdorffness and second countability through existing native mothers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry Algebra ComplexSchemes Manifold
open ComplexGeometry.Pluripotential
open scoped Topology Manifold ContDiff

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance tnSchemeCoordinateTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

/-- The SAME actual coordinate chart with its actual Euclidean the target. -/
def schemeAnalyticComplexChart (p : SchemeComplexPoint f) :
    OpenPartialHomeomorph (SchemeComplexPoint f) (ComplexModel n) :=
  (schemeAnalyticCoordinateChart f n p).trans
    (schemeCoordinateModelEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The actual transported chart has exactly the original source. -/
theorem schemeAnalyticComplexChart_source (p : SchemeComplexPoint f) :
    (schemeAnalyticComplexChart f n p).source = (schemeAnalyticCoordinateChart f n p).source := by
  simp only [schemeAnalyticComplexChart, mfld_simps]

/-- The actual target is the genuine linear preimage of the old target. -/
theorem schemeAnalyticComplexChart_target (p : SchemeComplexPoint f) :
    (schemeAnalyticComplexChart f n p).target =
      (schemeCoordinateModelEquiv n) ⁻¹' (schemeAnalyticCoordinateChart f n p).target := by
  simp only [schemeAnalyticComplexChart, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm]

/-- The original chart-point coordinate is transported by the actual inverse. -/
theorem schemeAnalyticComplexChart_point (p : SchemeComplexPoint f) :
    schemeAnalyticComplexChart f n p p =
      (schemeCoordinateModelEquiv n).symm (schemeCoordinateCenter f n p) :=
  rfl

/-- The original chart cover internally gives the actual the-model atlas. -/
@[instance_reducible] def schemeAnalyticComplexChartedSpace :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) where
  atlas := Set.range (schemeAnalyticComplexChart f n)
  chartAt := schemeAnalyticComplexChart f n
  mem_chart_source p := by
    rw [schemeAnalyticComplexChart_source]
    exact schemeAnalyticCoordinateChart_point_mem_source f n p
  chart_mem_atlas p := ⟨p, rfl⟩

/-- The literal native transition of the actual transported charts. -/
def schemeAnalyticComplexTransition (p q : SchemeComplexPoint f) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  (schemeAnalyticComplexChart f n p).symm.trans (schemeAnalyticComplexChart f n q)

/-- Whole function readback as the genuine conjugate of the old transition. -/
theorem schemeAnalyticComplexTransition_apply (p q : SchemeComplexPoint f) (z : ComplexModel n) :
    schemeAnalyticComplexTransition f n p q z =
      (schemeCoordinateModelEquiv n).symm
        (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)) :=
  rfl

/-- The actual transported overlap sends its point to the SAME old overlap. -/
theorem schemeAnalyticComplexTransition_source (p q : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticComplexTransition f n p q).source) :
    schemeCoordinateModelEquiv n z ∈ (schemeAnalyticCoordinateTransition f n p q).source := by
  simpa only [schemeAnalyticComplexTransition, schemeAnalyticComplexChart,
    schemeAnalyticCoordinateTransition, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm] using hz

/-- Existing actual overlap analyticity and the genuine linear maps produce
the full transported transition analyticity on its true source. -/
theorem schemeAnalyticComplexTransition_analyticOnNhd (p q : SchemeComplexPoint f) :
    AnalyticOnNhd ℂ (schemeAnalyticComplexTransition f n p q)
      (schemeAnalyticComplexTransition f n p q).source := by
  intro z hz
  have hOld := schemeAnalyticCoordinateTransition_analyticOnNhd f n p q
    (schemeCoordinateModelEquiv n z) (schemeAnalyticComplexTransition_source f n p q z hz)
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
theorem schemeAnalyticComplexTransition_contDiffOn (p q : SchemeComplexPoint f)
    (k : WithTop ℕ∞) :
    ContDiffOn ℂ k (schemeAnalyticComplexTransition f n p q)
      (schemeAnalyticComplexTransition f n p q).source :=
  (schemeAnalyticComplexTransition_analyticOnNhd f n p q).contDiffOn
    (schemeAnalyticComplexTransition f n p q).open_source.uniqueDiffOn

/-- The actual reverse chart transition is the true native inverse. -/
theorem schemeAnalyticComplexTransition_symm (p q : SchemeComplexPoint f) :
    (schemeAnalyticComplexTransition f n p q).symm = schemeAnalyticComplexTransition f n q p :=
  rfl

/-- Both actual directions lie in the native smooth groupoid. -/
theorem schemeAnalyticComplexTransition_mem_contDiffGroupoid
    (p q : SchemeComplexPoint f) (k : WithTop ℕ∞) :
    schemeAnalyticComplexTransition f n p q ∈ contDiffGroupoid k 𝓘(ℂ, ComplexModel n) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      schemeAnalyticComplexTransition_contDiffOn f n p q k
  · have h := schemeAnalyticComplexTransition_contDiffOn f n q p k
    have ht : (schemeAnalyticComplexTransition f n p q).target =
        (schemeAnalyticComplexTransition f n q p).source :=
      congrArg (fun e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) => e.source)
        (schemeAnalyticComplexTransition_symm f n p q)
    simpa only [contDiffPregroupoid, mfld_simps, schemeAnalyticComplexTransition_symm, ht] using h

/-- The SAME actual atlas satisfies native the-model compatibility. -/
theorem schemeAnalyticComplex_hasGroupoid (k : WithTop ℕ∞) :
    letI := schemeAnalyticComplexChartedSpace f n
    HasGroupoid (SchemeComplexPoint f) (contDiffGroupoid k 𝓘(ℂ, ComplexModel n)) := by
  let := schemeAnalyticComplexChartedSpace f n
  constructor
  intro e e' he he'
  change e ∈ Set.range (schemeAnalyticComplexChart f n) at he
  change e' ∈ Set.range (schemeAnalyticComplexChart f n) at he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  exact schemeAnalyticComplexTransition_mem_contDiffGroupoid f n p q k

/-- Native manifold structure is derived for the actual transported atlas. -/
theorem schemeAnalyticComplex_isManifold (k : WithTop ℕ∞) :
    letI := schemeAnalyticComplexChartedSpace f n
    IsManifold 𝓘(ℂ, ComplexModel n) k (SchemeComplexPoint f) := by
  let := schemeAnalyticComplexChartedSpace f n
  let := schemeAnalyticComplex_hasGroupoid f n k
  exact IsManifold.mk' 𝓘(ℂ, ComplexModel n) k (SchemeComplexPoint f)

/-- Actual ORIGINAL source separatedness and quasi-compactness manufacture the
full the complex manifold, including genuine T2 and second-countability. -/
theorem schemeAnalyticComplex_isComplexManifold [IsSeparated f] [QuasiCompact f] :
    letI := schemeAnalyticComplexChartedSpace f n
    IsComplexManifold n (SchemeComplexPoint f) := by
  let := schemeAnalyticComplexChartedSpace f n
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : T2Space (SchemeComplexPoint f) := schemeAnalyticPoint_t2Space f
  let : SecondCountableTopology (SchemeComplexPoint f) := schemeAnalyticPoint_secondCountable f
  let : IsManifold 𝓘(ℂ, ComplexModel n) ∞ (SchemeComplexPoint f) :=
    schemeAnalyticComplex_isManifold f n ∞
  exact {}

end HolomorphicGerms
