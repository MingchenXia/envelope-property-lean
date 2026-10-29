import EnvelopeProperty.ComplexGeometry.Pluripotential.HolomorphicIdealSheaves
import EnvelopeProperty.ComplexGeometry.Pluripotential.IEnvelope
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-! # Full multiplier ideals for genuine zero-dimensional quasi-PSH potentials -/

open Metric Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ComplexGeometry.AnalyticGeometry.ZeroDimensionalQuasiPshMultiplierIdeals

open Pluripotential Pluripotential.HolomorphicIdealSheaves Pluripotential.IEnvelope
  Pluripotential.QuasiEquisingularApproximation

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X]

private theorem ne_bot_of_dim_zero {v : X → EReal}
    (hv : IsGlobalQuasiPshPotential (n := 0) v) (x : X) : v x ≠ ⊥ := by
  let e : ComplexChart 0 X := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨y, hy, hfin⟩ := hv.2 x e.val.source e.val.open_source hx
  have hyx : y = x := e.val.injOn hy hx (Subsingleton.elim _ _)
  simpa only [hyx] using hfin

private theorem integrable_at_of_finite
    (φ : ComplexModel 0 → EReal) (f : ComplexModel 0 → ℂ) (z : ComplexModel 0)
    {c : ℝ} (hc : 0 < c) (hbot : φ z ≠ ⊥) (htop : φ z ≠ ⊤) :
    MultiplierIntegrableAt φ c f z volume := by
  have hval : ∀ y, φ y = ((φ z).toReal : EReal) := by
    intro y
    rw [Subsingleton.elim y z]
    exact (EReal.coe_toReal htop hbot).symm
  have hf : f = fun _ => f z := by
    funext y
    rw [Subsingleton.elim y z]
  have hdens : multiplierDensity φ c f = fun _ =>
      ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (Real.exp (-(c * (φ z).toReal))) := by
    funext y
    have hfy : f y = f z := congrArg f (Subsingleton.elim y z)
    simp only [multiplierDensity, hval y, hfy, multiplierWeight_coe]
  refine ⟨hc, ball z 1, isOpen_ball, mem_ball_self one_pos, ?_, ?_, ?_⟩
  · rw [hf]
    exact differentiableOn_const (f z)
  · rw [hdens]
    exact aemeasurable_const
  · rw [hdens, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) measure_ball_lt_top

/-- A genuine zero-dimensional quasi-PSH potential has the full original holomorphic stalk. -/
theorem mem_multiplierIdeal_iff_holomorphicAt {v : X → EReal}
    (hv : IsGlobalQuasiPshPotential (n := 0) v) {c : ℝ} (hc : 0 < c)
    (x : X) (F : X → ℂ) :
    (multiplierIdeal (n := 0) c v).mem x F ↔ HolomorphicAt 0 F x := by
  refine ⟨fun h => h.1, fun hF => ⟨hF, ?_⟩⟩
  let e : ComplexChart 0 X := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  apply integrable_at_of_finite (chartFunction v e)
    (fun z => F (e.val.symm z)) (e.val x) hc
  · simpa only [chartFunction, e.val.left_inv hx] using ne_bot_of_dim_zero hv x
  · simpa only [chartFunction, e.val.left_inv hx] using hv.1.ne_top x

/-- Every extended-real function precedes a genuine zero-dimensional potential
in the actual all-chart, all-positive-level multiplier order. -/
theorem iOrderOnManifold_of_genuine_right (u : X → EReal) {v : X → EReal}
    (hv : IsGlobalQuasiPshPotential (n := 0) v) : IOrderOnManifold (n := 0) u v := by
  intro c hc e z _ f _ _
  apply (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp
  apply integrable_at_of_finite (chartFunction v e) f z hc
  · exact ne_bot_of_dim_zero hv (e.val.symm z)
  · exact hv.1.ne_top (e.val.symm z)

end
end ComplexGeometry.AnalyticGeometry.ZeroDimensionalQuasiPshMultiplierIdeals
