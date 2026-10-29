import EnvelopeProperty.Char0.AnalyticMultiplierSubadditivity

/-!
# Independent positive levels in analytic multiplier subadditivity

The two original quasi-PSH weights may have unrelated positive real levels.
Positive scaling preserves their actual local decompositions and finite loci.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.AnalyticMultiplierSubadditivity

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open ComplexGeometry ComplexGeometry.Pluripotential
open ComplexGeometry.Pluripotential.HolomorphicIdealSheaves
open ComplexGeometry.AnalyticGeometry

private theorem isGlobalQuasiPshPotential_const_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) :
    IsGlobalQuasiPshPotential (n := n) (fun y => (c : EReal) * u y) := by
  constructor
  · intro e z hz
    obtain ⟨P, r, hP, hr, heq⟩ := hu.1 e z hz
    refine ⟨fun y => (c : EReal) * P y, fun y => c * r y, hP.const_mul hc,
      hr.mono fun y hy => contDiffAt_const.mul hy, ?_⟩
    filter_upwards [heq] with y hy
    change (c : EReal) * chartFunction u e y = _
    rw [hy, EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top c), ← EReal.coe_mul]
  · intro x U hU hxU
    obtain ⟨y, hy, hfin⟩ := hu.2 x U hU hxU
    refine ⟨y, hy, ?_⟩
    change (c : EReal) * u y ≠ ⊥
    generalize u y = a at hfin ⊢
    induction a using EReal.rec with
    | bot => exact (hfin rfl).elim
    | top => simp [EReal.coe_mul_top_of_pos hc]
    | coe a => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

private theorem multiplierIdeal_one_coe_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (u : M → EReal) {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := n) 1 (fun y => (c : EReal) * u y) =
      multiplierIdeal (n := n) c u := by
  ext x f
  dsimp only [multiplierIdeal, chartFunction]
  apply and_congr_right
  intro _
  let e := complexChartAt (n := n) x
  change MultiplierIntegrableAt (fun y => (c : EReal) * u (e.val.symm y)) 1
      (fun y => f (e.val.symm y)) (e.val x) volume ↔
    MultiplierIntegrableAt (fun y => u (e.val.symm y)) c
      (fun y => f (e.val.symm y)) (e.val x) volume
  simpa only [one_mul] using
    (PositiveCurrentTraceMultiplier.multiplierIntegrableAt_coe_mul_iff
      (w := fun y => u (e.val.symm y)) (c := 1) (t := c)
      (f := fun y => f (e.val.symm y)) (z := e.val x) (μ := volume) one_pos hc)

/-- Analytic subadditivity at arbitrary independent positive real levels,
with the actual original multiplier ideals and their genuine germ product. -/
theorem multiplierIdeal_weighted_sum_le_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (multiplierIdeal (n := n) 1 (fun y => (a : EReal) * u y + (b : EReal) * v y)).Le
      ((multiplierIdeal (n := n) a u).mul (multiplierIdeal (n := n) b v)) := by
  have h := multiplierIdeal_sum_le_mul
    (isGlobalQuasiPshPotential_const_mul hu ha) (isGlobalQuasiPshPotential_const_mul hv hb)
  rw [multiplierIdeal_one_coe_mul u ha, multiplierIdeal_one_coe_mul v hb] at h
  exact h

/-- Splitting two arbitrary positive levels of the same quasi-PSH potential. -/
theorem multiplierIdeal_add_levels_le_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (multiplierIdeal (n := n) (a + b) u).Le
      ((multiplierIdeal (n := n) a u).mul (multiplierIdeal (n := n) b u)) := by
  have h := multiplierIdeal_weighted_sum_le_mul hu hu ha hb
  have hweight : (fun y => (a : EReal) * u y + (b : EReal) * u y) =
      fun y => ((a + b : ℝ) : EReal) * u y := by
    funext y
    rw [EReal.coe_add, EReal.right_distrib_of_nonneg
      (EReal.coe_nonneg.mpr ha.le) (EReal.coe_nonneg.mpr hb.le)]
  rw [hweight, multiplierIdeal_one_coe_mul u (add_pos ha hb)] at h
  exact h

end EnvelopeProperty.Char0.AnalyticMultiplierSubadditivity
