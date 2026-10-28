import TranscendentalNakamaye.Pending.BlowupJacobianMultiplierGermEquivalence
import TranscendentalNakamaye.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false

/-! # Actual all-fiber Jacobian multiplier germs on global modifications

Geometry supplies all off-null, proper and surjective requirements. No
factorization into a finite blowup tower or integrability certificate.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace TranscendentalNakamaye.Pending.AnalyticModificationJacobianMultiplierGerms

open FirstPass FirstPass.HolomorphicMaps FirstPass.BlowupSequences
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

/-- Every genuine proper holomorphic modification supplies the complete
all-fiber Jacobian criterion using its actual original Haar weighted germs. -/
theorem multiplierIntegrableAt_iff_fiber_jacobian_germs
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) (x : X)
    {w : ComplexModel (m + 1) → EReal} {g : ComplexModel (m + 1) → ℂ}
    {c : ℝ} (hc : 0 < c)
    (hw : QuasiPlurisubharmonicAt w ((complexChartAt (n := m + 1) x).val x))
    (hg : ∀ᶠ z in 𝓝 ((complexChartAt (n := m + 1) x).val x),
      DifferentiableAt ℂ g z) :
    MultiplierIntegrableAt w c g ((complexChartAt (n := m + 1) x).val x) volume ↔
      ∀ y : Y, π y = x → MultiplierIntegrableAt
        (fun z => w (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z)) c
        (fun z => g (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z) *
          complexJacobian (coordinateMap π (complexChartAt (n := m + 1) y)
            (complexChartAt (n := m + 1) x)) z)
        ((complexChartAt (n := m + 1) y).val y) volume := by
  have hn := AnalyticModificationLocalDiscrepancy.isInjectiveOffNull_of_isAnalyticModification hπ
  constructor
  · intro hint y hy
    let d := complexChartAt (n := m + 1) x
    let e := complexChartAt (n := m + 1) y
    let F := coordinateMap π e d
    let D := coordinateDomain π e d
    have hD : IsOpen D := coordinateDomain_isOpen hπ.1 e d
    have hpD : e.val y ∈ D := by
      apply mem_coordinateDomain (mem_chart_source _ _)
      rw [hy]
      exact mem_chart_source _ _
    have hFy : F (e.val y) = d.val x := by
      change coordinateMap π e d (e.val y) = d.val x
      rw [coordinateMap_at (f := π) (e := e) (d := d)
        (show y ∈ e.val.source from mem_chart_source _ _), hy]
    obtain ⟨S, hS, hπinj⟩ := hn
    let S' := e.val '' (S ∩ e.val.source)
    have hS' : volume S' = 0 := hS y
    have hFi : InjOn F (D \ S') := by
      intro p hp q hq hpq
      have hpS : e.val.symm p ∉ S := by
        intro h
        exact hp.2 ⟨e.val.symm p, ⟨h, e.val.map_target hp.1.1⟩,
          e.val.right_inv hp.1.1⟩
      have hqS : e.val.symm q ∉ S := by
        intro h
        exact hq.2 ⟨e.val.symm q, ⟨h, e.val.map_target hq.1.1⟩,
          e.val.right_inv hq.1.1⟩
      have hpqπ := d.val.injOn hp.1.2 hq.1.2 hpq
      have hpqe := hπinj hpS hqS hpqπ
      calc p = e.val (e.val.symm p) := (e.val.right_inv hp.1.1).symm
           _ = e.val (e.val.symm q) := congrArg e.val hpqe
           _ = q := e.val.right_inv hq.1.1
    apply BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian hD
      (coordinateMap_contDiffOn hπ.1 e d) hpD hS' hFi
    · change QuasiPlurisubharmonicAt w (F (e.val y))
      rw [hFy]
      exact hw
    · change MultiplierIntegrableAt w c g (F (e.val y)) volume
      rw [hFy]
      exact hint
  · exact ProperJacobianMultiplierGermDescent.multiplierIntegrableAt_of_fiber_jacobian_germs
      hπ.1 hπ.2.1
      (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ) hn x hc hw hg


end
end TranscendentalNakamaye.Pending.AnalyticModificationJacobianMultiplierGerms
