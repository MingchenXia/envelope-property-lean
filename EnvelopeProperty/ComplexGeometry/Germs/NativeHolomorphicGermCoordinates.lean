import EnvelopeProperty.ComplexGeometry.Germs.NativeHolomorphicGermRing
import EnvelopeProperty.ComplexGeometry.Pluripotential.HolomorphicMaps
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HironakaHolomorphicJetChartInvariance

/-! # Actual centered-chart composition of whole native holomorphic germs -/

set_option autoImplicit false

noncomputable section

namespace HolomorphicGerms.NativeHolGerm

open Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicMaps HironakaHolomorphicJetChartInvariance
open scoped Topology Manifold ContDiff

variable {k n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel k) N] [IsComplexManifold k N]

/-- The literal original map in the existing centered source and target charts. -/
def centeredCoordinateMap (b : N → M) (y : N) (z : ComplexModel k) : ComplexModel n :=
  coordinateMap b (complexChartAt (n := k) y) (complexChartAt (n := n) (b y))
    (z + (complexChartAt (n := k) y).val y) - (complexChartAt (n := n) (b y)).val (b y)

omit [IsComplexManifold n M] [IsComplexManifold k N] in
/-- The actual map fixes the genuine chart center. -/
theorem centeredCoordinateMap_zero (b : N → M) (y : N) :
    centeredCoordinateMap (k := k) (n := n) b y 0 = 0 := by
  simp only [centeredCoordinateMap, zero_add,
    coordinateMap_at (mem_complexChartAt_source (n := k) y), sub_self]

omit [IsComplexManifold n M] [IsComplexManifold k N] in
private theorem centeredDomain_eventually (b : N → M)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel k),
      z + (complexChartAt (n := k) y).val y ∈
        coordinateDomain b (complexChartAt (n := k) y) (complexChartAt (n := n) (b y)) := by
  have hAdd : Tendsto (fun z : ComplexModel k => z + (complexChartAt (n := k) y).val y)
      (𝓝 0) (𝓝 ((complexChartAt (n := k) y).val y)) := by
    simpa only [zero_add] using
      (continuous_add_const ((complexChartAt (n := k) y).val y)).tendsto (0 : ComplexModel k)
  exact hAdd.eventually ((coordinateDomain_isOpen hb _ _).mem_nhds
    (mem_coordinateDomain (mem_complexChartAt_source (n := k) y) (mem_complexChartAt_source (n := n) (b y))))

/-- Actual near-origin holomorphy follows from the original map on its genuine chart domain. -/
theorem centeredCoordinateMap_holomorphic (b : N → M)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel k), DifferentiableAt ℂ (centeredCoordinateMap (k := k) (n := n) b y) z := by
  filter_upwards [centeredDomain_eventually b hb y] with z hz
  exact (((coordinateMap_contDiffAt hb _ _ hz).differentiableAt (by simp)).comp z
    (differentiableAt_id.add_const ((complexChartAt (n := k) y).val y))).sub_const _

/-- The whole actual native pullback is literal nonlinear composition in the actual centered charts. -/
theorem chartEquiv_comap (b : N → M)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N)
    (g : NativeHolGerm n M (b y)) :
    chartEquiv y (comap b hb y g) =
      compAlgHom (centeredCoordinateMap (k := k) (n := n) b y) (centeredCoordinateMap_holomorphic b hb y)
        (centeredCoordinateMap_zero b y) (chartEquiv (b y) g) := by
  obtain ⟨g, hg, rfl⟩ := exists_eq_mk g
  apply Subtype.ext
  change ((fun z : ComplexModel k => g (b ((complexChartAt (n := k) y).val.symm
    (z + (complexChartAt (n := k) y).val y)))) : Germ (𝓝 (0 : ComplexModel k)) ℂ) =
      ((fun z : ComplexModel k => g ((complexChartAt (n := n) (b y)).val.symm
        (centeredCoordinateMap (k := k) (n := n) b y z + (complexChartAt (n := n) (b y)).val (b y)))) :
          Germ (𝓝 (0 : ComplexModel k)) ℂ)
  apply Germ.coe_eq.mpr
  filter_upwards [centeredDomain_eventually b hb y] with z hz
  change g (b ((complexChartAt (n := k) y).val.symm (z + (complexChartAt (n := k) y).val y))) =
    g ((complexChartAt (n := n) (b y)).val.symm
      (((complexChartAt (n := n) (b y)).val
        (b ((complexChartAt (n := k) y).val.symm (z + (complexChartAt (n := k) y).val y))) -
          (complexChartAt (n := n) (b y)).val (b y)) + (complexChartAt (n := n) (b y)).val (b y)))
  rw [sub_add_cancel, (complexChartAt (n := n) (b y)).val.left_inv hz.2]

end HolomorphicGerms.NativeHolGerm
