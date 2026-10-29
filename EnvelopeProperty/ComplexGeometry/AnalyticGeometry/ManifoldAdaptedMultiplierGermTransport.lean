import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.LocalHolomorphicMultiplierGermCovariance
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.ManifoldFiniteSpanChartTransport

set_option autoImplicit false

/-! # Original bounded analytic germs and arbitrary tests in adapted coordinates

Actual local inverses preserve bounded logarithmic presentations, the literal
preferred multiplier reader and nonzero original holomorphic tests. No mass,
nondegeneracy, continuous remainder or coordinate-integrability certificate is
an input. Reference: Demailly, *Analytic Methods in Algebraic Geometry*,
multiplier ideals; *Complex Analytic and Differential Geometry*, local charts.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold

namespace ComplexGeometry.AnalyticGeometry.ManifoldAdaptedMultiplierGermTransport

open Pluripotential Pluripotential.HolomorphicIdealSheaves

noncomputable section

/-- The actual inverse preserves the original family and merely bounded remainder. -/
theorem logarithmicTypeAt_comp_inv {n s : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p)
    {u : ComplexModel n → EReal} {r : ℝ} {G : Fin s → ComplexModel n → ℂ}
    (htype : LogarithmicTypeAt u r G p) :
    LogarithmicTypeAt (fun z => u (Φ.invFun z)) r
      (fun i z => G i (Φ.invFun z)) (Φ.toFun p) := by
  obtain ⟨hr, ⟨U, hU, hpU, hG⟩, b, hb, heq⟩ := htype
  have hq : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have hinv := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)
  have ht : Tendsto Φ.invFun (𝓝 (Φ.toFun p)) (𝓝 p) := by
    simpa only [Φ.left_inv p Φ.center_mem_source] using hinv.continuousAt.tendsto
  have hbound : BoundedRealGermAt (fun z => b (Φ.invFun z)) (Φ.toFun p) :=
    (show BoundedRealGermAt b (Φ.invFun (Φ.toFun p)) from
      by simpa only [Φ.left_inv p Φ.center_mem_source] using hb).comp_continuousAt
        hinv.continuousAt
  refine ⟨hr, ⟨Φ.target ∩ Φ.invFun ⁻¹' U, ?_, ?_, ?_⟩,
    fun z => b (Φ.invFun z), hbound, ?_⟩
  · exact Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target hU
  · exact ⟨hq, by simpa only [mem_preimage, Φ.left_inv p Φ.center_mem_source] using hpU⟩
  · intro i
    exact (hG i).comp (Φ.invFun_holomorphic.mono inter_subset_left) fun _ hz => hz.2
  · filter_upwards [ht.eventually heq] with z hz
    rw [hz]
    rfl

/-- The original preferred multiplier reader is exactly the adapted weighted germ. -/
theorem multiplierIdeal_mem_comp_adapted_iff {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    {F : M → ℂ} (hF : HolomorphicAt n F x) (c : ℝ) :
    (multiplierIdeal (n := n) c u).mem x F ↔
      MultiplierIntegrableAt
        (fun z => u ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) c
        (fun z => F ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) 0 volume := by
  have hw := hu (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val x)
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))
  have h := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    Φ (f := fun z => F ((complexChartAt (n := n) x).val.symm z)) (c := c) hw
  change (HolomorphicAt n F x ∧ MultiplierIntegrableAt _ c _ _ volume) ↔ _
  constructor
  · intro hf
    simpa only [h0, chartFunction] using h.mpr hf.2
  · intro hf
    exact ⟨hF, h.mp (by simpa only [h0, chartFunction] using hf)⟩

/-- Every original nonzero holomorphic germ remains a nonzero adapted germ,
without imposing a unit condition or any restriction on its extra zeros. -/
theorem holomorphic_nonzero_comp_adapted {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : M → ℂ} (hF : HolomorphicAt n F x) (hFnon : ∃ᶠ y in 𝓝 x, F y ≠ 0) :
    (∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z) ∧
    (∃ᶠ z in 𝓝 (0 : ComplexModel n),
      F ((chartAt (ComplexModel n) x).symm (Φ.invFun z)) ≠ 0) := by
  have hspan := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp
      (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF)
  refine ⟨hspan.1.mono fun _ hz => hz.differentiableAt, ?_⟩
  let e := chartAt (ComplexModel n) x
  have he : Tendsto e (𝓝 x) (𝓝 (e x)) :=
    (e.continuousAt (mem_chart_source (ComplexModel n) x)).tendsto
  have hto : Tendsto Φ.toFun (𝓝 (e x)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [h0] using (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.tendsto
  change ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),
    ¬F (e.symm (Φ.invFun z)) ≠ 0
  intro hzero
  have hround : ∀ᶠ y in 𝓝 x, F y = 0 := by
    filter_upwards [(hto.comp he).eventually hzero,
      he.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source),
      e.open_source.mem_nhds (mem_chart_source (ComplexModel n) x)] with y hy hys hye
    have hz : F (e.symm (Φ.invFun (Φ.toFun (e y)))) = 0 := not_ne_iff.mp hy
    simpa only [Φ.left_inv (e y) hys, e.left_inv hye] using hz
  exact (hFnon.and_eventually hround).exists.elim fun _ h => h.1 h.2

end
end ComplexGeometry.AnalyticGeometry.ManifoldAdaptedMultiplierGermTransport
