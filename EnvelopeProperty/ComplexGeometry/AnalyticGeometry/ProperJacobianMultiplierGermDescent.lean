import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.DemaillyApproximantDivisorialLelong
import EnvelopeProperty.ComplexGeometry.Pluripotential.HolomorphicMaps
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicWeightedImageChangeOfVariables
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.ProperFiberFiniteNeighborhoodCover
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.IEquivalentMax

set_option autoImplicit false

/-! # Actual proper-fiber descent of Jacobian-weighted local multiplier germs -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace ComplexGeometry.AnalyticGeometry.ProperJacobianMultiplierGermDescent

open Pluripotential Pluripotential.HolomorphicMaps DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong

noncomputable section

private theorem lintegral_biUnion_finset_lt_top
    {A B : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ≥0∞)
    (t : Finset B) (V : B → Set A)
    (hV : ∀ b ∈ t, ∫⁻ a in V b, f a ∂μ < ⊤) :
    ∫⁻ a in ⋃ b ∈ t, V b, f a ∂μ < ⊤ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert b t hb ih =>
      have heq : (⋃ a ∈ insert b t, V a) = V b ∪ ⋃ a ∈ t, V a := by
        ext a
        simp
      rw [heq]
      exact (lintegral_union_le f _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hV b (Finset.mem_insert_self _ _),
          ih (fun a ha => hV a (Finset.mem_insert_of_mem ha))⟩)

/-- An internally finite cover of the actual proper fiber descends the
literal Jacobian-weighted source germs to the original target germ. -/
theorem multiplierIntegrableAt_of_fiber_jacobian_germs
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hproper : IsProperMap π) (hsurj : Function.Surjective π)
    (hinj : IsInjectiveOffNull m π) (x : X)
    {w : ComplexModel (m + 1) → EReal} {g : ComplexModel (m + 1) → ℂ}
    {c : ℝ} (hc : 0 < c)
    (hw : QuasiPlurisubharmonicAt w ((complexChartAt (n := m + 1) x).val x))
    (hg : ∀ᶠ z in 𝓝 ((complexChartAt (n := m + 1) x).val x),
      DifferentiableAt ℂ g z)
    (hfiber : ∀ y : Y, π y = x →
      MultiplierIntegrableAt
        (fun z => w (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z)) c
        (fun z => g (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z) *
          complexJacobian (coordinateMap π (complexChartAt (n := m + 1) y)
            (complexChartAt (n := m + 1) x)) z)
        ((complexChartAt (n := m + 1) y).val y) volume) :
    MultiplierIntegrableAt w c g ((complexChartAt (n := m + 1) x).val x) volume := by
  classical
  let d := complexChartAt (n := m + 1) x
  let e (y : π ⁻¹' {x}) := complexChartAt (n := m + 1) (y : Y)
  let F (y : π ⁻¹' {x}) := coordinateMap π (e y) d
  have hfy (y : π ⁻¹' {x}) : π (y : Y) = x := mem_singleton_iff.mp y.property
  obtain ⟨S, hS, hπinj⟩ := hinj
  choose L hL hcenter hhol hint using fun y : π ⁻¹' {x} =>
    (hfiber (y : Y) (hfy y)).2
  let N (y : π ⁻¹' {x}) := L y ∩ coordinateDomain π (e y) d
  have hN (y : π ⁻¹' {x}) : IsOpen (N y) :=
    (hL y).inter (coordinateDomain_isOpen hπ (e y) d)
  have hyN (y : π ⁻¹' {x}) : (e y).val y ∈ N y := by
    refine ⟨hcenter y, mem_coordinateDomain (mem_chart_source _ _) ?_⟩
    rw [hfy y]
    exact mem_chart_source _ _
  let U (y : π ⁻¹' {x}) := (e y).val.source ∩ (e y).val ⁻¹' N y
  have hU (y : π ⁻¹' {x}) : IsOpen (U y) ∧ (y : Y) ∈ U y :=
    ⟨(e y).val.isOpen_inter_preimage (hN y), ⟨mem_chart_source _ _, hyN y⟩⟩
  have hfinite (y : π ⁻¹' {x}) :
      ∫⁻ z in F y '' N y, multiplierDensity w c g z < ⊤ := by
    let S' := (e y).val '' (S ∩ (e y).val.source)
    have hS' : volume S' = 0 := hS y
    have hF : DifferentiableOn ℂ (F y) (N y) := fun z hz =>
      (coordinateMap_contDiffAt hπ (e y) d hz.2).differentiableAt
        (by simp) |>.differentiableWithinAt
    have hFinj : InjOn (F y) (N y \ S') := by
      intro p hp q hq hpq
      have hpS : (e y).val.symm p ∉ S := by
        intro h
        apply hp.2
        exact ⟨(e y).val.symm p, ⟨h, (e y).val.map_target hp.1.2.1⟩,
          (e y).val.right_inv hp.1.2.1⟩
      have hqS : (e y).val.symm q ∉ S := by
        intro h
        apply hq.2
        exact ⟨(e y).val.symm q, ⟨h, (e y).val.map_target hq.1.2.1⟩,
          (e y).val.right_inv hq.1.2.1⟩
      have hpqπ : π ((e y).val.symm p) = π ((e y).val.symm q) :=
        d.val.injOn hp.1.2.2 hq.1.2.2 hpq
      have hpqe := hπinj hpS hqS hpqπ
      calc p = (e y).val ((e y).val.symm p) := ((e y).val.right_inv hp.1.2.1).symm
           _ = (e y).val ((e y).val.symm q) := congrArg (e y).val hpqe
           _ = q := (e y).val.right_inv hq.1.2.1
    rw [← HolomorphicWeightedImageChangeOfVariables.lintegral_multiplierDensity_comp_eq
      (hN y) hF hS' hFinj w c g]
    exact (lintegral_mono_set inter_subset_left).trans_lt (hint y).2
  obtain ⟨t, W, hW, hxW, _, hcover⟩ :=
    ProperFiberFiniteNeighborhoodCover.exists_finite_fiber_cover_target_neighborhood
      hproper hsurj x U hU
  let V := d.val '' (W ∩ d.val.source)
  have hV : IsOpen V := d.val.isOpen_image_of_subset_source (hW.inter d.val.open_source)
    inter_subset_right
  have hxV : d.val x ∈ V := ⟨x, ⟨hxW, mem_chart_source _ _⟩, rfl⟩
  have hVcover : V ⊆ ⋃ y ∈ t, F y '' N y := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, a, ha, hπa⟩ := mem_iUnion₂.mp (hcover hz.1)
    refine mem_iUnion₂.mpr ⟨y, hy, (e y).val a, ha.2, ?_⟩
    change d.val (π ((e y).val.symm ((e y).val a))) = d.val z
    rw [(e y).val.left_inv ha.1, hπa]
  have hVint : ∫⁻ z in V, multiplierDensity w c g z < ⊤ :=
    (lintegral_mono_set hVcover).trans_lt
      (lintegral_biUnion_finset_lt_top volume (multiplierDensity w c g) t
        (fun y => F y '' N y) (fun y _ => hfinite y))
  obtain ⟨Q, hQ, hxQ, hwQ⟩ := IEquivalentMax.exists_open_quasiPlurisubharmonicOn_of_at hw
  obtain ⟨P, hPsub, hP, hxP⟩ := _root_.mem_nhds_iff.mp hg
  let Z := (V ∩ Q) ∩ P
  have hZ : IsOpen Z := (hV.inter hQ).inter hP
  have hxZ : d.val x ∈ Z := ⟨⟨hxV, hxQ⟩, hxP⟩
  have hgZ : DifferentiableOn ℂ g Z := fun z hz =>
    (hPsub hz.2).differentiableWithinAt
  exact ⟨hc, Z, hZ, hxZ, hgZ,
    IEquivalentMax.aemeasurable_multiplierDensity_restrict hZ
      (hwQ.mono fun _ hz => hz.1.2) hc.ne' hgZ.continuousOn,
    (lintegral_mono_set (show Z ⊆ V from fun _ hz => hz.1.1)).trans_lt hVint⟩

end
end ComplexGeometry.AnalyticGeometry.ProperJacobianMultiplierGermDescent
