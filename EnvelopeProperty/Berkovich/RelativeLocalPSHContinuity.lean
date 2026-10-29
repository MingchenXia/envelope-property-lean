import EnvelopeProperty.Berkovich.SpectrumLocalPSH

/-! # Continuity and upper semicontinuity of the actual relative local psh definitions -/
open scoped NNReal Topology
open Topology Filter Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {v : Valuation R ℝ≥0}

/-- Every actual intrinsic convex PL value is finite above on its ORIGINAL domain. -/
theorem IsConvexPLOn.ne_top {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, n, a, s, hs, _, hform⟩ := hu x hx
  rw [hform x hxW]
  exact EReal.coe_ne_top _

/-- Every actual intrinsic convex PL value is finite below on its ORIGINAL domain. -/
theorem IsConvexPLOn.ne_bot {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊥ := by
  obtain ⟨W, _, hxW, _, n, a, s, hs, _, hform⟩ := hu x hx
  rw [hform x hxW]
  exact EReal.coe_ne_bot _

/-- Genuine original ring evaluations prove continuity at every original domain point. -/
theorem IsConvexPLOn.continuousAt {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : ContinuousAt u x := by
  obtain ⟨W,hW,hxW,_,n,a,s,hs,ha,hform⟩ := hu x hx
  have hlog (i : Fin n) : ContinuousAt (fun y : RelativeSpectrum v A =>
      Real.log (y.1.val (a i) : ℝ)) x :=
    (NNReal.continuous_coe.comp ((Spectrum.continuous_abs (a i)).comp continuous_subtype_val)).continuousAt.log
      (NNReal.coe_ne_zero.mpr (ha x hxW i))
  have htrop (p) : ContinuousAt (fun y => tropAffine a p y) x :=
    (tendsto_finsetSum Finset.univ (fun i _ => continuousAt_const.mul (hlog i))).add continuousAt_const
  have hcont : ContinuousAt (fun y => ((s.sup' hs (fun p => tropAffine a p y) : ℝ) : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp (ContinuousAt.finset_sup'_apply hs (fun p _ => htrop p))
  exact hcont.congr (Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) (fun y hy => (hform y hy).symm))

/-- The ORIGINAL convex PL function is continuous on its whole true domain. -/
theorem IsConvexPLOn.continuousOn {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsConvexPLOn U u) : ContinuousOn u U :=
  fun _ hx => (hu.continuousAt hx).continuousWithinAt

/-- The actual ORIGINAL infimum is bounded by a finite first term, so positive infinity is excluded. -/
theorem IsDecrConvexPLLimitOn.ne_top {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsDecrConvexPLLimitOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨w, hw, _, hlim⟩ := hu
  apply ne_of_lt
  calc
    u x = ⨅ j, w j x := hlim x hx
    _ ≤ w 0 x := iInf_le _ 0
    _ < ⊤ := lt_top_iff_ne_top.mpr ((hw 0).ne_top hx)

/-- Every actual pointwise decreasing convex PL limit is genuinely upper semicontinuous, including minus infinity. -/
theorem IsDecrConvexPLLimitOn.upperSemicontinuousOn {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsDecrConvexPLLimitOn U u) :
    UpperSemicontinuousOn u U := by
  obtain ⟨w, hw, _, hlim⟩ := hu
  intro x hx c hc
  change u x < c at hc
  rw [hlim x hx] at hc
  obtain ⟨j, hj⟩ := iInf_lt_iff.1 hc
  have hev : ∀ᶠ y in 𝓝 x, w j y < c :=
    ((hw j).continuousAt hx).eventually (gt_mem_nhds hj)
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hev, self_mem_nhdsWithin]
    with y hy hyU
  rw [hlim y hyU]
  exact (iInf_le _ j).trans_lt hy

/-- The SAME intrinsic local function never takes positive infinity on its genuine domain. -/
theorem IsLocallyPSHOn.ne_top {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsLocallyPSHOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, hw⟩ := hu x hx
  exact hw.ne_top hxW

/-- True original local neighborhoods and infima imply upper semicontinuity of the actual local-psh function. -/
theorem IsLocallyPSHOn.upperSemicontinuousOn {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsLocallyPSHOn U u) :
    UpperSemicontinuousOn u U := by
  intro x hx c hc
  obtain ⟨W, hW, hxW, _, hw⟩ := hu x hx
  have hev := hw.upperSemicontinuousOn x hxW c hc
  have hle : 𝓝 x ≤ 𝓝[W] x := by
    change 𝓝 x ≤ 𝓝 x ⊓ Filter.principal W
    exact le_inf le_rfl (Filter.le_principal_iff.mpr (hW.mem_nhds hxW))
  exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds.trans hle) hev

end EnvelopeProperty.Berkovich.RelativeSpectrum
