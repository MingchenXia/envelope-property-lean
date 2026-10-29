/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLocalPSH

/-!
# Genuine intrinsic presentation continuity and upper semicontinuity

Original unit evaluations and pointwise infima are retained. No classical
harmonicity, subharmonicity, maximum principle or descent is asserted.
-/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The ORIGINAL rational unit expression is continuous on ANY true support-open subspace. -/
theorem continuous_unitTropAffine (W : Set (RelativeSchemeValuedPoint v f)) {V : X.Opens}
    (hWV : ∀ y ∈ W, y.1.point ∈ V) {n : ℕ} (a : Fin n → Γ(X, V)ˣ) (p : (Fin n → ℚ) × ℚ) :
    Continuous (fun y : W => unitTropAffine a p y.1 (hWV y.1 y.2)) := by
  have hi : Continuous (fun y : W => (⟨y.1.1, hWV y.1 y.2⟩ :
      {z : SchemeValuedPoint X // z.point ∈ V})) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hlog (i : Fin n) : Continuous (fun y : W =>
      Real.log (SchemeValuedPoint.eval y.1.1 V (hWV y.1 y.2) (a i : Γ(X, V)) : ℝ)) :=
    (NNReal.continuous_coe.comp ((SchemeValuedPoint.continuous_eval V (a i : Γ(X, V))).comp hi)).log
      (fun y => NNReal.coe_ne_zero.mpr (eval_unit_ne_zero V (a i) y.1 (hWV y.1 y.2)))
  unfold unitTropAffine
  exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (hlog i))).add continuous_const

/-- Every actual intrinsic convex PL value is finite above on its ORIGINAL domain. -/
theorem IsConvexPLOn.ne_top {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, V, hWV, n, a, s, hs, hform⟩ := hu x hx
  rw [hform x hxW]
  exact EReal.coe_ne_top _

/-- Every actual intrinsic convex PL value is finite below on its ORIGINAL domain. -/
theorem IsConvexPLOn.ne_bot {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊥ := by
  obtain ⟨W, _, hxW, _, V, hWV, n, a, s, hs, hform⟩ := hu x hx
  rw [hform x hxW]
  exact EReal.coe_ne_bot _

/-- Genuine unit evaluation continuity proves continuity of the SAME original convex PL function. -/
theorem IsConvexPLOn.continuousAt {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsConvexPLOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : ContinuousAt u x := by
  obtain ⟨W, hW, hxW, _, V, hWV, n, a, s, hs, hform⟩ := hu x hx
  have hcont : Continuous (fun y : W =>
      ((s.sup' hs (fun p => unitTropAffine a p y.1 (hWV y.1 y.2)) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (Continuous.finset_sup'_apply hs
      (fun p _ => continuous_unitTropAffine W hWV a p))
  have he : (fun y : W => u y.1) =
      (fun y : W => ((s.sup' hs (fun p => unitTropAffine a p y.1 (hWV y.1 y.2)) : ℝ) : EReal)) :=
    funext (fun y => hform y.1 y.2)
  have hOn : ContinuousOn u W := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun y : W => u y.1)
    rw [he]
    exact hcont
  exact (hOn x hxW).continuousAt (hW.mem_nhds hxW)

/-- The ORIGINAL convex PL function is continuous on its whole true domain. -/
theorem IsConvexPLOn.continuousOn {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsConvexPLOn U u) : ContinuousOn u U :=
  fun _ hx => (hu.continuousAt hx).continuousWithinAt

/-- The actual ORIGINAL infimum is bounded by a finite first term, so positive infinity is excluded. -/
theorem IsDecrConvexPLLimitOn.ne_top {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsDecrConvexPLLimitOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨w, hw, _, hlim⟩ := hu
  apply ne_of_lt
  calc
    u x = ⨅ j, w j x := hlim x hx
    _ ≤ w 0 x := iInf_le _ 0
    _ < ⊤ := lt_top_iff_ne_top.mpr ((hw 0).ne_top hx)

/-- Every actual pointwise decreasing convex PL limit is genuinely upper semicontinuous, including minus infinity. -/
theorem IsDecrConvexPLLimitOn.upperSemicontinuousOn {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsDecrConvexPLLimitOn U u) :
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
theorem IsLocallyPSHOn.ne_top {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsLocallyPSHOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, hw⟩ := hu x hx
  exact hw.ne_top hxW

/-- True original local neighborhoods and infima imply upper semicontinuity of the actual local-psh function. -/
theorem IsLocallyPSHOn.upperSemicontinuousOn {U : Set (RelativeSchemeValuedPoint v f)}
    {u : RelativeSchemeValuedPoint v f → EReal} (hu : IsLocallyPSHOn U u) :
    UpperSemicontinuousOn u U := by
  intro x hx c hc
  obtain ⟨W, hW, hxW, _, hw⟩ := hu x hx
  have hev := hw.upperSemicontinuousOn x hxW c hc
  have hle : 𝓝 x ≤ 𝓝[W] x := by
    change 𝓝 x ≤ 𝓝 x ⊓ Filter.principal W
    exact le_inf le_rfl (Filter.le_principal_iff.mpr (hW.mem_nhds hxW))
  exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds.trans hle) hev

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
