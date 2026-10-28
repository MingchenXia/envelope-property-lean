/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeConvexPLAlgebra
import EnvelopeProperty.Berkovich.SchemeLocalPSHContinuity
import EnvelopeProperty.ERealAntitoneLimits

/-! # Actual decreasing and local intrinsic regular-unit presentation algebra -/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U V : Set (RelativeSchemeValuedPoint v f)}
  {u w : RelativeSchemeValuedPoint v f → EReal}

/-- An actual decreasing presentation has a genuinely open original domain. -/
theorem IsDecrConvexPLLimitOn.isOpen (hu : IsDecrConvexPLLimitOn U u) : IsOpen U := by
  obtain ⟨a, ha, _⟩ := hu
  exact (ha 0).isOpen

/-- Restrict every original sequence term to the same genuine open subset. -/
theorem IsDecrConvexPLLimitOn.mono (hu : IsDecrConvexPLLimitOn U u) (hV : IsOpen V)
    (hVU : V ⊆ U) : IsDecrConvexPLLimitOn V u := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨a, fun j => (ha j).mono hV hVU,
    fun y hy => hanti y (hVU hy), fun y hy => hlim y (hVU hy)⟩

/-- Domainwise equality preserves the SAME genuine decreasing sequence. -/
theorem IsDecrConvexPLLimitOn.congr (hu : IsDecrConvexPLLimitOn U u)
    (heq : ∀ y ∈ U, u y = w y) : IsDecrConvexPLLimitOn U w := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨a, ha, hanti, fun y hy => (heq y hy).symm.trans (hlim y hy)⟩

/-- The constant original sequence is a true decreasing presentation. -/
theorem IsConvexPLOn.isDecrConvexPLLimitOn (hu : IsConvexPLOn U u) :
    IsDecrConvexPLLimitOn U u := by
  exact ⟨fun _ => u, fun _ => hu, fun _ _ => antitone_const, fun _ _ => by simp⟩

/-- An actual decreasing presentation gives local presentations on its genuine open domain. -/
theorem IsDecrConvexPLLimitOn.isLocallyPSHOn (hu : IsDecrConvexPLLimitOn U u) :
    IsLocallyPSHOn U u := fun _ hx => ⟨U, hu.isOpen, hx, subset_rfl, hu⟩

/-- The original pointwise maximum is the infimum of the genuine termwise maxima. -/
theorem IsDecrConvexPLLimitOn.max (hu : IsDecrConvexPLLimitOn U u)
    (hw : IsDecrConvexPLLimitOn U w) :
    IsDecrConvexPLLimitOn U (fun y => max (u y) (w y)) := by
  obtain ⟨a, ha, haa, hau⟩ := hu
  obtain ⟨b, hb, hbb, hbw⟩ := hw
  refine ⟨fun j y => Max.max (a j y) (b j y), fun j => (ha j).max (hb j),
    fun y hy _ _ hij => max_le_max (haa y hy hij) (hbb y hy hij), fun y hy => ?_⟩
  change Max.max (u y) (w y) = ⨅ j, Max.max (a j y) (b j y)
  rw [hau y hy, hbw y hy, iInf_max_of_antitone (haa y hy) (hbb y hy)]

/-- Actual finite first terms exclude mixed infinities in the ORIGINAL sum limit. -/
theorem IsDecrConvexPLLimitOn.add (hu : IsDecrConvexPLLimitOn U u)
    (hw : IsDecrConvexPLLimitOn U w) :
    IsDecrConvexPLLimitOn U (fun y => u y + w y) := by
  obtain ⟨a, ha, haa, hau⟩ := hu
  obtain ⟨b, hb, hbb, hbw⟩ := hw
  refine ⟨fun j y => a j y + b j y, fun j => (ha j).add (hb j),
    fun y hy _ _ hij => add_le_add (haa y hy hij) (hbb y hy hij), fun y hy => ?_⟩
  change u y + w y = ⨅ j, (a j y + b j y)
  rw [hau y hy, hbw y hy, iInf_add_of_antitone (haa y hy) (hbb y hy)
    ((ha 0).ne_top hy) ((hb 0).ne_top hy)]

/-- Positive rational factors commute with actual infima; zero uses the genuine zero sequence. -/
theorem IsDecrConvexPLLimitOn.smul (hu : IsDecrConvexPLLimitOn U u) {c : ℚ} (hc : 0 ≤ c) :
    IsDecrConvexPLLimitOn U (fun y => ((c : ℝ) : EReal) * u y) := by
  by_cases hc0 : c = 0
  · subst c
    simpa using (isConvexPLOn_const (v := v) (f := f) hu.isOpen 0).isDecrConvexPLLimitOn
  · obtain ⟨a, ha, hanti, hlim⟩ := hu
    have hc' : (0 : ℝ) < c := by exact_mod_cast lt_of_le_of_ne hc (Ne.symm hc0)
    refine ⟨fun j y => ((c : ℝ) : EReal) * a j y, fun j => (ha j).smul hc,
      fun y hy _ _ hij => mul_le_mul_of_nonneg_left (hanti y hy hij) (by exact_mod_cast hc),
      fun y hy => ?_⟩
    change ((c : ℝ) : EReal) * u y = ⨅ j, ((c : ℝ) : EReal) * a j y
    rw [hlim y hy, iInf_coe_mul_of_antitone (hanti y hy) hc']

/-- A REAL translate is represented by the original sequence plus genuine decreasing rational constants. -/
theorem IsDecrConvexPLLimitOn.add_const (hu : IsDecrConvexPLLimitOn U u) (c : ℝ) :
    IsDecrConvexPLLimitOn U (fun y => u y + (c : EReal)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  obtain ⟨q, hq, _, hqinf⟩ := exists_antitone_rat_iInf_eq c
  have hq' : Antitone (fun j => (((q j : ℚ) : ℝ) : EReal)) := by
    intro i j hij
    change (((q j : ℚ) : ℝ) : EReal) ≤ (((q i : ℚ) : ℝ) : EReal)
    exact_mod_cast hq hij
  refine ⟨fun j y => a j y + (((q j : ℚ) : ℝ) : EReal),
    fun j => (ha j).add_const (q j),
    fun y hy _ _ hij => add_le_add (hanti y hy hij) (hq' hij), fun y hy => ?_⟩
  change u y + (c : EReal) = ⨅ j, (a j y + (((q j : ℚ) : ℝ) : EReal))
  rw [iInf_add_of_antitone (hanti y hy) hq' ((ha 0).ne_top hy) (EReal.coe_ne_top _),
    ← hlim y hy, hqinf]

/-- Every finite REAL constant has a genuine decreasing rational presentation. -/
theorem isDecrConvexPLLimitOn_const (hU : IsOpen U) (c : ℝ) :
    IsDecrConvexPLLimitOn U (fun _ => (c : EReal)) := by
  simpa using (isConvexPLOn_const (v := v) (f := f) hU 0).isDecrConvexPLLimitOn.add_const c

/-- Finite sums use the ORIGINAL actual decreasing functions, including the empty sum. -/
theorem isDecrConvexPLLimitOn_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → RelativeSchemeValuedPoint v f → EReal) (hU : IsOpen U)
    (hF : ∀ i ∈ s, IsDecrConvexPLLimitOn U (F i)) :
    IsDecrConvexPLLimitOn U (fun y => ∑ i ∈ s, F i y) := by
  revert hF
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using isDecrConvexPLLimitOn_const (v := v) (f := f) hU 0
  | @insert i s hi ih =>
    intro hF
    have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hF i (Finset.mem_insert_self i s)).add hs

/-- Every actual finite nonempty maximum preserves the original decreasing-limit class. -/
theorem isDecrConvexPLLimitOn_finset_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (F : ι → RelativeSchemeValuedPoint v f → EReal)
    (hF : ∀ i ∈ s, IsDecrConvexPLLimitOn U (F i)) :
    IsDecrConvexPLLimitOn U (fun y => s.sup' hs (fun i => F i y)) := by
  revert hs hF
  induction s using Finset.induction_on with
  | empty => intro hs; simp at hs
  | @insert i s hi ih =>
    intro hs hF
    by_cases hs' : s.Nonempty
    · have htail := ih hs' (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sup'_insert hs'] using (hF i (Finset.mem_insert_self i s)).max htail
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using hF i (Finset.mem_insert_self i ∅)

/-- The genuine original local-presentation neighborhoods cover its exact domain. -/
theorem IsLocallyPSHOn.isOpen (hu : IsLocallyPSHOn U u) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, hWU, _⟩ := hu x hx
  exact ⟨W, hWU, hW, hxW⟩

/-- Open restriction takes actual finite intersections, without any common countable neighborhood. -/
theorem IsLocallyPSHOn.mono (hu : IsLocallyPSHOn U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsLocallyPSHOn V u := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x (hVU hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, Set.inter_subset_right,
    hlim.mono (hW.inter hV) Set.inter_subset_left⟩

/-- Original domainwise equality changes only the SAME function's limit identity. -/
theorem IsLocallyPSHOn.congr (hu : IsLocallyPSHOn U u) (heq : ∀ y ∈ U, u y = w y) :
    IsLocallyPSHOn U w := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, hlim.congr (fun y hy => heq y (hWU hy))⟩

/-- True local presentations glue through their actual original open neighborhoods. -/
theorem isLocallyPSHOn_of_local
    (h : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsLocallyPSHOn V u) :
    IsLocallyPSHOn U u := by
  intro x hx
  obtain ⟨V, _, hxV, hVU, hv⟩ := h x hx
  obtain ⟨W, hW, hxW, hWV, hlim⟩ := hv x hxV
  exact ⟨W, hW, hxW, hWV.trans hVU, hlim⟩

/-- The maximum uses a genuine intersection of TWO original local sequence neighborhoods. -/
theorem IsLocallyPSHOn.max (hu : IsLocallyPSHOn U u) (hw : IsLocallyPSHOn U w) :
    IsLocallyPSHOn U (fun y => max (u y) (w y)) := by
  intro x hx
  obtain ⟨V₁, hV₁, hxV₁, hV₁U, hu'⟩ := hu x hx
  obtain ⟨V₂, hV₂, hxV₂, _, hw'⟩ := hw x hx
  exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hxV₁, hxV₂⟩, Set.inter_subset_left.trans hV₁U,
    (hu'.mono (hV₁.inter hV₂) Set.inter_subset_left).max
      (hw'.mono (hV₁.inter hV₂) Set.inter_subset_right)⟩

/-- Actual local decreasing sums retain the ORIGINAL functions, including negative infinity. -/
theorem IsLocallyPSHOn.add (hu : IsLocallyPSHOn U u) (hw : IsLocallyPSHOn U w) :
    IsLocallyPSHOn U (fun y => u y + w y) := by
  intro x hx
  obtain ⟨V₁, hV₁, hxV₁, hV₁U, hu'⟩ := hu x hx
  obtain ⟨V₂, hV₂, hxV₂, _, hw'⟩ := hw x hx
  exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hxV₁, hxV₂⟩, Set.inter_subset_left.trans hV₁U,
    (hu'.mono (hV₁.inter hV₂) Set.inter_subset_left).add
      (hw'.mono (hV₁.inter hV₂) Set.inter_subset_right)⟩

/-- Genuine nonnegative rational multiplication preserves every local sequence presentation. -/
theorem IsLocallyPSHOn.smul (hu : IsLocallyPSHOn U u) {c : ℚ} (hc : 0 ≤ c) :
    IsLocallyPSHOn U (fun y => ((c : ℝ) : EReal) * u y) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, hlim.smul hc⟩

/-- Every finite REAL translate is genuinely local, with rational approximants on each original neighborhood. -/
theorem IsLocallyPSHOn.add_const (hu : IsLocallyPSHOn U u) (c : ℝ) :
    IsLocallyPSHOn U (fun y => u y + (c : EReal)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, hlim.add_const c⟩

/-- Every finite REAL constant belongs to the actual intrinsic local class on an original open domain. -/
theorem isLocallyPSHOn_const (hU : IsOpen U) (c : ℝ) :
    IsLocallyPSHOn U (fun _ => (c : EReal)) :=
  (isDecrConvexPLLimitOn_const hU c).isLocallyPSHOn

/-- Actual finite sums preserve intrinsic local presentations, including the zero empty sum. -/
theorem isLocallyPSHOn_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → RelativeSchemeValuedPoint v f → EReal) (hU : IsOpen U)
    (hF : ∀ i ∈ s, IsLocallyPSHOn U (F i)) :
    IsLocallyPSHOn U (fun y => ∑ i ∈ s, F i y) := by
  revert hF
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using isLocallyPSHOn_const (v := v) (f := f) hU 0
  | @insert i s hi ih =>
    intro hF
    have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hF i (Finset.mem_insert_self i s)).add hs

/-- Actual finite nonempty maxima preserve the WHOLE original local functions. -/
theorem isLocallyPSHOn_finset_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (F : ι → RelativeSchemeValuedPoint v f → EReal)
    (hF : ∀ i ∈ s, IsLocallyPSHOn U (F i)) :
    IsLocallyPSHOn U (fun y => s.sup' hs (fun i => F i y)) := by
  revert hs hF
  induction s using Finset.induction_on with
  | empty => intro hs; simp at hs
  | @insert i s hi ih =>
    intro hs hF
    by_cases hs' : s.Nonempty
    · have htail := ih hs' (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sup'_insert hs'] using (hF i (Finset.mem_insert_self i s)).max htail
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using hF i (Finset.mem_insert_self i ∅)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
