/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeModelIdealContinuity
import EnvelopeProperty.Berkovich.SchemeModelIdealSupport
import Mathlib.Topology.NoetherianSpace

/-!
# Genuine center anti-continuity with explicit finiteness scope

Actual quasi-compact opens have closed true-center inverse images.
Topological Noetherianity supplies this for every scheme open and gives
full anti-continuity. Genuine affine finite generation and continuous model
norms separately give open center inverse images of actual ideal supports.
No unrestricted infinite-open or infinite-supremum strict-gap claim is made.
-/


open scoped NNReal Topology
open Topology TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The inverse image under the true center of every quasi-compact scheme open is closed. -/
theorem isClosed_center_preimage_of_isCompact [IsProper f] (hb : ∀ r, v r ≤ 1)
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsClosed ((center (v := v) (f := f) hb) ⁻¹' (U : Set X)) := by
  obtain ⟨S, hS, hcov⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  rw [hcov]
  simp only [Set.preimage_iUnion]
  exact hS.isClosed_biUnion fun i _ => isClosed_center_preimage_affine hb i

/-- On a topologically Noetherian model, every true center inverse image of an open is closed. -/
theorem isClosed_center_preimage_of_noetherian [IsProper f] [NoetherianSpace X]
    (hb : ∀ r, v r ≤ 1) (U : X.Opens) :
    IsClosed ((center (v := v) (f := f) hb) ⁻¹' (U : Set X)) :=
  isClosed_center_preimage_of_isCompact hb U (NoetherianSpace.isCompact _)

/-- Genuine center anti-continuity on a topologically Noetherian proper model sends closed sets to open inverse images. -/
theorem isOpen_center_preimage_of_isClosed [IsProper f] [NoetherianSpace X]
    (hb : ∀ r, v r ≤ 1) (C : Set X) (hC : IsClosed C) :
    IsOpen ((center (v := v) (f := f) hb) ⁻¹' C) := by
  have h := isClosed_center_preimage_of_noetherian (v := v) (f := f) hb ⟨Cᶜ, hC.isOpen_compl⟩
  change IsClosed ((center (v := v) (f := f) hb) ⁻¹' Cᶜ) at h
  simpa only [Set.preimage_compl, compl_compl] using h.isOpen_compl

/-- Actual local finite generation gives the strict-value criterion for genuine ideal support at the TRUE center. -/
theorem modelIdealNorm_lt_one_iff_of_fg [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (hfg : ∀ U : X.affineOpens, (I.ideal U).FG)
    (y : RelativeSchemeValuedPoint v f) : modelIdealNorm I hb y < 1 ↔ center hb y ∈ I.support := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := center hb y) trivial
  obtain ⟨S, hS⟩ := hfg ⟨U, hU⟩
  exact modelIdealNorm_lt_one_iff_of_generators I hb y ⟨U, hU⟩ hy S hS.symm

/-- Genuine finitely generated ideal supports have open center inverse images, without a Noetherian hypothesis. -/
theorem isOpen_center_preimage_idealSupport_of_fg [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsOpen ((center (v := v) (f := f) hb) ⁻¹' (I.support : Set X)) := by
  have he : (center (v := v) (f := f) hb) ⁻¹' (I.support : Set X) =
      {y : RelativeSchemeValuedPoint v f | modelIdealNorm I hb y < 1} := by
    ext y
    exact (modelIdealNorm_lt_one_iff_of_fg I hb hfg y).symm
  rw [he]
  exact isOpen_lt (continuous_modelIdealNorm_of_fg I hb hfg) continuous_const
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
