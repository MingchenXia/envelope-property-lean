/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumLocalPSH
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Local.Defs

open scoped NNReal Topology
open Topology Classical
noncomputable section
namespace EnvelopeProperty
open Berkovich
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The independent finite-coefficient class specializes to the UNCHANGED original trivial-field convex-PL class. -/
theorem isConvexPLOn_relativeSpectrum_iff
    {U : Set (RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A)}
    {u : RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A → EReal} :
    RelativeSpectrum.IsConvexPLOn U u ↔ IsConvexPLOn (Berk.relativeSpectrumHomeomorph ⁻¹' U)
      (fun y => u (Berk.relativeSpectrumHomeomorph y)) := by
  constructor
  · intro hu x hx
    obtain ⟨W, hW, hxW, hWU, n, a, s, hs, ha, hform⟩ := hu (Berk.relativeSpectrumHomeomorph x) hx
    exact ⟨Berk.relativeSpectrumHomeomorph ⁻¹' W, hW.preimage Berk.relativeSpectrumHomeomorph.continuous,
      hxW, Set.preimage_mono hWU, n, a, s, hs, (fun y hy i => ha _ hy i), fun y hy => hform _ hy⟩
  · intro hu x hx
    obtain ⟨W, hW, hxW, hWU, n, a, s, hs, ha, hform⟩ := hu
      (Berk.relativeSpectrumHomeomorph.symm x) (by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hx)
    refine ⟨Berk.relativeSpectrumHomeomorph.symm ⁻¹' W, hW.preimage Berk.relativeSpectrumHomeomorph.symm.continuous,
      hxW, (fun y hy => by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hWU hy), n, a, s, hs,
      (fun y hy i => ha _ hy i), ?_⟩
    intro y hy
    simpa only [Homeomorph.apply_symm_apply, tropAffine, RelativeSpectrum.tropAffine, Berk.relativeSpectrumHomeomorph_symm_val] using hform (Berk.relativeSpectrumHomeomorph.symm y) hy

/-- Actual whole decreasing sequences specialize to the unchanged OLD class. -/
theorem isDecrConvexPLLimitOn_relativeSpectrum_iff
    {U : Set (RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A)}
    {u : RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A → EReal} :
    RelativeSpectrum.IsDecrConvexPLLimitOn U u ↔ IsDecrConvexPLLimitOn (Berk.relativeSpectrumHomeomorph ⁻¹' U)
      (fun y => u (Berk.relativeSpectrumHomeomorph y)) := by
  constructor
  · rintro ⟨a, ha, hanti, hlim⟩
    exact ⟨fun j y => a j (Berk.relativeSpectrumHomeomorph y),
      fun j => isConvexPLOn_relativeSpectrum_iff.mp (ha j), fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩
  · rintro ⟨a, ha, hanti, hlim⟩
    refine ⟨fun j y => a j (Berk.relativeSpectrumHomeomorph.symm y), ?_, ?_, ?_⟩
    · intro j
      apply isConvexPLOn_relativeSpectrum_iff.mpr
      simpa only [Homeomorph.symm_apply_apply] using ha j
    · intro y hy
      exact hanti _ (by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hy)
    · intro y hy
      simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hlim (Berk.relativeSpectrumHomeomorph.symm y)
        (by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hy)

/-- The independently defined actual prescribed class equals the unchanged OLD local-psh class at trivial k. -/
theorem isLocallyPSHOn_relativeSpectrum_iff
    {U : Set (RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A)}
    {u : RelativeSpectrum (1 : _root_.Valuation k ℝ≥0) A → EReal} :
    RelativeSpectrum.IsLocallyPSHOn U u ↔ IsLocallyPSHOn (Berk.relativeSpectrumHomeomorph ⁻¹' U)
      (fun y => u (Berk.relativeSpectrumHomeomorph y)) := by
  constructor
  · intro hu x hx
    obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (Berk.relativeSpectrumHomeomorph x) hx
    exact ⟨Berk.relativeSpectrumHomeomorph ⁻¹' W, hW.preimage Berk.relativeSpectrumHomeomorph.continuous,
      hxW, Set.preimage_mono hWU, isDecrConvexPLLimitOn_relativeSpectrum_iff.mp hloc⟩
  · intro hu x hx
    obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (Berk.relativeSpectrumHomeomorph.symm x)
      (by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hx)
    refine ⟨Berk.relativeSpectrumHomeomorph.symm ⁻¹' W, hW.preimage Berk.relativeSpectrumHomeomorph.symm.continuous,
      hxW, (fun y hy => by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hWU hy), ?_⟩
    apply isDecrConvexPLLimitOn_relativeSpectrum_iff.mpr
    simpa only [Set.preimage_preimage, Function.comp_def, Homeomorph.symm_apply_apply, Set.preimage_id'] using hloc

end EnvelopeProperty
