/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Topology.LocalAtTarget


/-!
# Genuine locality of proper maps at an open target cover

For actually continuous maps of arbitrary topological spaces, properness is
local at the target. Real closed-map locality and compactness of each whole
fibre prove this criterion without separation or local compactness.
-/

open Set Topology TopologicalSpace

namespace EnvelopeProperty

/-- For an actually continuous map, properness is local on any open cover of its target. -/
theorem isProperMap_iff_restrictPreimage_of_openCover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {ι : Type*} {U : ι → Opens Y} (hU : IsOpenCover U) (hf : Continuous f) :
    IsProperMap f ↔ ∀ i, IsProperMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, fun h => ?_⟩
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf, hU.isClosedMap_iff_restrictPreimage.mpr (fun i => (h i).isClosedMap), ?_⟩
  intro y
  obtain ⟨i, hy⟩ := hU.exists_mem y
  have hc := ((h i).isCompact_preimage (isCompact_singleton (x := (⟨y, hy⟩ : U i)))).image
    (continuous_subtype_val : Continuous ((↑) : (f ⁻¹' U i) → X))
  have he : Subtype.val '' (U i).1.restrictPreimage f ⁻¹' {(⟨y, hy⟩ : U i)} =
      f ⁻¹' {y} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hx
      change f x = y at hx
      refine ⟨⟨x, by change f x ∈ U i; rw [hx]; exact hy⟩, Subtype.ext hx, rfl⟩
  exact he ▸ hc

end EnvelopeProperty
