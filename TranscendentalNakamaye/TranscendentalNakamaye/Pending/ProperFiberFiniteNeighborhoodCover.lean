import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

/-! # A genuine finite fiber cover and target neighborhood supplied by actual properness -/

open Set
open scoped Topology

namespace TranscendentalNakamaye.Pending.ProperFiberFiniteNeighborhoodCover

/-- Compactness of the actual fiber and proper closedness supply the finite cover and target neighborhood. -/
theorem exists_finite_fiber_cover_target_neighborhood
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] {f : Y → X}
    (hf : IsProperMap f) (hsurj : Function.Surjective f) (x : X)
    (U : (f ⁻¹' {x}) → Set Y) (hU : ∀ y, IsOpen (U y) ∧ (y : Y) ∈ U y) :
    ∃ (t : Finset (f ⁻¹' {x})) (W : Set X), IsOpen W ∧ x ∈ W ∧
      f ⁻¹' W ⊆ ⋃ y ∈ t, U y ∧ W ⊆ ⋃ y ∈ t, f '' U y := by
  classical
  have hK : IsCompact (f ⁻¹' {x}) := hf.isCompact_preimage isCompact_singleton
  have hcover : f ⁻¹' {x} ⊆ ⋃ y, U y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, (hU ⟨y, hy⟩).2⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun y => (hU y).1) hcover
  let V : Set Y := ⋃ y ∈ t, U y
  have hV : IsOpen V := isOpen_biUnion fun y _ => (hU y).1
  let W : Set X := (f '' Vᶜ)ᶜ
  have hW : IsOpen W := (hf.isClosedMap _ hV.isClosed_compl).isOpen_compl
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hfy⟩
    exact hy (ht (show y ∈ f ⁻¹' {x} from Set.mem_singleton_iff.mpr hfy))
  have hpre : f ⁻¹' W ⊆ V := by
    intro y hy
    by_contra hyV
    exact hy ⟨y, hyV, rfl⟩
  refine ⟨t, W, hW, hxW, hpre, ?_⟩
  intro z hz
  obtain ⟨y, hfy⟩ := hsurj z
  have hy : y ∈ V := hpre (by change f y ∈ W; rw [hfy]; exact hz)
  obtain ⟨a, ha, hyU⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨a, ha, y, hyU, hfy⟩

end TranscendentalNakamaye.Pending.ProperFiberFiniteNeighborhoodCover
