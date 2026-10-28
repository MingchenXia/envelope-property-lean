/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Topology.Connected.Clopen

namespace EnvelopeProperty

/-- An actual nonconstant continuous path from a preconnected space prevents its value from being isolated in a T1 target. -/
theorem not_isOpen_singleton_of_continuous_connected
    {Z W : Type*} [TopologicalSpace Z] [PreconnectedSpace Z]
    [TopologicalSpace W] [T1Space W] {f : Z → W} (hf : Continuous f)
    (z : Z) (z' : Z) (hne : f z' ≠ f z) :
    ¬ IsOpen ({f z} : Set W) := by
  intro ho
  have he : f ⁻¹' ({f z} : Set W) = Set.univ :=
    IsClopen.eq_univ ⟨(isClosed_singleton).preimage hf, ho.preimage hf⟩
      ⟨z, by simp⟩
  have hmem : z' ∈ f ⁻¹' ({f z} : Set W) := by rw [he]; trivial
  exact hne hmem

end EnvelopeProperty
