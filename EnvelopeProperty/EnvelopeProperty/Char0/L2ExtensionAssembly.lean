/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.L2Extension
import EnvelopeProperty.Char0.AssemblyInputs

/-!
# The Bergman input of the characteristic-zero assembly

`EnvelopeProperty.Char0.AssemblyInputs` states `cor:c0-bergman-lower` (blueprint `char0.tex`) as
the hypothesis structure `BergmanLowerBound` of the assembly. This file discharges it:
`bergmanLowerBound_holds` is `exists_homogeneous_lower_bound_of_bihomogeneous`
(`EnvelopeProperty.Char0.L2Extension`), which rests on the Ohsawa–Takegoshi and Hörmander theorems
of the pinned dependency TranscendentalNakamaye (`deps/TN-PIN.md`).
-/

namespace EnvelopeProperty.Char0

/-- **`cor:c0-bergman-lower` holds**: the Bergman input `BergmanLowerBound` of the
characteristic-zero assembly is a theorem. -/
theorem bergmanLowerBound_holds : BergmanLowerBound where
  exists_lower_bound n ι _ g D hg hg0 c hc := by
    obtain ⟨j₀, hj₀⟩ := hg0
    obtain ⟨s, hs, hlow⟩ := exists_homogeneous_lower_bound_of_bihomogeneous g hg hj₀ hc
    exact ⟨s, fun P hP => ⟨(hs P hP).2.1, (hs P hP).2.2, (hs P hP).1⟩, hlow⟩

end EnvelopeProperty.Char0
