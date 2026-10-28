/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.EnvelopeChar0
import EnvelopeProperty.Char0.L2ExtensionAssembly

/-!
# FHX Theorem 3.1 on ℙⁿ in characteristic 0, with the Bergman input discharged

`ProjBerk.hasEnvelopeProperty_of_charZero_of_inputs` (Projective/EnvelopeChar0.lean) assembles the
envelope property of ℙⁿ over a countable algebraically closed field of characteristic `0` from two
literal input statements of the blueprint `char0.tex`: `Char0.BergmanLowerBound`
(`cor:c0-bergman-lower`) and `Char0.ValuativeUpperBound` (`prop:c0-valuative-bound`,
`cor:c0-valuative-upper`). The first is a theorem, `Char0.bergmanLowerBound_holds`
(Char0/L2ExtensionAssembly.lean, from the Ohsawa–Takegoshi and Hörmander theorems of the pinned
dependency TranscendentalNakamaye). The statement below therefore assumes only the valuative bound,
which lane Z3 is proving.
-/

namespace EnvelopeProperty

universe u

/-- **FHX Theorem 3.1 on ℙⁿ in characteristic 0**, conditional only on the valuative bound
`Char0.ValuativeUpperBound` (`prop:c0-valuative-bound`). -/
theorem ProjBerk.hasEnvelopeProperty_of_charZero_of_valuativeUpperBound {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] [Countable k] (hval : Char0.ValuativeUpperBound) (n : ℕ) {θ : ℝ}
    (hθ : 0 ≤ θ) : ProjBerk.HasEnvelopeProperty k n θ :=
  ProjBerk.hasEnvelopeProperty_of_charZero_of_inputs hval Char0.bergmanLowerBound_holds n hθ

end EnvelopeProperty
