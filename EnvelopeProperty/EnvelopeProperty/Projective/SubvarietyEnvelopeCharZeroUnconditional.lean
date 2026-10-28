/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Vanishing.RelativeNadelVanishing
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroNadel

/-!
# The smooth envelope property in characteristic zero holds: the instance `SmoothEnvelopeCharZero k`

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX, revision
`832e086`), Theorem 3.1 (`thm:smooth-EP`) in characteristic `0`, which FHX cites from
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
Theorem 5.20 (`thm:contenvlisse`): over an algebraically closed field `k` of characteristic `0`,
for every projectively normal `X = V(I) ⊆ ℙᴹ` with smooth charts and every `θ ≥ 0`, the class
`θ c₁(O_X(1))` has the envelope property. In the project this statement is the `Prop`-valued class
`SmoothEnvelopeCharZero k` (`Projective/SmoothEPCharZeroImport.lean`, blueprint
`thm:import-sg-ep-char0`).

## Proof

`smoothEnvelopeCharZero_of_relativeNadel` (`Projective/SubvarietyEnvelopeCharZeroNadel.lean`,
blueprint `thm:c0n-original-smooth-envelope-from-nadel`) derives the class from relative ample
Nadel vanishing over finite-type affine `k`-bases, which is
`Char0.relativeAmpleNadelVanishingInput k` (`Vanishing/RelativeNadelVanishing.lean`, blueprint
`thm:kn-relative-ample-nadel-vanishing`), as in BJ22 §5 (multiplier ideals and the uniform global
generation of their twists).

## Main results

* `smoothEnvelopeCharZero_unconditional k` (blueprint `thm:kn-smooth-envelope-char-zero`).
* `SmoothEnvelopeCharZero.instOfIsAlgClosed`: the global instance. `SmoothEnvelopeCharZero` is a
  `Prop`-valued class, so the instance creates no diamond; no other instance of the class exists,
  and no instance takes it as an argument, so it creates no loop.
* `ProjSubvariety.hasEnvelopeProperty_of_smooth_unconditional` (blueprint
  `thm:kn-smooth-envelope-all-characteristics`): FHX Theorem 3.1 for projectively normal
  `X = V(I) ⊆ ℙᴹ` with smooth charts over every algebraically closed field, without hypothesis.
-/

namespace EnvelopeProperty

universe u

/-- **FHX Theorem 3.1 in characteristic `0`** (BJ22 Theorem 5.20, `thm:contenvlisse`; FHX
`thm:smooth-EP`; blueprint `thm:kn-smooth-envelope-char-zero`): over an algebraically closed
field of characteristic `0`, every projectively normal `X = V(I) ⊆ ℙᴹ` with smooth charts has the
envelope property in every class `θ c₁(O_X(1))`, `θ ≥ 0`. -/
theorem smoothEnvelopeCharZero_unconditional (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] : SmoothEnvelopeCharZero k :=
  smoothEnvelopeCharZero_of_relativeNadel (Char0.relativeAmpleNadelVanishingInput k)

/-- **FHX Theorem 3.1 in characteristic `0`**, as an instance: `SmoothEnvelopeCharZero k` holds
for every algebraically closed field `k` of characteristic `0`. -/
instance SmoothEnvelopeCharZero.instOfIsAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] : SmoothEnvelopeCharZero k :=
  smoothEnvelopeCharZero_unconditional k

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ}

/-- **FHX Theorem 3.1 for smooth projectively normal `X = V(I)`** (FHX `thm:smooth-EP`, classes
`θ c₁(O_X(1))`; blueprint `thm:kn-smooth-envelope-all-characteristics`): over an algebraically
closed field `k` of any characteristic, every projectively normal `X = V(I) ⊆ ℙᴹ` with smooth
charts has the envelope property in every class `θ ∈ ℝ`. This is `hasEnvelopeProperty_of_smooth`
(`thm:sg-ep`) with its characteristic-`0` hypothesis discharged by
`SmoothEnvelopeCharZero.instOfIsAlgClosed`. -/
theorem hasEnvelopeProperty_of_smooth_unconditional [IsAlgClosed k] (X : ProjSubvariety k M)
    (hX : X.IsProjNormal) (hs : X.HasSmoothCharts) (θ : ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_smooth inferInstance X hX hs θ

end ProjSubvariety

end EnvelopeProperty
