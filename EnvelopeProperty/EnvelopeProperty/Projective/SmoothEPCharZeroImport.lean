/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietySmoothEP

/-!
# The envelope property of smooth `X = V(I)` in characteristic `0` (imported) and in general

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX, revision
`832e086`), Theorem 3.1 (`thm:smooth-EP`): *let `X` be a smooth projective variety over `k`; then
every nef class `θ ∈ N¹(X)_ℝ` has the envelope property*. FHX proves it in characteristic `p > 0`
(§3) and cites, for `char k = 0` (or `dim X ≤ 2`), Boucksom–Jonsson, *Global pluripotential
theory over a trivially valued field* (BJ22), Theorem 5.20 (`thm:contenvlisse`): *assume that `X`
is smooth and connected, and that either `char k = 0` or `dim X ≤ 2`; then any `θ ∈ Nef(X)` has
the envelope property*. Its proof resolves test configurations and uses multiplier ideals.

In characteristic `p` the statement for a projectively normal `X = V(I) ⊆ ℙᴹ` with smooth charts and
the classes `θ c₁(O_X(1))` is proved in `EnvelopeProperty.Projective.SubvarietySmoothEP`
(`ProjSubvariety.hasEnvelopeProperty_of_charP`, blueprint `thm:sg-ep-charp`). In characteristic `0`
it is recorded here as a hypothesis class (blueprint `thm:import-sg-ep-char0`, chapter
`smooth-general.tex`; author's decision D1 of `PLAN-31G`), and the two cases are combined into
blueprint `thm:sg-ep`. The class is now proved for every algebraically closed field of
characteristic `0`: `smoothEnvelopeCharZero_unconditional` and the instance
`SmoothEnvelopeCharZero.instOfIsAlgClosed` (`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`,
from relative ample Nadel vanishing, `Vanishing/RelativeNadelVanishing.lean`).

## Main definitions and results

* `SmoothEnvelopeCharZero k` (**`thm:import-sg-ep-char0`**, imported): a `Prop`-valued class, not an
  axiom.
* `ProjSubvariety.hasEnvelopeProperty_of_neg`: classes `θ < 0` have the envelope property
  vacuously (`PSH(X, θ) = ∅`, `prop:pg-maxprin`).
* `ProjSubvariety.hasEnvelopeProperty_of_charZero`: in characteristic `0`, under
  `SmoothEnvelopeCharZero k`, every `θ ∈ ℝ` has the envelope property.
* `ProjSubvariety.hasEnvelopeProperty_of_smooth` (**`thm:sg-ep`**): for `k` algebraically closed of
  any characteristic, every `θ ∈ ℝ` has the envelope property on a projectively normal `X` with
  smooth charts; unconditionally in characteristic `p`, and from `SmoothEnvelopeCharZero k` in
  characteristic `0`.

## Fidelity of the imported statement

`SmoothEnvelopeCharZero` is the special case of BJ22 Theorem 5.20 (in characteristic `0`) for
`X = V(I)` projectively normal with smooth charts over an algebraically closed field `k` and the
nef classes `θ c₁(O_X(1))`, `θ ≥ 0`: such an `X` is smooth (it is covered by the smooth charts
`A_i`, `xᵢ ∉ I`) and connected (`I` is prime), and `O_X(1)` is ample. The psh classes are those
of the Fubini–Study system of `X` (`ProjSubvariety.IsPSH`, `def:pg-subvariety-psh`); they coincide
with BJ22's `PSH(X, θ c₁(O(1)))` by `rmk:pg-subvariety-psh-comparison` (Serre's lifting of sections
and the openness of the ample cone), a comparison of models that is not formalized. The envelope
property is `FSSystem.HasEnvelopeProperty` (`def:sg-ep`, BJ22 §5.2): for every nonempty family in
`PSH(X, θ)` uniformly bounded above, the usc regularization of its supremum is `θ`-psh. The class
is stated for `θ ≥ 0` only, since classes `θ < 0` have the property vacuously
(`ProjSubvariety.hasEnvelopeProperty_of_neg`). For `X = ℙⁿ` the characteristic `0` statement is
proved unconditionally elsewhere in the project (`thm:c0-pn-ep`).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u

/-- **Imported (FHX Theorem 3.1, `thm:smooth-EP`, in characteristic `0`; BJ22 Theorem 5.20,
`thm:contenvlisse`), blueprint `thm:import-sg-ep-char0`.** Let `k` be algebraically closed of
characteristic `0` and `X = V(I) ⊆ ℙᴹ` projectively normal with smooth charts. Then every class
`θ c₁(O_X(1))`, `θ ≥ 0`, has the envelope property on `X`.

Source statements: BJ22 Theorem 5.20: *Assume that `X` is smooth and connected, and that either
`char k = 0` or `dim X ≤ 2`. Then any `θ ∈ Nef(X)` has the envelope property.* FHX Theorem 3.1:
*Let `X` be a smooth projective variety over `k`. Then every nef class `θ ∈ N¹(X)_ℝ` has the
envelope property* (for `char k = 0` or `n ≤ 2` FHX cites BJ22 Theorem 5.20). This class is an
explicit hypothesis, **not** an axiom: every theorem using it lists it among its hypotheses. -/
class SmoothEnvelopeCharZero (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] : Prop where
  hasEnvelopeProperty : ∀ {M : ℕ} (X : ProjSubvariety k M), X.IsProjNormal → X.HasSmoothCharts →
    ∀ θ : ℝ, 0 ≤ θ → X.HasEnvelopeProperty θ

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ}

/-- For `θ < 0` there are no `θ`-psh functions on `X^an` (`prop:pg-maxprin`), so `θ` has the
envelope property vacuously. -/
theorem hasEnvelopeProperty_of_neg (X : ProjSubvariety k M) {θ : ℝ} (hθ : θ < 0) :
    X.HasEnvelopeProperty θ :=
  FSSystem.hasEnvelopeProperty_of_not_nonneg fun h => absurd (h 0) (not_le.2 hθ)

/-- **`thm:sg-ep` in characteristic `0`**: under the imported `SmoothEnvelopeCharZero k`
(`thm:import-sg-ep-char0`), every `θ ∈ ℝ` has the envelope property on a projectively normal
`X = V(I)` with smooth charts; for `θ < 0` this is `hasEnvelopeProperty_of_neg`. -/
theorem hasEnvelopeProperty_of_charZero [IsAlgClosed k] [CharZero k] [SmoothEnvelopeCharZero k]
    (X : ProjSubvariety k M) (hX : X.IsProjNormal) (hs : X.HasSmoothCharts) (θ : ℝ) :
    X.HasEnvelopeProperty θ := by
  rcases le_or_gt 0 θ with hθ | hθ
  · exact SmoothEnvelopeCharZero.hasEnvelopeProperty X hX hs θ hθ
  · exact hasEnvelopeProperty_of_neg X hθ

/-- **FHX Theorem 3.1 for smooth projectively normal `X = V(I)`** (**`thm:sg-ep`**, FHX
`thm:smooth-EP`, classes `θ c₁(O_X(1))`): let `k` be algebraically closed and `X = V(I) ⊆ ℙᴹ`
projectively normal with smooth charts. Then every `θ ∈ ℝ` has the envelope property on `X`. In
characteristic `p > 0` this is `hasEnvelopeProperty_of_charP` (`thm:sg-ep-charp`), with no
hypothesis; in characteristic `0` it rests on the imported `SmoothEnvelopeCharZero k`
(`thm:import-sg-ep-char0`), which `h₀` provides (in positive characteristic `h₀` holds vacuously). -/
theorem hasEnvelopeProperty_of_smooth [IsAlgClosed k]
    (h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k) (X : ProjSubvariety k M)
    (hX : X.IsProjNormal) (hs : X.HasSmoothCharts) (θ : ℝ) : X.HasEnvelopeProperty θ := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    exact hasEnvelopeProperty_of_charP (ringChar k) X hX hs θ
  · have : CharZero k := (CharP.charP_zero_iff_charZero k).1 (h0 ▸ ringChar.charP k)
    exact hasEnvelopeProperty_of_charZero X hX hs θ

end ProjSubvariety

end EnvelopeProperty
