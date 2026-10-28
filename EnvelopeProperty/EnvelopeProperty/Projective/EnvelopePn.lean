/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.EnvelopeChar0Final
import EnvelopeProperty.Projective.SmoothEP
import EnvelopeProperty.Char0.ValuativeBoundAssembly
import EnvelopeProperty.Local.NonflatExtension

/-!
# FHX Theorem 3.1 on ℙⁿ in every characteristic

* `ProjBerk.hasEnvelopeProperty_of_charZero`: over a countable algebraically closed field of
  characteristic `0`, every `θ ≥ 0` has the envelope property on ℙⁿ. This is
  `ProjBerk.hasEnvelopeProperty_of_charZero_of_valuativeUpperBound` with the valuative bound
  `Char0.valuativeUpperBound_holds` (lane Z3). The L² inputs come from the pinned dependency
  TranscendentalNakamaye (`deps/TN-PIN.md`).
* `ProjBerk.hasEnvelopeProperty_of_countable`: the same over any countable algebraically closed
  field, combining the characteristic-`0` case with `ProjBerk.hasEnvelopeProperty_of_charP`.
* `IsRegularizable.exists_extend`: the extension step of FHX Proposition 5.22
  (`lem:nonflat-extension`), with the envelope property of ℙⁿ discharged in every characteristic.
-/

namespace EnvelopeProperty

universe u

/-- **FHX Theorem 3.1 on ℙⁿ, characteristic 0**: unconditional. -/
theorem ProjBerk.hasEnvelopeProperty_of_charZero {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] [Countable k] (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ProjBerk.HasEnvelopeProperty k n θ :=
  ProjBerk.hasEnvelopeProperty_of_charZero_of_valuativeUpperBound Char0.valuativeUpperBound_holds n hθ

/-- **FHX Theorem 3.1 on ℙⁿ** over a countable algebraically closed field of any characteristic. -/
theorem ProjBerk.hasEnvelopeProperty_of_countable {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) : ProjBerk.HasEnvelopeProperty k n θ := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    exact ProjBerk.hasEnvelopeProperty_of_charP (ringChar k) n hθ
  · have : CharZero k := (CharP.charP_zero_iff_charZero k).1 (h0 ▸ ringChar.charP k)
    exact ProjBerk.hasEnvelopeProperty_of_charZero n hθ

/-- **Extension step of FHX Proposition 5.22** (`lem:nonflat-extension`), with the envelope property
of ℙⁿ (FHX Theorem 3.1) discharged in every characteristic. -/
theorem IsRegularizable.exists_extend {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [WuRegularization.{u, u} k] {n : ℕ} (hn : 1 ≤ n) {hS : MvPolynomial (Fin n) k} (hS0 : hS ≠ 0)
    {h : Localization.Away hS} (hh : h ≠ 0) {v₀ : Berk k (Localization.Away h) → EReal}
    (hv₀ : IsRegularizable v₀) (g : FSData k (Localization.Away hS)) (B : ℝ)
    (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap h y) + (B : EReal)) :
    ∃ v : Berk k (Localization.Away hS) → EReal, IsRegularizable v ∧
      ∀ y, v (Berk.awayComap h y) = v₀ y :=
  IsRegularizable.exists_extend_of_hasEnvelopeProperty hn
    (fun a ha => ProjBerk.hasEnvelopeProperty_of_countable n (by exact_mod_cast ha.le)) hS0 hh hv₀
    g B hv₀g

end EnvelopeProperty
