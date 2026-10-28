/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Defs

/-!
# Strict exhaustions

The property produced by FHX Lemma 5.18 (`lem:strict-exhaustion`) and consumed by
Lemma 5.19 (`lem:hull-criterion`) and Proposition 5.20 (`prop:gluing`): a nonnegative
regularizable function `ρ` such that for every point `x` and neighbourhood `V` of `x` there are a
regularizable `ρ' ≤ ρ` with `ρ'(x) = ρ(x)` and a constant `δ > 0` with `ρ' ≤ ρ - δ` off `V`.
-/

open scoped Topology

namespace EnvelopeProperty

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- `ρ` is a **strict exhaustion** in the sense of FHX Lemma 5.18. The inequality `ρ' ≤ ρ - δ`
off `V` is written `ρ' y + δ ≤ ρ y` (all values are finite). -/
def IsStrictExhaustion (ρ : Berk k A → EReal) : Prop :=
  IsRegularizable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    ∀ x : Berk k A, ∀ V ∈ 𝓝 x, ∃ (ρ' : Berk k A → EReal) (δ : ℝ), 0 < δ ∧
      IsRegularizable ρ' ∧ (∀ y, ρ' y ≤ ρ y) ∧ ρ' x = ρ x ∧
      ∀ y ∉ V, ρ' y + (δ : EReal) ≤ ρ y

end EnvelopeProperty
