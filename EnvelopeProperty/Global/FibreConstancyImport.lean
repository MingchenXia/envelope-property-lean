/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupPSH
import EnvelopeProperty.Projective.SubvarietyNormal

/-!
# Fibre constancy of psh functions on blowups

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX),
Theorem 6.1 (`thm:normal-ample-EP`), Step 1, contains the claim

> *We claim that `Φ` is constant on every fibre of `β^an`.*

for `Φ ∈ PSH(Y, β^* h^* L)`, where `Y → T → X` is the Stein factorization of an alteration of a
normal `X`, `β : Y → T` its birational part and `L` ample on `X`. This file states the claim, in
the model of the blowups of `projective-general.tex` (`def:pg-blowup`,
`ProjSubvariety.BlowupCenter`), as the hypothesis class `BlowupFibreConstancy k` (blueprint
`thm:gl-fibre-constancy`, `rmk:gl-fibre-constancy`). The class holds over every algebraically
closed field: the instance `blowupFibreConstancy_proved` (`Global/BlowupFibreConstancyProved.lean`)
derives geometric connectedness of the fibres from the formal functions `H⁰` and applies a maximum
principle for directed nets on the whole fibre, which needs no countability. The class is stated
in this separate module so that the theorems taking it as a hypothesis do not import that proof.

## Main definitions and results

* `BlowupFibreConstancy k` (**`thm:gl-fibre-constancy`**): a `Prop`-valued class, **not
  an axiom**. For a projectively normal `T' = V(I) ⊆ ℙᴹ`, a blowup `μ : B → T'` along forms of one
  degree (`B : T'.BlowupCenter M'`), a rational `a > 0` and `Φ ∈ PSH(B, μ^* O(a))`
  (`B.IsPSH ![a, 0] Φ`), `Φ` is constant on the fibres of `μ^an = B.proj`.
* `ProjSubvariety.BlowupCenter.IsPSH.apply_eq_of_proj_eq`: the class, applied.
* `ProjSubvariety.BlowupCenter.IsPSH.factorsThrough_proj`,
  `ProjSubvariety.BlowupCenter.IsPSH.exists_eq_comp_proj`: `Φ = φ ∘ μ^an` for a function `φ` on
  `T'^an`; by surjectivity of `μ^an` (`BlowupCenter.proj_surjective`, `lem:pg-blowup-surjective`)
  `φ` is unique.

## Fidelity of the statement (`rmk:gl-fibre-constancy`)

FHX's proof of the claim: the fibre of `β^an` over `t ∈ T^an` is the analytification of the
proper `𝓗(t)`-scheme `Y ×_T Spec 𝓗(t)`, connected because `β` has geometrically connected fibres,
hence compact, connected and without boundary (Berkovich 1990, §§3.4–3.5); for an admissible pair
`(m, s)` with `t ∈ T_s^an`, `Φ - m⁻¹ log |β^* s|` is locally psh (FHX Lemma 5.4(2),
`lem:global-to-local`), its restriction to the fibre is classically psh (FHX Lemma 5.2(2),(4),
`lem:local-basic`) and `m⁻¹ log |β^* s|` is constant on the fibre; unless `Φ ≡ -∞` on the fibre,
the set where `Φ` attains its maximum on the fibre is closed (upper semicontinuity) and open
(local maximum principle, Gubler–Rabinoff 2025, Theorem 6.1: *let `X`
be a `k`-analytic space and `u` a classically psh function on `X`; if `u` has a local maximum at
`x ∈ Int(X)`, then `u` is locally constant at `x`*).

The class is stated for **every** blowup `μ : B → T'` of a projectively normal `T'` along forms of
one degree, not only for the birational part of a Stein factorization with smooth source: the
argument uses only properness of `μ`, geometric connectedness of its fibres (Zariski's main
theorem, `μ_* O_B = O_{T'}` for `T'` normal) and FHX Lemma 5.4(2) for the pulled-back semiample
class `μ^* O(a)`; smoothness of the source plays no role. Nor does
countability of `k` (FHX assume it in Step 1 only for Corollary 5.26): Lemma 5.4(2) rests on BJ22
Corollary 12.18(ii), which holds over any `k`. The classes
are `PSH(B, μ^* O(a)) = B.IsPSH ![a, 0]` (`def:pg-blowup-psh`),
the psh functions of the bigraded Fubini–Study system of `B ⊆ ℙᴹ × ℙ^{M'}`, which coincide with
BJ22's `PSH(B, μ^* O(a))` by `rmk:pg-blowup-psh-comparison` (not formalized). The proof of
the class works with the points of the completed fibres, traces along finite flat curves,
maximum principles on proper spaces and formal functions on the original projective model; it
treats directed nets directly, without reducing them to sequences.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u

/-- **Fibre constancy (FHX Theorem 6.1, Step 1, `thm:normal-ample-EP`: "`Φ` is constant on every
fibre of `β^an`"), blueprint `thm:gl-fibre-constancy`.** Let `k` be algebraically closed,
`T' = V(I) ⊆ ℙᴹ` projectively normal, `μ : B → T'` the blowup of `T'` along forms
`G₀, …, G_{M'}` of one degree (`B : T'.BlowupCenter M'`, `def:pg-blowup`), `a ∈ ℚ_{>0}` and
`Φ ∈ PSH(B, μ^* O(a))` (`B.IsPSH ![a, 0] Φ`, `def:pg-blowup-psh`). Then `Φ` is constant on every
fibre of `μ^an = B.proj : B^an → T'^an`.

FHX proves the claim for the birational part of the Stein factorization of an alteration (with
smooth source) through the local maximum principle of Gubler–Rabinoff for classically psh
functions on the compact, connected, boundaryless fibres; the same argument applies to every such
blowup (`rmk:gl-fibre-constancy`). This class is **not** an axiom: the instance
`blowupFibreConstancy_proved` (`Global/BlowupFibreConstancyProved.lean`) proves it over every
algebraically closed field. -/
class BlowupFibreConstancy (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  /-- `Φ ∈ PSH(B, μ^* O(a))` takes the same value at two points with the same image under
  `μ^an`. -/
  apply_eq_of_proj_eq : ∀ {M M' : ℕ} (T' : ProjSubvariety k M), T'.IsProjNormal →
    ∀ (B : T'.BlowupCenter M') (a : ℚ), 0 < a → ∀ Φ : B.an → EReal,
      B.IsPSH ![(a : ℝ), 0] Φ → ∀ y y' : B.an, B.proj y = B.proj y' → Φ y = Φ y'

namespace ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] [IsAlgClosed k] [BlowupFibreConstancy k] {M M' : ℕ}
  {T' : ProjSubvariety k M} {B : T'.BlowupCenter M'} {a : ℚ} {Φ : B.an → EReal}

/-- **Fibre constancy** (`thm:gl-fibre-constancy`, from the imported `BlowupFibreConstancy k`): a
`μ^* O(a)`-psh function on the blowup `B` of a projectively normal `T'`, `a ∈ ℚ_{>0}`, takes the
same value at two points of `B^an` with the same image in `T'^an`. -/
theorem IsPSH.apply_eq_of_proj_eq (hT' : T'.IsProjNormal) (ha : 0 < a)
    (hΦ : B.IsPSH ![(a : ℝ), 0] Φ) {y y' : B.an} (h : B.proj y = B.proj y') : Φ y = Φ y' :=
  BlowupFibreConstancy.apply_eq_of_proj_eq T' hT' B a ha Φ hΦ y y' h

/-- Fibre constancy as a factorization property: `Φ` factors through `μ^an = B.proj`. -/
theorem IsPSH.factorsThrough_proj (hT' : T'.IsProjNormal) (ha : 0 < a)
    (hΦ : B.IsPSH ![(a : ℝ), 0] Φ) : Function.FactorsThrough Φ B.proj :=
  fun _ _ h => hΦ.apply_eq_of_proj_eq hT' ha h

/-- Fibre constancy: `Φ = φ ∘ μ^an` for a function `φ` on `T'^an` (unique, as `μ^an` is
surjective, `proj_surjective`). -/
theorem IsPSH.exists_eq_comp_proj (hT' : T'.IsProjNormal) (ha : 0 < a)
    (hΦ : B.IsPSH ![(a : ℝ), 0] Φ) : ∃ φ : T'.an → EReal, Φ = φ ∘ B.proj :=
  ⟨Function.extend B.proj Φ fun _ => ⊥, funext fun y =>
    ((hΦ.factorsThrough_proj hT' ha).extend_apply _ y).symm⟩

end ProjSubvariety.BlowupCenter

end EnvelopeProperty
