/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Boucksom–Jonsson's Lemma 4.6 is false (`prop:nn-bj-lemma46-false`)

This file gives a machine-checked counterexample to Lemma 4.6 (`lem:PSH`) of Boucksom–Jonsson,
*Global pluripotential theory over a trivially valued field* (BJ22, arXiv v4,
`references/bj22-trivval/source/trivval_2022_Mar8.tex`, label `lem:PSH`), following the blueprint
proposition `prop:nn-bj-lemma46-false` (`blueprint/src/nonnef.tex`) and the erratum
`LITERATURE-ERRATA.md` §1.1.

## BJ22's statement

> **Lemma 4.6.** Let `K` be a compact topological space, and assume we are given:
> * a set `S` and, for each `s ∈ S`, a family `𝓕_s` of continuous functions
>   `f : K → ℝ ∪ {-∞}`, stable under addition of a constant;
> * a map `ρ : S → T` to a metrizable topological space `T`.
>
> For each `t ∈ T`, denote by `𝓕̃_t` the set of all (usc) functions `g : K → ℝ ∪ {-∞}` that can
> be written as the pointwise limit of a decreasing net `(f_i)` with `f_i ∈ 𝓕_{s_i}` for a net
> `(s_i)` of `S` such that `lim_i ρ(s_i) = t` in `T`. Then `𝓕̃̃_t = 𝓕̃_t` for any `t ∈ T`. In
> other words, if a function `g : K → ℝ ∪ {-∞}` can be written as the pointwise limit of a
> decreasing net `(g_i)_{i ∈ I}` with `g_i ∈ 𝓕̃_{t_i}` for a net `(t_i)` of `T` such that
> `lim_i t_i = t`, then `g ∈ 𝓕̃_t`.

## Formalization of the statement

* `EnvelopeProperty.bj22DecrLimits 𝓕 ρ t` is `𝓕̃_t`: the functions `g : K → EReal` with values
  in `[-∞, ∞)` (i.e. `g y ≠ ⊤`) for which there are a net, i.e. a nonempty directed preorder `I`,
  `s : I → S` and `f : I → K → EReal` with `f i ∈ 𝓕 (s i)`, `f` antitone (decreasing),
  `f i y → g y` for every `y` (pointwise limit in the order topology of `EReal`), and
  `ρ (s i) → t`.
* `EnvelopeProperty.BJ22Lemma46Statement` is the lemma as stated: for every compact `K`, set `S`,
  families `𝓕 s` of continuous functions with values in `[-∞, ∞)` stable under addition of real
  constants, and map `ρ : S → T` to a metrizable space, `𝓕̃̃_t = 𝓕̃_t` for all `t`, where
  `𝓕̃̃ = bj22DecrLimits (bj22DecrLimits 𝓕 ρ) id` is the same construction applied to the
  family `(𝓕̃_t)_{t ∈ T}` indexed by `T` itself (with `ρ = id`), exactly as in the "in other
  words" sentence. `EnvelopeProperty.BJ22Lemma46StatementExplicit` is that sentence verbatim, and
  `EnvelopeProperty.bj22Lemma46Statement_iff_explicit` shows the two are equivalent (the inclusion
  `𝓕̃_t ⊆ 𝓕̃̃_t` is trivial, by constant nets: `bj22DecrLimits_subset_iterated`).

Conventions, all chosen so that the formal statement is BJ22's:
* `ℝ ∪ {-∞}` is `{a : EReal // a ≠ ⊤}`; a function into it is a function `K → EReal` with
  values `≠ ⊤`. The subspace topology of `[-∞, ∞)` in `EReal` is its order topology, so
  continuity and limits are BJ22's.
* "Stable under addition of a constant" is read with real constants `c`.
* Nets are indexed by nonempty directed preorders (BJ22 itself uses a preordered index set in the
  proof). Nonemptiness is part of the usual notion of net convergence (with Kelley's definition
  an empty net converges to nothing); with Mathlib's `Filter.atTop`, which is `⊥` on an empty
  type, an empty index would make every function a "limit" and the lemma vacuous.
* "(usc)" is a remark, not a condition: limits of decreasing nets of upper semicontinuous
  functions are upper semicontinuous (`upperSemicontinuous_of_mem_bj22DecrLimits`).
* Universes: `K`, `S`, `T` and the index types of nets live in arbitrary universes
  `u`, `v`, `w`, `x`; the counterexample `not_bj22Lemma46` refutes the statement in **every**
  choice of universes.

## The counterexample (blueprint `prop:nn-bj-lemma46-false`)

`S` and `T` are one point, `K = [0, 1]`. For `i ≥ 1` let `p_i = 2^{-i}`, `r_i = 2^{-i-2}`,
`B_i = [p_i - r_i, p_i + r_i]` (pairwise disjoint, avoiding `0` and `1`), and
`ℓ_i(x) = log(|x - p_i| / r_i)` on `B_i`, `ℓ_i = 0` off `B_i` (`BJ22Lemma46Counterexample.ell`,
written as `min{0, log(|x - p_i| / r_i)}`; `ell_eq_ite` is the blueprint's form). For `n, j ≥ 1`

  `f_{n,j} = ∑_{i=1}^{n} max{2ℓ_i, (1 + 1/n)ℓ_i - j}`,  `𝓕 = {f_{n,j} + c : n, j ≥ 1, c ∈ ℝ}`

(`approx`, `family`). Each `f_{n,j}` is continuous with values in `[-∞, 0]`. For fixed `n`,
`f_{n,j}` decreases in `j` to `g_n = ∑_{i ≤ n} 2ℓ_i` (`partialLimit`), and `g_n` decreases to
`g = ∑_{i ≥ 1} 2ℓ_i` (`limit`, a finite sum at every point); hence `g ∈ 𝓕̃̃`
(`limit_mem_iterated`). But `g ∉ 𝓕̃` (`limit_not_mem`): in a decreasing net
`f_{n_α,j_α} + c_α → g`, the rate `1 + 1/n` of `f_{n,j}` at `p_1` forces `n_β ≤ n_α` for `β ≥ α`
(a larger `n` exceeds a smaller one near `p_1`), so `n_α` is eventually a constant `N`; then
`f_{N,j}(1) + c = c = f_{N,j}(p_{N+1}) + c`, so `c_α` would converge both to `g(1) = 0` and to
`g(p_{N+1}) = -∞`.

## Main results

* `EnvelopeProperty.not_bj22Lemma46 : ¬ BJ22Lemma46Statement`;
* `EnvelopeProperty.not_bj22Lemma46StatementExplicit : ¬ BJ22Lemma46StatementExplicit`;
* `EnvelopeProperty.BJ22Lemma46Counterexample.limit_mem_iterated_Icc` (`g ∈ 𝓕̃̃`) and
  `EnvelopeProperty.BJ22Lemma46Counterexample.limit_not_mem_Icc` (`g ∉ 𝓕̃`), on `K = [0, 1]`,
  with `family_continuous` and `family_add_const` checking BJ22's hypotheses on `𝓕`.
-/

open scoped NNReal ENNReal Topology

open Filter Set

noncomputable section

namespace EnvelopeProperty

/-! ### BJ22's construction `𝓕 ↦ 𝓕̃` and the statement of Lemma 4.6 -/

/-- **BJ22's `𝓕̃_t`** (`lem:PSH`). Given families `𝓕 s` (`s ∈ S`) of functions `K → EReal`, a map
`ρ : S → T` and `t ∈ T`, `bj22DecrLimits 𝓕 ρ t` is the set of functions `g : K → ℝ ∪ {-∞}`
(i.e. `g y ≠ ⊤` for all `y`) that are the pointwise limit of a decreasing net `(f_i)_{i ∈ I}`
with `f_i ∈ 𝓕 (s i)` for a net `(s_i)` of `S` such that `ρ (s i) → t`. Nets are indexed by
nonempty directed preorders `I` in the universe `x`. -/
def bj22DecrLimits.{x, uK, uS, uT} {K : Type uK} {S : Type uS} {T : Type uT} [TopologicalSpace T]
    (𝓕 : S → Set (K → EReal)) (ρ : S → T) (t : T) : Set (K → EReal) :=
  {g | (∀ y, g y ≠ ⊤) ∧
    ∃ (I : Type x) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (s : I → S) (f : I → K → EReal),
      (∀ i, f i ∈ 𝓕 (s i)) ∧ Antitone f ∧
      (∀ y, Tendsto (fun i => f i y) atTop (𝓝 (g y))) ∧
      Tendsto (fun i => ρ (s i)) atTop (𝓝 t)}

/-- **BJ22, Lemma 4.6** (`lem:PSH`), as stated: for a compact topological space `K`, a set `S`
with families `𝓕 s` of continuous functions `K → ℝ ∪ {-∞}` stable under addition of (real)
constants, and a map `ρ : S → T` to a metrizable topological space `T`, one has `𝓕̃̃_t = 𝓕̃_t`
for every `t ∈ T`. Here `𝓕̃ = bj22DecrLimits 𝓕 ρ : T → Set (K → EReal)`, and `𝓕̃̃` is the same
construction applied to the family `(𝓕̃_t)_{t ∈ T}`, indexed by `T` with the map `id : T → T`.
The universes of `K`, `S`, `T` and of the index types of nets are `u`, `v`, `w`, `x`.
This statement is **false** in every universe: `not_bj22Lemma46`. -/
def BJ22Lemma46Statement.{u, v, w, x} : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] (S : Type v) (𝓕 : S → Set (K → EReal))
    (T : Type w) [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T] (ρ : S → T),
    (∀ s, ∀ f ∈ 𝓕 s, Continuous f ∧ ∀ y, f y ≠ ⊤) →
    (∀ s, ∀ f ∈ 𝓕 s, ∀ c : ℝ, (fun y => f y + (c : EReal)) ∈ 𝓕 s) →
    ∀ t : T, bj22DecrLimits.{x} (bj22DecrLimits.{x} 𝓕 ρ) id t = bj22DecrLimits.{x} 𝓕 ρ t

/-- **BJ22, Lemma 4.6**, in the "in other words" form of BJ22: under the same hypotheses, if a
function `g : K → ℝ ∪ {-∞}` is the pointwise limit of a decreasing net `(g_i)_{i ∈ I}` with
`g_i ∈ 𝓕̃_{t_i}` for a net `(t_i)` of `T` such that `t_i → t`, then `g ∈ 𝓕̃_t`. Equivalent to
`BJ22Lemma46Statement` (`bj22Lemma46Statement_iff_explicit`), and false
(`not_bj22Lemma46StatementExplicit`). -/
def BJ22Lemma46StatementExplicit.{u, v, w, x} : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] (S : Type v) (𝓕 : S → Set (K → EReal))
    (T : Type w) [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T] (ρ : S → T),
    (∀ s, ∀ f ∈ 𝓕 s, Continuous f ∧ ∀ y, f y ≠ ⊤) →
    (∀ s, ∀ f ∈ 𝓕 s, ∀ c : ℝ, (fun y => f y + (c : EReal)) ∈ 𝓕 s) →
    ∀ (t : T) (g : K → EReal), (∀ y, g y ≠ ⊤) →
      (∃ (I : Type x) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (τ : I → T) (G : I → K → EReal),
        (∀ i, G i ∈ bj22DecrLimits.{x} 𝓕 ρ (τ i)) ∧ Antitone G ∧
        (∀ y, Tendsto (fun i => G i y) atTop (𝓝 (g y))) ∧ Tendsto τ atTop (𝓝 t)) →
      g ∈ bj22DecrLimits.{x} 𝓕 ρ t

section Generic

universe x

variable {K : Type*} {S : Type*} {T : Type*} [TopologicalSpace T]
  {𝓕 : S → Set (K → EReal)} {ρ : S → T}

/-- The trivial inclusion `𝓕̃_t ⊆ 𝓕̃̃_t` (constant nets). -/
theorem bj22DecrLimits_subset_iterated (t : T) :
    bj22DecrLimits.{x} 𝓕 ρ t ⊆ bj22DecrLimits.{x} (bj22DecrLimits.{x} 𝓕 ρ) id t := by
  intro g hg
  exact ⟨hg.1, PUnit.{x + 1}, inferInstance, inferInstance, inferInstance, fun _ => t,
    fun _ => g, fun _ => hg, fun _ _ _ => le_rfl, fun _ => tendsto_const_nhds,
    tendsto_const_nhds⟩

/-- `𝓕̃_t` with the limit written as an infimum: for a decreasing net, pointwise convergence to
`g` means `g = infᵢ fᵢ`. (This is the shape of `IsDecrNetLimit` in
`EnvelopeProperty.Projective.PSH2`.) -/
theorem mem_bj22DecrLimits_iff_iInf {t : T} {g : K → EReal} :
    g ∈ bj22DecrLimits.{x} 𝓕 ρ t ↔ (∀ y, g y ≠ ⊤) ∧
      ∃ (I : Type x) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I) (s : I → S)
        (f : I → K → EReal), (∀ i, f i ∈ 𝓕 (s i)) ∧ Tendsto (fun i => ρ (s i)) atTop (𝓝 t) ∧
          (∀ y, Antitone fun i => f i y) ∧ ∀ y, g y = ⨅ i, f i y := by
  constructor
  · rintro ⟨hg, I, _, _, _, s, f, hf, hanti, hlim, hρ⟩
    exact ⟨hg, I, inferInstance, inferInstance, inferInstance, s, f, hf, hρ,
      fun y _ _ h => hanti h y,
      fun y => tendsto_nhds_unique (hlim y) (tendsto_atTop_iInf fun _ _ h => hanti h y)⟩
  · rintro ⟨hg, I, _, _, _, s, f, hf, hρ, hanti, hinf⟩
    refine ⟨hg, I, inferInstance, inferInstance, inferInstance, s, f, hf,
      fun _ _ h y => hanti y h, fun y => ?_, hρ⟩
    rw [hinf y]
    exact tendsto_atTop_iInf (hanti y)

/-- If all members of the families `𝓕 s` are upper semicontinuous (e.g. continuous), every
`g ∈ 𝓕̃_t` is upper semicontinuous, being an infimum of such functions. So the parenthetical
"(usc)" in BJ22's definition of `𝓕̃_t` is automatic, both for `𝓕̃` and for `𝓕̃̃`. -/
theorem upperSemicontinuous_of_mem_bj22DecrLimits [TopologicalSpace K]
    (h𝓕 : ∀ s, ∀ f ∈ 𝓕 s, UpperSemicontinuous f) {t : T} {g : K → EReal}
    (hg : g ∈ bj22DecrLimits.{x} 𝓕 ρ t) : UpperSemicontinuous g := by
  obtain ⟨-, I, _, _, _, s, f, hf, -, -, hinf⟩ := mem_bj22DecrLimits_iff_iInf.1 hg
  rw [show g = fun y => ⨅ i, f i y from funext hinf]
  exact upperSemicontinuous_iInf fun i => h𝓕 _ _ (hf i)

/-- `ULift ℕ` is directed (used to index sequences in the universe `x`). -/
private theorem isDirected_uLift_nat : IsDirected (ULift.{x} ℕ) (· ≤ ·) :=
  ⟨fun a b => ⟨ULift.up (max a.down b.down), le_max_left a.down b.down,
    le_max_right a.down b.down⟩⟩

/-- A decreasing *sequence* gives an element of `𝓕̃_t` (the sequence is reindexed by `ULift ℕ`
to live in the universe `x`). -/
theorem mem_bj22DecrLimits_of_seq {t : T} {g : K → EReal} (hg : ∀ y, g y ≠ ⊤) (s : ℕ → S)
    (f : ℕ → K → EReal) (hf : ∀ n, f n ∈ 𝓕 (s n)) (hanti : Antitone f)
    (hlim : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (g y)))
    (hρ : Tendsto (fun n => ρ (s n)) atTop (𝓝 t)) : g ∈ bj22DecrLimits.{x} 𝓕 ρ t := by
  have hdown : Tendsto (fun m : ULift.{x} ℕ => m.down) atTop atTop :=
    tendsto_atTop.2 fun b => mem_of_superset (mem_atTop (ULift.up b)) fun _ hm => hm
  exact ⟨hg, ULift.{x} ℕ, inferInstance, isDirected_uLift_nat, inferInstance, fun m => s m.down,
    fun m => f m.down, fun m => hf m.down, fun _ _ hab => hanti hab,
    fun y => (hlim y).comp hdown, hρ.comp hdown⟩

end Generic

/-- The two formulations of BJ22's Lemma 4.6 (`𝓕̃̃_t = 𝓕̃_t`, and the "in other words"
sentence) are equivalent. -/
theorem bj22Lemma46Statement_iff_explicit.{u, v, w, x} :
    BJ22Lemma46Statement.{u, v, w, x} ↔ BJ22Lemma46StatementExplicit.{u, v, w, x} := by
  constructor
  · intro h K _ _ S 𝓕 T _ _ ρ hc hadd t g hg hnet
    rw [← h K S 𝓕 T ρ hc hadd t]
    obtain ⟨I, _, _, _, τ, G, hG, hanti, hlim, hτ⟩ := hnet
    exact ⟨hg, I, inferInstance, inferInstance, inferInstance, τ, G, hG, hanti, hlim, hτ⟩
  · intro h K _ _ S 𝓕 T _ _ ρ hc hadd t
    refine Set.Subset.antisymm ?_ (bj22DecrLimits_subset_iterated t)
    rintro g ⟨hg, I, _, _, _, τ, G, hG, hanti, hlim, hτ⟩
    exact h K S 𝓕 T ρ hc hadd t g hg
      ⟨I, inferInstance, inferInstance, inferInstance, τ, G, hG, hanti, hlim, hτ⟩

/-! ### The counterexample -/

namespace BJ22Lemma46Counterexample

/-- The centre `p_i = 2^{-i}`. -/
def center (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i

/-- The radius `r_i = 2^{-i-2}`. -/
def radius (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 2)

/-- `ℓ_i(x) = min{0, log(|x - p_i| / r_i)}`, with `log 0 = -∞`. This is `log(|x - p_i| / r_i)` on
`B_i = [p_i - r_i, p_i + r_i]` and `0` off `B_i` (`ell_eq_ite`), as in the blueprint. -/
def ell (i : ℕ) (x : ℝ) : EReal :=
  min 0 (ENNReal.log (ENNReal.ofReal (|x - center i| / radius i)))

/-- `f_{n,j} = ∑_{i=1}^{n} max{2ℓ_i, (1 + 1/n)ℓ_i - j}` (blueprint notation; used for
`n, j ≥ 1`). -/
def approx (n j : ℕ) (x : ℝ) : EReal :=
  ∑ i ∈ Finset.Icc 1 n,
    max (2 * ell i x) (((1 + 1 / (n : ℝ) : ℝ) : EReal) * ell i x - ((j : ℝ) : EReal))

/-- `g_n = ∑_{i=1}^{n} 2ℓ_i`, the limit of `f_{n,j}` as `j → ∞`. -/
def partialLimit (n : ℕ) (x : ℝ) : EReal :=
  ∑ i ∈ Finset.Icc 1 n, 2 * ell i x

/-- `g = ∑_{i ≥ 1} 2ℓ_i` (a finite sum at every point, `limit_eq_of_active`), the limit of the
`g_n`. -/
def limit (x : ℝ) : EReal :=
  ∑ᶠ i ∈ Set.Ici 1, 2 * ell i x

/-- The family `𝓕 = {f_{n,j} + c : n, j ≥ 1, c ∈ ℝ}`, pulled back along a map `φ : K → ℝ` (for
`K = [0, 1]`, `φ` is the inclusion). -/
def family {K : Type*} (φ : K → ℝ) : Set (K → EReal) :=
  {F | ∃ n j : ℕ, 1 ≤ n ∧ 1 ≤ j ∧ ∃ c : ℝ, F = fun y => approx n j (φ y) + (c : EReal)}

/-! #### Small facts about `EReal` -/

private theorem coe_two_eq : ((2 : ℝ) : EReal) = 2 := rfl

private theorem coe_mul_nonpos' {a : ℝ} (ha : 0 < a) {ℓ : EReal} (hℓ : ℓ ≤ 0) :
    (a : EReal) * ℓ ≤ 0 := by
  induction ℓ using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ha]; exact bot_le
  | coe L =>
    rw [← EReal.coe_mul]
    exact EReal.coe_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos ha.le (EReal.coe_nonpos.1 hℓ))
  | top => exact absurd hℓ (not_le.2 EReal.zero_lt_top)

private theorem two_mul_nonpos' {ℓ : EReal} (hℓ : ℓ ≤ 0) : 2 * ℓ ≤ 0 := by
  rw [← coe_two_eq]; exact coe_mul_nonpos' two_pos hℓ

private theorem term_nonpos {ℓ : EReal} (hℓ : ℓ ≤ 0) {a : ℝ} (ha : 0 < a) {c : ℝ} (hc : 0 ≤ c) :
    max (2 * ℓ) ((a : EReal) * ℓ - (c : EReal)) ≤ 0 := by
  refine max_le (two_mul_nonpos' hℓ) ((EReal.sub_le_sub (coe_mul_nonpos' ha hℓ)
    (EReal.coe_nonneg.2 hc)).trans ?_)
  simp

private theorem term_zero (a : ℝ) (j : ℕ) :
    max (2 * (0 : EReal)) ((a : EReal) * 0 - ((j : ℝ) : EReal)) = 0 := by
  rw [mul_zero, mul_zero, zero_sub]
  refine max_eq_left ?_
  rw [← EReal.coe_neg]
  exact EReal.coe_nonpos.2 (neg_nonpos.2 (Nat.cast_nonneg j))

private theorem continuous_add_of_ne_top' {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hf : Continuous f) (hg : Continuous g) (hf' : ∀ x, f x ≠ ⊤) (hg' : ∀ x, g x ≠ ⊤) :
    Continuous fun x => f x + g x :=
  continuous_iff_continuousAt.2 fun x =>
    (EReal.continuousAt_add (p := (f x, g x)) (Or.inl (hf' x)) (Or.inr (hg' x))).comp
      (f := fun x => (f x, g x)) (hf.prodMk hg).continuousAt

private theorem continuous_coe_mul' {X : Type*} [TopologicalSpace X] {f : X → EReal}
    (hf : Continuous f) {a : ℝ} (ha : 0 < a) : Continuous fun x => (a : EReal) * f x := by
  have h0 : (a : EReal) ≠ 0 := EReal.coe_ne_zero.2 ha.ne'
  exact continuous_iff_continuousAt.2 fun x =>
    (EReal.continuousAt_mul (p := ((a : EReal), f x)) (Or.inl h0) (Or.inl h0)
        (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).comp
      (f := fun x => ((a : EReal), f x)) (continuous_const.prodMk hf).continuousAt

private theorem continuous_sub_coe' {X : Type*} [TopologicalSpace X] {f : X → EReal}
    (hf : Continuous f) (c : ℝ) : Continuous fun x => f x - (c : EReal) := by
  simp_rw [sub_eq_add_neg, ← EReal.coe_neg]
  exact continuous_iff_continuousAt.2 fun x =>
    (EReal.continuousAt_add (p := (f x, ((-c : ℝ) : EReal))) (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))).comp (f := fun x => (f x, ((-c : ℝ) : EReal)))
      (hf.prodMk continuous_const).continuousAt

private theorem continuous_finset_sum_of_nonpos {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) {f : ι → X → EReal} (hc : ∀ i, Continuous (f i)) (hn : ∀ i x, f i x ≤ 0) :
    Continuous fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact continuous_add_of_ne_top' (hc a) ih
      (fun x => ne_top_of_le_ne_top EReal.zero_ne_top (hn a x))
      (fun x => ne_top_of_le_ne_top EReal.zero_ne_top (Finset.sum_nonpos fun i _ => hn i x))

private theorem mult_pos (n : ℕ) : 0 < 1 + 1 / (n : ℝ) := by positivity

private theorem mult_le_two {n : ℕ} (hn : 1 ≤ n) : 1 + 1 / (n : ℝ) ≤ 2 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
  linarith

/-! #### The intervals `B_i` -/

theorem center_pos (i : ℕ) : 0 < center i := by unfold center; positivity

theorem radius_eq (i : ℕ) : radius i = center i / 4 := by
  unfold radius center; rw [pow_add]; ring

theorem radius_pos (i : ℕ) : 0 < radius i := by
  rw [radius_eq]; exact div_pos (center_pos i) (by norm_num)

theorem center_le_half {i k : ℕ} (h : i < k) : center k ≤ center i / 2 := by
  unfold center
  calc (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ (i + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = (1 / 2) ^ i / 2 := by rw [pow_succ]; ring

theorem center_mem_Icc (i : ℕ) : center i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(center_pos i).le, pow_le_one₀ (by norm_num) (by norm_num)⟩

private theorem false_of_abs_le_of_lt {x : ℝ} {i k : ℕ} (h : i < k)
    (hi : |x - center i| ≤ radius i) (hk : |x - center k| ≤ radius k) : False := by
  have h1 := (abs_le.1 hi).1
  have h2 := (abs_le.1 hk).2
  have h3 := center_le_half h
  have h4 := center_pos i
  rw [radius_eq] at h1 h2
  linarith

/-- The intervals `B_i = [p_i - r_i, p_i + r_i]` are pairwise disjoint. -/
theorem eq_of_abs_sub_le {x : ℝ} {i k : ℕ} (hi : |x - center i| ≤ radius i)
    (hk : |x - center k| ≤ radius k) : i = k := by
  rcases lt_trichotomy i k with h | h | h
  · exact (false_of_abs_le_of_lt h hi hk).elim
  · exact h
  · exact (false_of_abs_le_of_lt h hk hi).elim

/-! #### The functions `ℓ_i` -/

theorem ell_nonpos (i : ℕ) (x : ℝ) : ell i x ≤ 0 := min_le_left _ _

theorem ell_eq_zero_of_radius_le {i : ℕ} {x : ℝ} (h : radius i ≤ |x - center i|) :
    ell i x = 0 := by
  unfold ell
  refine min_eq_left ?_
  rw [ENNReal.zero_le_log_iff, ENNReal.one_le_ofReal, one_le_div (radius_pos i)]
  exact h

/-- The blueprint's definition of `ℓ_i`: `log(|x - p_i| / r_i)` on `B_i`, `0` elsewhere. -/
theorem ell_eq_ite (i : ℕ) (x : ℝ) :
    ell i x = if x ∈ Set.Icc (center i - radius i) (center i + radius i) then
      ENNReal.log (ENNReal.ofReal (|x - center i| / radius i)) else 0 := by
  split_ifs with h
  · unfold ell
    refine min_eq_right ?_
    rw [ENNReal.log_le_zero_iff, ENNReal.ofReal_le_one, div_le_one (radius_pos i)]
    exact abs_sub_le_iff.2 ⟨by linarith [h.2], by linarith [h.1]⟩
  · refine ell_eq_zero_of_radius_le ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    have := radius_pos i
    rcases h with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

theorem continuous_ell (i : ℕ) : Continuous (ell i) :=
  continuous_const.min (ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp
    (((continuous_id.sub continuous_const).abs).div_const _)))

theorem ell_eq_zero_of_ne {x : ℝ} {i₀ i : ℕ} (h₀ : |x - center i₀| ≤ radius i₀) (hi : i ≠ i₀) :
    ell i x = 0 :=
  ell_eq_zero_of_radius_le (not_le.1 fun h => hi (eq_of_abs_sub_le h h₀)).le

/-- At every point at most one `ℓ_i` is nonzero (the `B_i` are disjoint). -/
theorem exists_active (x : ℝ) : ∃ i₀, ∀ i, i ≠ i₀ → ell i x = 0 := by
  by_cases h : ∃ i₀, |x - center i₀| ≤ radius i₀
  · obtain ⟨i₀, h₀⟩ := h
    exact ⟨i₀, fun i hi => ell_eq_zero_of_ne h₀ hi⟩
  · push Not at h
    exact ⟨0, fun i _ => ell_eq_zero_of_radius_le (h i).le⟩

/-! #### The functions `f_{n,j}`, `g_n`, `g` at a point -/

theorem approx_eq_of_active {x : ℝ} {i₀ : ℕ} (h : ∀ i, i ≠ i₀ → ell i x = 0) (n j : ℕ) :
    approx n j x = if i₀ ∈ Finset.Icc 1 n then
      max (2 * ell i₀ x) (((1 + 1 / (n : ℝ) : ℝ) : EReal) * ell i₀ x - ((j : ℝ) : EReal))
      else 0 := by
  unfold approx
  split_ifs with hi
  · refine Finset.sum_eq_single_of_mem i₀ hi fun i _ hne => ?_
    rw [h i hne, term_zero]
  · refine Finset.sum_eq_zero fun i hi' => ?_
    rw [h i (by rintro rfl; exact hi hi'), term_zero]

theorem partialLimit_eq_of_active {x : ℝ} {i₀ : ℕ} (h : ∀ i, i ≠ i₀ → ell i x = 0) (n : ℕ) :
    partialLimit n x = if i₀ ∈ Finset.Icc 1 n then 2 * ell i₀ x else 0 := by
  unfold partialLimit
  split_ifs with hi
  · refine Finset.sum_eq_single_of_mem i₀ hi fun i _ hne => ?_
    rw [h i hne, mul_zero]
  · refine Finset.sum_eq_zero fun i hi' => ?_
    rw [h i (by rintro rfl; exact hi hi'), mul_zero]

theorem limit_eq_of_active {x : ℝ} {i₀ : ℕ} (h : ∀ i, i ≠ i₀ → ell i x = 0) :
    limit x = if 1 ≤ i₀ then 2 * ell i₀ x else 0 := by
  unfold limit
  rw [finsum_mem_def, finsum_eq_single _ i₀]
  · simp only [Set.indicator_apply, Set.mem_Ici]
  · intro i hi
    simp only [Set.indicator_apply, h i hi, mul_zero, ite_self]

theorem approx_nonpos (n j : ℕ) (x : ℝ) : approx n j x ≤ 0 :=
  Finset.sum_nonpos fun i _ => term_nonpos (ell_nonpos i x) (mult_pos n) (Nat.cast_nonneg j)

theorem partialLimit_nonpos (n : ℕ) (x : ℝ) : partialLimit n x ≤ 0 :=
  Finset.sum_nonpos fun i _ => two_mul_nonpos' (ell_nonpos i x)

theorem limit_nonpos (x : ℝ) : limit x ≤ 0 := by
  obtain ⟨i₀, h⟩ := exists_active x
  rw [limit_eq_of_active h]
  split_ifs
  exacts [two_mul_nonpos' (ell_nonpos _ _), le_rfl]

theorem continuous_approx (n j : ℕ) : Continuous (approx n j) := by
  unfold approx
  refine continuous_finset_sum_of_nonpos _
    (f := fun i x => max (2 * ell i x)
      (((1 + 1 / (n : ℝ) : ℝ) : EReal) * ell i x - ((j : ℝ) : EReal))) (fun i => ?_)
    (fun i x => term_nonpos (ell_nonpos i x) (mult_pos n) (Nat.cast_nonneg j))
  refine Continuous.max ?_ (continuous_sub_coe' (continuous_coe_mul' (continuous_ell i)
    (mult_pos n)) _)
  rw [← coe_two_eq]
  exact continuous_coe_mul' (continuous_ell i) two_pos

/-! #### `f_{n,j} ↘ g_n` as `j → ∞` and `g_n ↘ g` as `n → ∞` -/

theorem approx_antitone (n : ℕ) (x : ℝ) : Antitone fun j : ℕ => approx n j x := by
  intro j j' hjj'
  refine Finset.sum_le_sum fun i _ => max_le_max le_rfl (EReal.sub_le_sub le_rfl ?_)
  exact EReal.coe_le_coe_iff.2 (Nat.cast_le.2 hjj')

private theorem max_eventually_eq {ℓ : EReal} (hℓ : ℓ ≤ 0) {a : ℝ} (ha : 0 < a) :
    ∃ J : ℕ, ∀ j ≥ J, max (2 * ℓ) ((a : EReal) * ℓ - ((j : ℝ) : EReal)) = 2 * ℓ := by
  induction ℓ using EReal.rec with
  | bot =>
    refine ⟨0, fun j _ => ?_⟩
    rw [EReal.coe_mul_bot_of_pos ha, EReal.bot_sub]
    exact max_eq_left bot_le
  | coe L =>
    have hL : L ≤ 0 := EReal.coe_nonpos.1 hℓ
    refine ⟨⌈(2 - a) * (-L)⌉₊, fun j hj => ?_⟩
    have hj' : (2 - a) * (-L) ≤ j := (Nat.le_ceil _).trans (Nat.cast_le.2 hj)
    refine max_eq_left ?_
    rw [← coe_two_eq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    nlinarith
  | top => exact absurd hℓ (not_le.2 EReal.zero_lt_top)

/-- `f_{n,j}(x)` is eventually equal to `g_n(x)` as `j → ∞`. -/
theorem approx_eventually_eq (n : ℕ) (x : ℝ) :
    ∃ J : ℕ, ∀ j ≥ J, approx n j x = partialLimit n x := by
  obtain ⟨i₀, h⟩ := exists_active x
  simp only [approx_eq_of_active h, partialLimit_eq_of_active h]
  by_cases hi : i₀ ∈ Finset.Icc 1 n
  · simp only [hi, if_true]
    exact max_eventually_eq (ell_nonpos i₀ x) (mult_pos n)
  · exact ⟨0, fun _ _ => by simp only [hi, if_false]⟩

theorem partialLimit_antitone (x : ℝ) : Antitone fun n => partialLimit n x := by
  obtain ⟨i₀, h⟩ := exists_active x
  intro n m hnm
  simp only [partialLimit_eq_of_active h]
  by_cases hn : i₀ ∈ Finset.Icc 1 n
  · have hm : i₀ ∈ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hnm hn
    simp only [hn, hm, if_true, le_refl]
  · by_cases hm : i₀ ∈ Finset.Icc 1 m
    · simp only [hn, hm, if_true, if_false]
      exact two_mul_nonpos' (ell_nonpos _ _)
    · simp only [hn, hm, if_false, le_refl]

/-- `g_n(x)` is eventually equal to `g(x)` as `n → ∞`. -/
theorem partialLimit_eventually_eq (x : ℝ) : ∃ N : ℕ, ∀ n ≥ N, partialLimit n x = limit x := by
  obtain ⟨i₀, h⟩ := exists_active x
  refine ⟨i₀, fun n hn => ?_⟩
  rw [partialLimit_eq_of_active h, limit_eq_of_active h]
  by_cases h1 : 1 ≤ i₀
  · rw [if_pos (Finset.mem_Icc.2 ⟨h1, hn⟩), if_pos h1]
  · rw [if_neg (fun hi => h1 (Finset.mem_Icc.1 hi).1), if_neg h1]

/-! #### Values at special points -/

/-- The point `p_1 + r_1 e^L ∈ B_1`, where `ℓ_1 = L`. -/
def nearPoint (L : ℝ) : ℝ := center 1 + radius 1 * Real.exp L

theorem nearPoint_mem_Icc {L : ℝ} (hL : L ≤ 0) : nearPoint L ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : Real.exp L ≤ 1 := Real.exp_le_one_iff.2 hL
  have h2 := Real.exp_pos L
  unfold nearPoint center radius
  norm_num
  constructor <;> nlinarith

theorem abs_nearPoint_sub (L : ℝ) : |nearPoint L - center 1| = radius 1 * Real.exp L := by
  unfold nearPoint
  rw [add_sub_cancel_left, abs_of_pos (mul_pos (radius_pos 1) (Real.exp_pos L))]

theorem ell_one_nearPoint {L : ℝ} (hL : L ≤ 0) : ell 1 (nearPoint L) = L := by
  unfold ell
  rw [abs_nearPoint_sub, mul_div_cancel_left₀ _ (radius_pos 1).ne',
    ENNReal.log_ofReal_of_pos (Real.exp_pos L), Real.log_exp]
  exact min_eq_right (EReal.coe_nonpos.2 hL)

theorem active_nearPoint {L : ℝ} (hL : L ≤ 0) : ∀ i, i ≠ 1 → ell i (nearPoint L) = 0 :=
  fun _ hi => ell_eq_zero_of_ne (by
    rw [abs_nearPoint_sub]
    exact mul_le_of_le_one_right (radius_pos 1).le (Real.exp_le_one_iff.2 hL)) hi

/-- Near `p_1`, `f_{n,j} = max{2ℓ_1, (1 + 1/n)ℓ_1 - j}`. -/
theorem approx_nearPoint {n : ℕ} (hn : 1 ≤ n) (j : ℕ) {L : ℝ} (hL : L ≤ 0) :
    approx n j (nearPoint L) = ((max (2 * L) ((1 + 1 / (n : ℝ)) * L - j) : ℝ) : EReal) := by
  rw [approx_eq_of_active (active_nearPoint hL), if_pos (Finset.mem_Icc.2 ⟨le_rfl, hn⟩),
    ell_one_nearPoint hL, ← coe_two_eq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub]
  exact (EReal.coe_strictMono.monotone.map_max).symm

theorem active_center (k : ℕ) : ∀ i, i ≠ k → ell i (center k) = 0 :=
  fun _ hi => ell_eq_zero_of_ne (by simp [(radius_pos k).le]) hi

theorem active_one : ∀ i, i ≠ 0 → ell i 1 = 0 := by
  have h : (1 : ℝ) = center 0 := by simp [center]
  rw [h]
  exact active_center 0

/-- `f_{n,j}(1) = 0`. -/
theorem approx_one (n j : ℕ) : approx n j 1 = 0 := by
  rw [approx_eq_of_active active_one, if_neg (by simp)]

/-- `g(1) = 0`. -/
theorem limit_one : limit 1 = 0 := by
  rw [limit_eq_of_active active_one, if_neg (by norm_num)]

/-- `f_{N,j}(p_{N+1}) = 0`. -/
theorem approx_center (N j : ℕ) : approx N j (center (N + 1)) = 0 := by
  rw [approx_eq_of_active (active_center (N + 1)), if_neg (by simp)]

theorem ell_center (k : ℕ) : ell k (center k) = ⊥ := by
  simp [ell]

/-- `g(p_k) = -∞` for `k ≥ 1`. -/
theorem limit_center {k : ℕ} (hk : 1 ≤ k) : limit (center k) = ⊥ := by
  rw [limit_eq_of_active (active_center k), if_pos hk, ell_center]
  exact EReal.mul_bot_of_pos (by rw [← coe_two_eq]; exact EReal.coe_pos.2 two_pos)

/-! #### BJ22's hypotheses on `𝓕` -/

/-- The members of `𝓕` are continuous with values in `[-∞, ∞)` (indeed `[-∞, c]`). -/
theorem family_continuous {K : Type*} [TopologicalSpace K] {φ : K → ℝ} (hφ : Continuous φ) :
    ∀ F ∈ family φ, Continuous F ∧ ∀ y, F y ≠ ⊤ := by
  rintro F ⟨n, j, -, -, c, rfl⟩
  refine ⟨continuous_add_of_ne_top' ((continuous_approx n j).comp hφ) continuous_const
    (fun y => ne_top_of_le_ne_top EReal.zero_ne_top (approx_nonpos n j _))
    (fun _ => EReal.coe_ne_top c), fun y => ?_⟩
  exact ne_top_of_le_ne_top (EReal.coe_ne_top c)
    ((add_le_add (approx_nonpos n j (φ y)) le_rfl).trans (zero_add _).le)

/-- `𝓕` is stable under addition of real constants. -/
theorem family_add_const {K : Type*} (φ : K → ℝ) :
    ∀ F ∈ family φ, ∀ c : ℝ, (fun y => F y + (c : EReal)) ∈ family φ := by
  rintro F ⟨n, j, hn, hj, c', rfl⟩ c
  refine ⟨n, j, hn, hj, c' + c, ?_⟩
  funext y
  rw [EReal.coe_add, add_assoc]

theorem approx_mem_family {K : Type*} (φ : K → ℝ) {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    (fun y => approx n j (φ y)) ∈ family φ :=
  ⟨n, j, hn, hj, 0, by funext y; rw [EReal.coe_zero, add_zero]⟩

section Membership

universe x

variable {K : Type*} {S : Type*} {T : Type*} [TopologicalSpace T]

/-- **`g ∈ 𝓕̃̃`.** `g` is the limit of the decreasing sequence `g_n` (`n ≥ 1`), and each `g_n`
is the limit of the decreasing sequence `f_{n,j}` (`j ≥ 1`) in `𝓕`. Here `S`, `T` are arbitrary,
`𝓕_s = 𝓕` for every `s`, and `t = ρ(s₀)` is any point in the image of `ρ`. -/
theorem limit_mem_iterated (φ : K → ℝ) (ρ : S → T) (s₀ : S) :
    (fun y => limit (φ y)) ∈
      bj22DecrLimits.{x} (bj22DecrLimits.{x} (fun _ => family φ) ρ) id (ρ s₀) := by
  refine mem_bj22DecrLimits_of_seq
    (fun y => ne_top_of_le_ne_top EReal.zero_ne_top (limit_nonpos _)) (fun _ => ρ s₀)
    (fun n y => partialLimit (n + 1) (φ y)) (fun n => ?_) ?_ ?_ tendsto_const_nhds
  · refine mem_bj22DecrLimits_of_seq
      (fun y => ne_top_of_le_ne_top EReal.zero_ne_top (partialLimit_nonpos _ _)) (fun _ => s₀)
      (fun j y => approx (n + 1) (j + 1) (φ y))
      (fun j => approx_mem_family φ (Nat.le_add_left 1 n) (Nat.le_add_left 1 j)) ?_ ?_
      tendsto_const_nhds
    · intro j j' hjj' y
      exact approx_antitone (n + 1) (φ y) (Nat.add_le_add_right hjj' 1)
    · intro y
      obtain ⟨J, hJ⟩ := approx_eventually_eq (n + 1) (φ y)
      exact tendsto_const_nhds.congr'
        (eventually_atTop.2 ⟨J, fun j hj => (hJ (j + 1) (by omega)).symm⟩)
  · intro n m hnm y
    exact partialLimit_antitone (φ y) (Nat.add_le_add_right hnm 1)
  · intro y
    obtain ⟨N, hN⟩ := partialLimit_eventually_eq (φ y)
    exact tendsto_const_nhds.congr'
      (eventually_atTop.2 ⟨N, fun n hn => (hN (n + 1) (by omega)).symm⟩)

/-- The real-number core of the rate argument at `p_1`: if `b < a ≤ 2`, then for suitable
`L ≤ 0`, `max{2L, aL - j} + c < max{2L, bL - j'} + c'`. -/
private theorem exists_rate_gap {a b cα cβ jα jβ : ℝ} (hab : b < a) (ha2 : a ≤ 2)
    (hjα : 0 ≤ jα) :
    ∃ L : ℝ, L ≤ 0 ∧ max (2 * L) (a * L - jα) + cα < max (2 * L) (b * L - jβ) + cβ := by
  have hab' : 0 < a - b := sub_pos.2 hab
  have hC := le_abs_self (jβ + cα - cβ)
  have hC' := abs_nonneg (jβ + cα - cβ)
  refine ⟨-(|jβ + cα - cβ| + 1) / (a - b),
    div_nonpos_of_nonpos_of_nonneg (by linarith) hab'.le, ?_⟩
  set L := -(|jβ + cα - cβ| + 1) / (a - b) with hL
  have hL0 : L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hab'.le
  have hLab : (a - b) * L = -(|jβ + cα - cβ| + 1) := by
    rw [hL]; field_simp
  have h2a : 2 * L ≤ a * L := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ha2) hL0]
  have h2 : max (2 * L) (a * L - jα) ≤ a * L := max_le h2a (by linarith)
  have h3 : b * L - jβ ≤ max (2 * L) (b * L - jβ) := le_max_right _ _
  nlinarith

/-- **`g ∉ 𝓕̃`.** No decreasing net in `𝓕` converges pointwise to `g` (whatever `S`, `T`, `ρ`,
`t`, and whatever `φ : K → ℝ` whose image contains `[0, 1]`). -/
theorem limit_not_mem (φ : K → ℝ) (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ y, φ y = x) (ρ : S → T)
    (t : T) : (fun y => limit (φ y)) ∉ bj22DecrLimits.{x} (fun _ => family φ) ρ t := by
  rintro ⟨-, D, _, _, _, s, F, hF, hanti, hlim, -⟩
  simp only [family, Set.mem_ofPred_eq] at hF
  choose n j hn hj c hc using hF
  -- Step 1: along the net, `n` can only decrease (the rate `1 + 1/n` at `p_1`).
  have hA : ∀ α β, α ≤ β → n β ≤ n α := by
    intro α β hαβ
    by_contra hlt
    push Not at hlt
    have hab : 1 + 1 / (n β : ℝ) < 1 + 1 / (n α : ℝ) := by
      have h1 : (1 : ℝ) ≤ n α := by exact_mod_cast hn α
      have h2 : (n α : ℝ) < n β := by exact_mod_cast hlt
      have := one_div_lt_one_div_of_lt (by linarith) h2
      linarith
    obtain ⟨L, hL, hgap⟩ := exists_rate_gap (cα := c α) (cβ := c β) (jα := (j α : ℝ))
      (jβ := (j β : ℝ)) hab (mult_le_two (hn α)) (Nat.cast_nonneg _)
    obtain ⟨y, hy⟩ := hφ (nearPoint L) (nearPoint_mem_Icc hL)
    have h1 : F β y ≤ F α y := hanti hαβ y
    rw [hc β, hc α] at h1
    simp only [hy] at h1
    rw [approx_nearPoint (hn β) _ hL, approx_nearPoint (hn α) _ hL, ← EReal.coe_add,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    linarith
  -- Step 2: hence `n` is eventually constant, `= N`.
  classical
  obtain ⟨α₀⟩ := ‹Nonempty D›
  have hex : ∃ m, ∃ α, n α = m := ⟨n α₀, α₀, rfl⟩
  obtain ⟨α₁, hα₁⟩ := Nat.find_spec hex
  have hmin : ∀ β, n α₁ ≤ n β := fun β => by rw [hα₁]; exact Nat.find_min' hex ⟨β, rfl⟩
  have hconst : ∀ β, α₁ ≤ β → n β = n α₁ := fun β h => le_antisymm (hA _ _ h) (hmin β)
  -- Step 3: then the net takes the same value at `1` and at `p_{N+1}`, where `g` is `0`
  -- and `-∞` respectively.
  obtain ⟨y₁, hy₁⟩ := hφ 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨y₂, hy₂⟩ := hφ (center (n α₁ + 1)) (center_mem_Icc _)
  have heq : (fun β => F β y₁) =ᶠ[atTop] fun β => F β y₂ := by
    filter_upwards [mem_atTop α₁] with β hβ
    rw [hc β]
    simp only [hy₁, hy₂, hconst β hβ, approx_one, approx_center]
  have h1 := hlim y₁
  have h2 := hlim y₂
  simp only [hy₁, hy₂, limit_one, limit_center (Nat.le_add_left 1 _)] at h1 h2
  exact EReal.zero_ne_bot (tendsto_nhds_unique (h1.congr' heq) h2)

/-- **`g ∈ 𝓕̃̃` on `K = [0, 1]`**, with `S = T = Unit`. -/
theorem limit_mem_iterated_Icc :
    (fun y : Set.Icc (0 : ℝ) 1 => limit y) ∈
      bj22DecrLimits.{x}
        (bj22DecrLimits.{x} (fun _ : Unit => family (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
          (fun _ => ())) id () :=
  limit_mem_iterated _ _ ()

/-- **`g ∉ 𝓕̃` on `K = [0, 1]`**, with `S = T = Unit`. -/
theorem limit_not_mem_Icc :
    (fun y : Set.Icc (0 : ℝ) 1 => limit y) ∉
      bj22DecrLimits.{x} (fun _ : Unit => family (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
        (fun _ => ()) () :=
  limit_not_mem _ (fun x hx => ⟨⟨x, hx⟩, rfl⟩) _ _

end Membership

end BJ22Lemma46Counterexample

open BJ22Lemma46Counterexample in
/-- **BJ22's Lemma 4.6 is false** (blueprint `prop:nn-bj-lemma46-false`), in every choice of
universes: take `K = [0, 1]` (lifted to the universe `u`), `S` and `T` one point, and
`𝓕 = {f_{n,j} + c}`; then `g = ∑_{i ≥ 1} 2ℓ_i ∈ 𝓕̃̃ \ 𝓕̃`. -/
theorem not_bj22Lemma46.{u, v, w, x} : ¬ BJ22Lemma46Statement.{u, v, w, x} := by
  intro h
  let φ : ULift.{u} (Set.Icc (0 : ℝ) 1) → ℝ := fun y => y.down.val
  have hφc : Continuous φ := continuous_subtype_val.comp continuous_uliftDown
  have hφs : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ y, φ y = x := fun x hx => ⟨ULift.up ⟨x, hx⟩, rfl⟩
  have heq := h (ULift.{u} (Set.Icc (0 : ℝ) 1)) PUnit.{v + 1} (fun _ => family φ) PUnit.{w + 1}
    (fun _ => PUnit.unit) (fun _ => family_continuous hφc) (fun _ => family_add_const φ)
    PUnit.unit
  have hmem := limit_mem_iterated.{x} φ (fun _ : PUnit.{v + 1} => (PUnit.unit : PUnit.{w + 1}))
    PUnit.unit
  exact limit_not_mem φ hφs _ _ ((Set.ext_iff.1 heq _).1 hmem)

/-- The "in other words" form of BJ22's Lemma 4.6 is false as well. -/
theorem not_bj22Lemma46StatementExplicit.{u, v, w, x} :
    ¬ BJ22Lemma46StatementExplicit.{u, v, w, x} :=
  fun h => not_bj22Lemma46 (bj22Lemma46Statement_iff_explicit.2 h)

end EnvelopeProperty
