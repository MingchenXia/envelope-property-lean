/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Global.Radicial

/-!
# Ring-level structure of radicial integral extensions (Stacks 0CNA, 0CN7, 0CN9, 0CNC)

This file contains the ring-theoretic core of Stacks Project, Section 29.47 ("Universal
homeomorphisms of affine schemes"), in the form needed for Frobenius descent
(`thm:gl-frobenius-descent`, FHX Theorem 8.3 in characteristic `p`, `thm:normalization-reflection`)
and for the tower form of subintegrality (Stacks 0CND, `thm:gl-additive-powers`, characteristic
`0`).

Universal homeomorphisms are bypassed: we work
with the predicate `EnvelopeProperty.Algebra.IsRadicialIntegral A B`, which says that `A → B` is
injective and integral, that `Spec B → Spec A` is bijective, and that every residue field
extension `κ(q ∩ A) → κ(q)` is purely inseparable. For an injective ring map these conditions
say that `Spec B → Spec A` is integral, surjective and radicial, i.e. a universal homeomorphism
(Stacks 04DF, 01S4); this equivalence is not formalized and not needed. The residue field
condition is stated exactly as `lem:gl-radicial` (`EnvelopeProperty/Global/Radicial.lean`) proves
it, and `EnvelopeProperty.Algebra.IsRadicialIntegral.of_maxSpec_injective` builds the predicate
from the hypotheses of that lemma.

## Main results

* `EnvelopeProperty.Algebra.IsRadicialIntegral.subalgebra` (Stacks 0CN7): the predicate passes
  from `A ⊆ B` to `A ⊆ B'` for every `A`-subalgebra `B' ⊆ B`;
  `EnvelopeProperty.Algebra.IsRadicialIntegral.over_subalgebra`: it passes to `B' ⊆ B`.
* `EnvelopeProperty.exists_sq_cube_of_pow_mem_of_pow_succ_mem` (Stacks 0CNA): if `b ∉ A` and
  `bⁿ, bⁿ⁺¹ ∈ A`, some power `b' = bᵐ` satisfies `b' ∉ A`, `b'², b'³ ∈ A`.
* `EnvelopeProperty.exists_mul_not_mem_and_mul_pow_mem` and
  `EnvelopeProperty.exists_not_mem_and_mul_pow_mem_of_localization` (Stacks 0CN9, "clear
  denominators").
* `EnvelopeProperty.Algebra.IsRadicialIntegral.exists_sq_cube_or_prime` (Stacks 0CNC, the
  structure lemma): if `A ⊊ B` is radicial integral, there is `b ∈ B ∖ A` with either
  `b², b³ ∈ A`, or `ℓ b, b^ℓ ∈ A` for a prime number `ℓ`.

## Proof of 0CNC and deviations from Stacks

Stacks reduces to `B = A[b₀]` (0CN7), so that `B` is a finite `A`-module, takes a minimal prime
`𝔭` of the support of `B/A`, localizes at `𝔭` (0CN9), and argues in the local ring `A_𝔭` with the
ideal `I = Ann(B/A)`, whose radical is the maximal ideal. We do the same reduction, but never
form `B_𝔭`: every statement about `A_𝔭 ⊆ B_𝔭` is replaced by its elementwise meaning in `B`
("`y/1 ∈ A_𝔭`" becomes "`t y ∈ A` for some `t ∉ 𝔭`"). Precisely, let `I = {a : a B ⊆ A}` (the
annihilator of `B/A`, a proper ideal since `A ≠ B`), `𝔭` a minimal prime over `I`, and `𝔮` the
prime of `B` over `𝔭`.

1. Since `B` is finite and `I ⊆ 𝔭`, some `b ∈ B` has `t b ∉ A` for all `t ∉ 𝔭` (`B_𝔭 ≠ A_𝔭`).
2. If some `x ∈ 𝔮` has `t x ∉ A` for all `t ∉ 𝔭` (Stacks: `𝔪' ⊄ A_𝔭`), then `t xⁿ` lies in the
   `B`-ideal `𝔠 = {y : y B ⊆ A}` for some `t ∉ 𝔭`, `n`: otherwise a prime `Q ⊇ 𝔠` of `B` avoids
   `{t xⁿ}`; then `I ⊆ Q ∩ A ⊆ 𝔭`, so `Q ∩ A = 𝔭` by minimality and `Q = 𝔮` by injectivity on
   spectra, contradicting `x ∈ 𝔮` (Stacks: `𝔪' = √(IB)`). Clearing denominators (0CN9) and 0CNA
   give an element with square and cube in `A`.
3. Otherwise every `x ∈ 𝔮` has `t x ∈ A` for some `t ∉ 𝔭` (Stacks: `𝔪' = 𝔪`). The image of the
   element `b` of step 1 in `κ(𝔮)` is not in `κ(𝔭)`; pure inseparability gives a prime exponent
   `ℓ` (in characteristic `0` it would be in `κ(𝔭)`) and a power `b' = b^{ℓᵏ}` whose image is not
   in `κ(𝔭)` while that of `b'^ℓ` is. Then `ℓ b' ∈ 𝔮` and clearing denominators gives the second
   alternative.

Only the injectivity of `Spec B → Spec A` and the existence of the prime over `𝔭` are used, so
bijectivity on spectra can replace the homeomorphism condition.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

/-- **Radicial integral extensions.** `A → B` is injective and integral, `Spec B → Spec A` is
bijective, and every residue field extension `κ(q ∩ A) → κ(q)` is purely inseparable. For an
injective ring map this says that `Spec B → Spec A` is a universal homeomorphism (Stacks 04DF,
01S4); it is the hypothesis of Stacks 0CNC, 0CNF and (over `ℚ`) 0CND, and the conclusion of
`lem:gl-radicial` (see `EnvelopeProperty.Algebra.IsRadicialIntegral.of_maxSpec_injective`). The
residue field algebra is Mathlib's `Localization.AtPrime.algebraOfLiesOver`. -/
structure Algebra.IsRadicialIntegral (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    Prop where
  /-- `A → B` is injective. -/
  injective : Function.Injective (algebraMap A B)
  /-- `B` is integral over `A`. -/
  isIntegral : Algebra.IsIntegral A B
  /-- `Spec B → Spec A` is bijective. -/
  bijective_comap : Function.Bijective (PrimeSpectrum.comap (algebraMap A B))
  /-- The residue field extensions are purely inseparable. -/
  isPurelyInseparable (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    IsPurelyInseparable (q.under A).ResidueField q.ResidueField

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

namespace Algebra.IsRadicialIntegral

/-- The residue field condition at a prime `q` over an arbitrary prime `p` (with the
`Localization.AtPrime.algebraOfLiesOver` structure). -/
theorem isPurelyInseparable_of_liesOver (h : Algebra.IsRadicialIntegral A B) (p : Ideal A)
    [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    IsPurelyInseparable p.ResidueField q.ResidueField := by
  obtain rfl : p = q.under A := Ideal.LiesOver.over
  exact h.isPurelyInseparable q

/-- The residue field condition in Mathlib's general form: for `q` over `p` and any algebra
structure `Localization.AtPrime p → Localization.AtPrime q` satisfying
`Localization.AtPrime.IsLiesOverAlgebra p q`, `κ(q)/κ(p)` is purely inseparable. -/
theorem isPurelyInseparable_of_isLiesOverAlgebra (h : Algebra.IsRadicialIntegral A B)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [inst : Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    IsPurelyInseparable p.ResidueField q.ResidueField := by
  obtain rfl : inst = Localization.AtPrime.algebraOfLiesOver p q :=
    Algebra.algebra_ext _ _ fun x => by
      rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
      rfl
  exact h.isPurelyInseparable_of_liesOver p q

/-- **Constructor from `lem:gl-radicial`.** Let `A ⊆ B` be algebras over an algebraically closed
field `k`, with `A` of finite type over `k` and `B` finite over `A`. If `MaxSpec B → MaxSpec A` is
injective, then `A ⊆ B` is radicial integral
(`EnvelopeProperty.bijective_comap_of_maxSpec_injective` and
`EnvelopeProperty.isPurelyInseparable_residueField_under`). -/
theorem of_maxSpec_injective {k : Type*} [Field k] [IsAlgClosed k] [Algebra k A] [Algebra k B]
    [IsScalarTower k A B] [Algebra.FiniteType k A] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    Algebra.IsRadicialIntegral A B where
  injective := hinj
  isIntegral := Algebra.IsIntegral.of_finite A B
  bijective_comap := bijective_comap_of_maxSpec_injective (k := k) hinj hmax
  isPurelyInseparable q _ := isPurelyInseparable_residueField_under (k := k) hmax q

end Algebra.IsRadicialIntegral

/-- Lying over for an integral extension with injective structure map. -/
theorem exists_comap_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (P : Ideal R) [P.IsPrime] :
    ∃ Q : Ideal S, Q.IsPrime ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  exact ⟨Q, hQ, hQP⟩

namespace Algebra.IsRadicialIntegral

/-- **Subalgebras inherit the property** (Stacks 0CN7, ring-level form). If `A ⊆ B` is radicial
integral, so is `A ⊆ B'` for every `A`-subalgebra `B'` of `B`. Primes of `B'` lift to `B`
(lying over), which gives injectivity on spectra, and `κ(q ∩ A) ⊆ κ(q ∩ B') ⊆ κ(q)` gives pure
inseparability (`IsPurelyInseparable.tower_bot`). -/
theorem subalgebra (h : Algebra.IsRadicialIntegral A B) (S : Subalgebra A B) :
    Algebra.IsRadicialIntegral A S := by
  have := h.isIntegral
  have hinjS : Function.Injective (algebraMap A S) := fun x y hxy =>
    h.injective (congrArg Subtype.val hxy)
  have hint : Algebra.IsIntegral A S := Algebra.IsIntegral.of_injective S.val Subtype.val_injective
  have hBS : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top A
  have hlift : ∀ (q : Ideal S) [q.IsPrime], ∃ Q : Ideal B, Q.IsPrime ∧
      Q.comap (algebraMap S B) = q := fun q _ =>
    exists_comap_eq_of_isIntegral_of_injective Subtype.val_injective q
  refine ⟨hinjS, hint, ⟨fun q₁ q₂ h12 => ?_, fun P => ?_⟩, fun q _ => ?_⟩
  · obtain ⟨Q₁, hQ₁, hQ₁q⟩ := hlift q₁.asIdeal
    obtain ⟨Q₂, hQ₂, hQ₂q⟩ := hlift q₂.asIdeal
    have hQ : (⟨Q₁, hQ₁⟩ : PrimeSpectrum B) = ⟨Q₂, hQ₂⟩ := h.bijective_comap.1 <|
      PrimeSpectrum.ext <| by
        change Q₁.comap (algebraMap A B) = Q₂.comap (algebraMap A B)
        rw [IsScalarTower.algebraMap_eq A S B, ← Ideal.comap_comap, ← Ideal.comap_comap, hQ₁q,
          hQ₂q]
        exact congrArg PrimeSpectrum.asIdeal h12
    ext1
    rw [← hQ₁q, ← hQ₂q]
    exact congrArg (fun Q : PrimeSpectrum B => Q.asIdeal.comap (algebraMap S B)) hQ
  · obtain ⟨Q, hQ, hQP⟩ := exists_comap_eq_of_isIntegral_of_injective hinjS P.asIdeal
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩
  · obtain ⟨Q, hQ, hQq⟩ := hlift q
    have : Q.LiesOver q := ⟨hQq.symm⟩
    have : Q.LiesOver (q.under A) := Ideal.LiesOver.trans Q q (q.under A)
    let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    let := Localization.AtPrime.algebraOfLiesOver q Q
    let := Localization.AtPrime.algebraOfLiesOver (q.under A) Q
    have := h.isPurelyInseparable_of_liesOver (q.under A) Q
    exact IsPurelyInseparable.tower_bot (q.under A).ResidueField q.ResidueField Q.ResidueField

/-- **Passing to an intermediate ring.** If `A ⊆ B` is radicial integral and `B'` is an
`A`-subalgebra of `B`, then `B' ⊆ B` is radicial integral (`κ(q ∩ A) ⊆ κ(q ∩ B') ⊆ κ(q)` and
`IsPurelyInseparable.tower_top`). This is an implicit step of the proof of Stacks 0CNF. -/
theorem over_subalgebra (h : Algebra.IsRadicialIntegral A B) (S : Subalgebra A B) :
    Algebra.IsRadicialIntegral S B := by
  have := h.isIntegral
  have hBS : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top A
  refine ⟨Subtype.val_injective, hBS, ⟨fun Q₁ Q₂ h12 => h.bijective_comap.1 ?_, fun P => ?_⟩,
    fun Q _ => ?_⟩
  · ext1
    change Q₁.asIdeal.comap (algebraMap A B) = Q₂.asIdeal.comap (algebraMap A B)
    rw [IsScalarTower.algebraMap_eq A S B, ← Ideal.comap_comap, ← Ideal.comap_comap]
    exact congrArg (fun P : PrimeSpectrum S => P.asIdeal.comap (algebraMap A S)) h12
  · obtain ⟨Q, hQ, hQP⟩ :=
      exists_comap_eq_of_isIntegral_of_injective Subtype.val_injective P.asIdeal
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩
  · let := Localization.AtPrime.algebraOfLiesOver (Q.under S) Q
    have : Q.LiesOver ((Q.under S).under A) := Ideal.LiesOver.trans Q (Q.under S) _
    let := Localization.AtPrime.algebraOfLiesOver ((Q.under S).under A) (Q.under S)
    let := Localization.AtPrime.algebraOfLiesOver ((Q.under S).under A) Q
    have := h.isPurelyInseparable_of_liesOver ((Q.under S).under A) Q
    exact IsPurelyInseparable.tower_top ((Q.under S).under A).ResidueField (Q.under S).ResidueField
      Q.ResidueField

end Algebra.IsRadicialIntegral

/-! ### Stacks 0CNA -/

/-- **Stacks 0CNA.** Let `S` be a submonoid (e.g. a subring) of a monoid `M` and `b ∉ S` with
`bⁿ, bⁿ⁺¹ ∈ S`. Then some power `b' = bᵐ`, `m > 0`, satisfies `b' ∉ S` and `b'², b'³ ∈ S`.
All `bʲ` with `j ≥ n²` lie in `S`, and `m` is the largest exponent with `bᵐ ∉ S`. (Stacks assumes
`n ≥ 2`; for `n ≤ 1` the hypotheses force `b ∈ S`.) -/
theorem exists_sq_cube_of_pow_mem_of_pow_succ_mem {M σ : Type*} [Monoid M] [SetLike σ M]
    [SubmonoidClass σ M] {S : σ} {b : M} (hb : b ∉ S) {n : ℕ} (h₁ : b ^ n ∈ S)
    (h₂ : b ^ (n + 1) ∈ S) :
    ∃ m : ℕ, 0 < m ∧ b ^ m ∉ S ∧ (b ^ m) ^ 2 ∈ S ∧ (b ^ m) ^ 3 ∈ S := by
  classical
  have hn : n ≠ 0 := by
    rintro rfl
    exact hb (by simpa using h₂)
  have hlarge : ∀ j, n * n ≤ j → b ^ j ∈ S := by
    intro j hj
    have key : ∀ q r : ℕ, r < n → n * n ≤ n * q + r → r ≤ q := by
      intro q r hr hle
      by_contra hlt
      have h2 : n * (q + 1) ≤ n * n := Nat.mul_le_mul_left n (by omega)
      rw [mul_add, mul_one] at h2
      omega
    obtain ⟨q, r, hr, hrq, rfl⟩ : ∃ q r, r < n ∧ r ≤ q ∧ j = n * q + r := by
      have h1 := Nat.div_add_mod j n
      have h3 := Nat.mod_lt j (Nat.pos_of_ne_zero hn)
      exact ⟨j / n, j % n, h3, key _ _ h3 (h1.symm ▸ hj), h1.symm⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrq
    have : n * (r + d) + r = n * d + (n + 1) * r := by ring
    rw [this, pow_add, pow_mul, pow_mul]
    exact mul_mem (pow_mem h₁ _) (pow_mem h₂ _)
  set N := n * n
  have h1N : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (mul_ne_zero hn hn)
  let P : ℕ → Prop := fun i => b ^ i ∉ S
  have hP1 : P 1 := by simpa [P] using hb
  set m := Nat.findGreatest P N
  have hPm : P m := Nat.findGreatest_spec h1N hP1
  have hm0 : 0 < m := by
    refine Nat.pos_of_ne_zero fun h0 => hPm ?_
    rw [h0, pow_zero]
    exact one_mem S
  have hgt : ∀ k, m < k → b ^ k ∈ S := by
    intro k hk
    by_cases hkN : k ≤ N
    · exact not_not.1 (Nat.findGreatest_is_greatest hk hkN)
    · exact hlarge k (by omega)
  refine ⟨m, hm0, hPm, ?_, ?_⟩
  · rw [← pow_mul]
    exact hgt _ (by omega)
  · rw [← pow_mul]
    exact hgt _ (by omega)

/-- If `b², b³ ∈ S` for a submonoid `S`, then `bᵐ ∈ S` for every `m ≥ 2` (write `m = 2a + 3c`). -/
theorem pow_mem_of_sq_mem_of_cube_mem {M σ : Type*} [Monoid M] [SetLike σ M]
    [SubmonoidClass σ M] {S : σ} {b : M} (h₂ : b ^ 2 ∈ S) (h₃ : b ^ 3 ∈ S) {m : ℕ}
    (hm : 2 ≤ m) : b ^ m ∈ S := by
  obtain ⟨a, c, rfl⟩ : ∃ a c, m = 2 * a + 3 * c := by
    rcases Nat.even_or_odd' m with ⟨a, ha | ha⟩
    · exact ⟨a, 0, by omega⟩
    · exact ⟨a - 1, 1, by omega⟩
  rw [pow_add, pow_mul, pow_mul]
  exact mul_mem (pow_mem h₂ a) (pow_mem h₃ c)

/-- Membership in the image of `B' → B` for an `A`-subalgebra `B'` of `B`. -/
theorem mem_range_algebraMap_subalgebra_iff (S : Subalgebra A B) {x : B} :
    x ∈ (algebraMap S B).range ↔ x ∈ S :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-! ### Stacks 0CN9: clearing denominators -/

/-- **Clearing denominators** (Stacks 0CN9, elementwise form). Let `M ⊆ A` be a multiplicative
subset and `y ∈ B` such that `s y ∉ A` for all `s ∈ M` ("`y/1 ∉ M⁻¹A`"). Suppose finitely many
conditions `c_j y^{e_j} ∈ M⁻¹A` (with `e_j ≥ 1`) hold, i.e. `s_j c_j y^{e_j} ∈ A` for some
`s_j ∈ M`. Then a single `s ∈ M` satisfies `s y ∉ A` and `c_j (s y)^{e_j} ∈ A` for all `j`. -/
theorem exists_mul_not_mem_and_mul_pow_mem {ι : Type*} (M : Submonoid A) {y : B}
    (hy : ∀ s ∈ M, algebraMap A B s * y ∉ (algebraMap A B).range) (J : Finset ι) (c : ι → B)
    (e : ι → ℕ) (he : ∀ j ∈ J, e j ≠ 0)
    (h : ∀ j ∈ J, ∃ s ∈ M, algebraMap A B s * (c j * y ^ e j) ∈ (algebraMap A B).range) :
    ∃ s ∈ M, algebraMap A B s * y ∉ (algebraMap A B).range ∧
      ∀ j ∈ J, c j * (algebraMap A B s * y) ^ e j ∈ (algebraMap A B).range := by
  classical
  choose! s hsM hs using h
  have hprod : ∏ j ∈ J, s j ∈ M := prod_mem fun j hj => hsM j hj
  refine ⟨∏ j ∈ J, s j, hprod, hy _ hprod, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, e j = k + 1 := ⟨e j - 1, by have := he j hj; omega⟩
  rw [← Finset.mul_prod_erase J s hj]
  have : c j * (algebraMap A B (s j * ∏ i ∈ J.erase j, s i) * y) ^ e j =
      algebraMap A B ((s j * ∏ i ∈ J.erase j, s i) ^ k * ∏ i ∈ J.erase j, s i) *
        (algebraMap A B (s j) * (c j * y ^ e j)) := by
    rw [hk]
    simp only [map_mul, map_pow]
    ring
  rw [this]
  exact mul_mem (RingHom.mem_range_self _ _) (hs j hj)

/-- **Stacks 0CN9** (special elements and localization). Let `M ⊆ A` be a multiplicative subset,
`Aₘ = M⁻¹A`, `Bₘ = M⁻¹B` with the induced map `Aₘ → Bₘ`, and let `x ∈ Bₘ` not in the image of
`Aₘ` be such that `c_j x^{e_j}` lies in the image of `Aₘ` for finitely many `c_j ∈ B` and
exponents `e_j ≥ 1`. Then `x = y/s` with `s ∈ M` and `y ∈ B` such that `y` is not in the image of
`A` and every `c_j y^{e_j}` is. (Stacks states this for `A ⊆ B` and the conditions
`b_i x^i ∈ S⁻¹A`, `1 ≤ i ≤ n`; injectivity of `A → B` is not needed.) -/
theorem exists_not_mem_and_mul_pow_mem_of_localization {ι : Type*} (M : Submonoid A)
    (Aₘ Bₘ : Type*) [CommRing Aₘ] [CommRing Bₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]
    [Algebra B Bₘ] [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ] [Algebra Aₘ Bₘ]
    [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ] {x : Bₘ}
    (hx : x ∉ (algebraMap Aₘ Bₘ).range) (J : Finset ι) (c : ι → B) (e : ι → ℕ)
    (he : ∀ j ∈ J, e j ≠ 0)
    (h : ∀ j ∈ J, algebraMap B Bₘ (c j) * x ^ e j ∈ (algebraMap Aₘ Bₘ).range) :
    ∃ y : B, ∃ s ∈ M, algebraMap B Bₘ y = algebraMap A Bₘ s * x ∧
      y ∉ (algebraMap A B).range ∧ ∀ j ∈ J, c j * y ^ e j ∈ (algebraMap A B).range := by
  obtain ⟨⟨y₀, u⟩, hy₀⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B M) x
  obtain ⟨s₀, hs₀, hu⟩ := u.2
  have hy₀' : algebraMap B Bₘ y₀ = algebraMap A Bₘ s₀ * x := by
    rw [← hy₀, mul_comm, IsScalarTower.algebraMap_apply A B Bₘ, hu]
  have hunit : ∀ s ∈ M, IsUnit (algebraMap A Bₘ s) := fun s hs => by
    rw [IsScalarTower.algebraMap_apply A B Bₘ]
    exact IsLocalization.map_units Bₘ
      (⟨algebraMap A B s, s, hs, rfl⟩ : Algebra.algebraMapSubmonoid B M)
  have hinv : ∀ s (hs : s ∈ M),
      algebraMap Aₘ Bₘ (IsLocalization.mk' Aₘ 1 ⟨s, hs⟩) * algebraMap A Bₘ s = 1 := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply A Aₘ Bₘ s, ← map_mul, IsLocalization.mk'_spec, map_one,
      map_one]
  -- the image of `z ∈ B` lies in the image of `Aₘ` iff `s z ∈ A` for some `s ∈ M`
  have key : ∀ z : B, algebraMap B Bₘ z ∈ (algebraMap Aₘ Bₘ).range →
      ∃ s ∈ M, algebraMap A B s * z ∈ (algebraMap A B).range := by
    rintro z ⟨w, hw⟩
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj M w
    have h1 : algebraMap B Bₘ (algebraMap A B t * z) =
        algebraMap B Bₘ (algebraMap A B a) := by
      rw [map_mul, ← hw, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A Aₘ Bₘ, IsScalarTower.algebraMap_apply A Aₘ Bₘ a, ← hat,
        map_mul, mul_comm]
    obtain ⟨⟨v, r, hr, rfl⟩, hv⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid B M) Bₘ).1 h1
    refine ⟨r * t, M.mul_mem hr t.2, r * a, ?_⟩
    rw [map_mul, map_mul, mul_assoc]
    exact hv.symm
  have key' : ∀ z : B, ∀ s ∈ M, algebraMap A B s * z ∈ (algebraMap A B).range →
      algebraMap B Bₘ z ∈ (algebraMap Aₘ Bₘ).range := by
    rintro z s hs ⟨a, ha⟩
    refine ⟨algebraMap A Aₘ a * IsLocalization.mk' Aₘ 1 ⟨s, hs⟩, ?_⟩
    apply (hunit s hs).mul_left_cancel
    rw [map_mul, mul_comm (algebraMap A Bₘ s), mul_assoc, hinv, mul_one,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B Bₘ,
      IsScalarTower.algebraMap_apply A B Bₘ s, ← map_mul, ha]
  have hy : ∀ s ∈ M, algebraMap A B s * y₀ ∉ (algebraMap A B).range := by
    intro s hs hsy
    obtain ⟨w, hw⟩ := key' y₀ s hs hsy
    refine hx ⟨w * IsLocalization.mk' Aₘ 1 ⟨s₀, hs₀⟩, ?_⟩
    rw [map_mul, hw, hy₀', mul_comm (algebraMap A Bₘ s₀), mul_assoc, mul_comm (algebraMap A Bₘ s₀),
      hinv, mul_one]
  have hcond : ∀ j ∈ J, ∃ s ∈ M, algebraMap A B s * (c j * y₀ ^ e j) ∈ (algebraMap A B).range := by
    intro j hj
    apply key
    rw [map_mul, map_pow, hy₀', mul_pow, mul_left_comm, ← map_pow,
      IsScalarTower.algebraMap_apply A Aₘ Bₘ]
    exact mul_mem (RingHom.mem_range_self _ _) (h j hj)
  obtain ⟨s, hs, hsy, hpow⟩ := exists_mul_not_mem_and_mul_pow_mem M hy J c e he hcond
  refine ⟨algebraMap A B s * y₀, s * s₀, M.mul_mem hs hs₀, ?_, hsy, hpow⟩
  rw [map_mul, hy₀', ← IsScalarTower.algebraMap_apply, map_mul, mul_assoc]

/-! ### Stacks 0CNC -/

/-- **Stacks 0CNC, finite case.** Let `A → B` be a ring map with `B` a finite `A`-module,
`Spec B → Spec A` bijective, and purely inseparable residue field extensions. If `A → B` is not
surjective, there is `b ∈ B` not in the image of `A` such that either `b², b³` are in the image,
or `ℓ b, b^ℓ` are in the image for some prime number `ℓ`. See the module docstring for the
proof. -/
theorem exists_sq_cube_or_prime_of_finite [Module.Finite A B]
    (hcomap : Function.Bijective (PrimeSpectrum.comap (algebraMap A B)))
    (hpi : ∀ (q : Ideal B) [q.IsPrime],
      letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
      IsPurelyInseparable (q.under A).ResidueField q.ResidueField)
    (hne : ¬ Function.Surjective (algebraMap A B)) :
    ∃ b : B, b ∉ (algebraMap A B).range ∧
      ((b ^ 2 ∈ (algebraMap A B).range ∧ b ^ 3 ∈ (algebraMap A B).range) ∨
        ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : B) * b ∈ (algebraMap A B).range ∧
          b ^ ℓ ∈ (algebraMap A B).range) := by
  classical
  set R := (algebraMap A B).range with hR
  -- `I = Ann_A(B/A)`
  let I : Ideal A :=
    { carrier := {a | ∀ z : B, algebraMap A B a * z ∈ R}
      add_mem' := fun {a a'} ha ha' z => by
        rw [map_add, add_mul]
        exact add_mem (ha z) (ha' z)
      zero_mem' := fun z => by
        rw [map_zero, zero_mul]
        exact zero_mem _
      smul_mem' := fun c a ha z => by
        rw [smul_eq_mul, map_mul, mul_assoc]
        exact mul_mem (RingHom.mem_range_self _ _) (ha z) }
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    apply hne
    intro z
    obtain ⟨a, ha⟩ := h1 z
    exact ⟨a, by rw [ha, map_one, one_mul]⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨p, ⟨⟨hp, hIp⟩, hpmin⟩, -⟩ := Ideal.exists_minimalPrimes_le (J := m) hIm
  obtain ⟨⟨q, hq⟩, hqp⟩ := hcomap.2 ⟨p, hp⟩
  have hqp' : q.comap (algebraMap A B) = p := congrArg PrimeSpectrum.asIdeal hqp
  -- Step 1: `B_𝔭 ≠ A_𝔭`.
  have F1 : ∃ b : B, ∀ t ∉ p, algebraMap A B t * b ∉ R := by
    by_contra! H
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
    choose t ht htR using fun i => H (g i)
    have hT : (∏ i, t i) ∈ p.primeCompl := prod_mem fun i _ => ht i
    apply hT
    apply hIp
    intro z
    have hz : z ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i), map_mul,
        mul_comm (algebraMap A B (t i)), mul_assoc]
      exact mul_mem (RingHom.mem_range_self _ _) (htR i)
    | zero =>
      rw [mul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, mul_left_comm]
      exact mul_mem (RingHom.mem_range_self _ _) hx
  by_cases C1 : ∃ x ∈ q, ∀ t ∉ p, algebraMap A B t * x ∉ R
  · -- Step 2: the prime over `𝔭` is not contained in `A_𝔭`.
    obtain ⟨x, hxq, hx⟩ := C1
    let 𝔠 : Ideal B :=
      { carrier := {y | ∀ z : B, y * z ∈ R}
        add_mem' := fun {y y'} hy hy' z => by
          rw [add_mul]
          exact add_mem (hy z) (hy' z)
        zero_mem' := fun z => by
          rw [zero_mul]
          exact zero_mem _
        smul_mem' := fun c y hy z => by
          rw [smul_eq_mul, mul_assoc, mul_left_comm]
          exact hy (c * z) }
    have F2 : ∃ t ∉ p, ∃ n : ℕ, algebraMap A B t * x ^ n ∈ 𝔠 := by
      by_contra! H
      let S : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl ⊔ Submonoid.powers x
      have hdisj : Disjoint (𝔠 : Set B) S := by
        rw [Set.disjoint_left]
        intro y hy hyS
        obtain ⟨u, hu, v, hv, rfl⟩ := Submonoid.mem_sup.1 hyS
        obtain ⟨t, ht, rfl⟩ := hu
        obtain ⟨n, rfl⟩ := hv
        exact H t ht n hy
      obtain ⟨Q, hQ, h𝔠Q, hQS⟩ := Ideal.exists_le_prime_disjoint 𝔠 S hdisj
      have h1 : I ≤ Q.comap (algebraMap A B) := fun a ha =>
        h𝔠Q (show algebraMap A B a ∈ 𝔠 from ha)
      have h2 : Q.comap (algebraMap A B) ≤ p := fun a ha => by
        by_contra hap
        exact Set.disjoint_left.1 hQS ha (Submonoid.mem_sup_left ⟨a, hap, rfl⟩)
      have h3 : Q.comap (algebraMap A B) = p :=
        le_antisymm h2 (hpmin ⟨Ideal.IsPrime.comap _, h1⟩ h2)
      have hQq : Q = q := congrArg PrimeSpectrum.asIdeal
        (hcomap.1 (a₁ := ⟨Q, hQ⟩) (a₂ := ⟨q, hq⟩) (PrimeSpectrum.ext (h3.trans hqp'.symm)))
      exact Set.disjoint_left.1 hQS (hQq ▸ hxq) (Submonoid.mem_sup_right (Submonoid.mem_powers x))
    obtain ⟨t, ht, n, htn⟩ := F2
    obtain ⟨s, -, hsx, hpow⟩ := exists_mul_not_mem_and_mul_pow_mem p.primeCompl hx
      (Finset.univ : Finset (Fin 2)) (fun _ => 1) ![n + 1, n + 2] (by simp) (by
        intro j _
        refine ⟨t, ht, ?_⟩
        fin_cases j
        · show algebraMap A B t * (1 * x ^ (n + 1)) ∈ R
          rw [one_mul, pow_succ, ← mul_assoc]
          exact htn x
        · show algebraMap A B t * (1 * x ^ (n + 2)) ∈ R
          rw [one_mul, pow_add, ← mul_assoc]
          exact htn _)
    obtain ⟨k, -, hk, hk2, hk3⟩ := exists_sq_cube_of_pow_mem_of_pow_succ_mem hsx (n := n + 1)
      (by simpa using hpow 0 (by simp)) (by simpa using hpow 1 (by simp))
    exact ⟨_, hk, Or.inl ⟨hk2, hk3⟩⟩
  · -- Step 3: the prime over `𝔭` is contained in `A_𝔭`; use the residue fields.
    push Not at C1
    obtain rfl : p = q.under A := hqp'.symm
    let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    have hpiq := hpi q
    have hcomm : ∀ a : A, algebraMap (q.under A).ResidueField q.ResidueField
        (algebraMap A (q.under A).ResidueField a) = algebraMap B q.ResidueField (algebraMap A B a) :=
      fun a => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hfrac : ∀ k : (q.under A).ResidueField, ∃ a : A, ∃ s ∉ q.under A,
        algebraMap A (q.under A).ResidueField s * k = algebraMap A (q.under A).ResidueField a := by
      intro k
      obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective k
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (q.under A).primeCompl z
      refine ⟨a, s, s.2, ?_⟩
      rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (q.under A)),
        IsScalarTower.algebraMap_apply A (Localization.AtPrime (q.under A)) _ a,
        ← IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec']
    -- membership of the image in `κ(𝔭)` is membership in `A_𝔭`
    have L : ∀ y : B, algebraMap B q.ResidueField y ∈
        (algebraMap (q.under A).ResidueField q.ResidueField).range →
        ∃ u ∉ q.under A, algebraMap A B u * y ∈ R := by
      rintro y ⟨k, hk⟩
      obtain ⟨a, s, hs, hsk⟩ := hfrac k
      have hmem : algebraMap A B s * y - algebraMap A B a ∈ q := by
        rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, map_mul, ← hcomm, ← hcomm, ← hk,
          ← map_mul, hsk, sub_self]
      obtain ⟨t, ht, htR⟩ := C1 _ hmem
      refine ⟨t * s, (q.under A).primeCompl.mul_mem ht hs, ?_⟩
      have : algebraMap A B (t * s) * y = algebraMap A B t * (algebraMap A B s * y -
          algebraMap A B a) + algebraMap A B (t * a) := by
        simp only [map_mul]
        ring
      rw [this]
      exact add_mem htR (RingHom.mem_range_self _ _)
    have L' : ∀ y : B, ∀ u ∉ q.under A, algebraMap A B u * y ∈ R →
        algebraMap B q.ResidueField y ∈
          (algebraMap (q.under A).ResidueField q.ResidueField).range := by
      rintro y u hu ⟨a, ha⟩
      have hu0 : algebraMap A (q.under A).ResidueField u ≠ 0 := fun h0 =>
        hu (Ideal.algebraMap_residueField_eq_zero.1 h0)
      have hu0' : algebraMap B q.ResidueField (algebraMap A B u) ≠ 0 := by
        rw [← hcomm]
        exact (map_ne_zero _).2 hu0
      refine ⟨algebraMap A (q.under A).ResidueField a / algebraMap A (q.under A).ResidueField u,
        ?_⟩
      rw [map_div₀, hcomm, hcomm, ha, map_mul, mul_div_cancel_left₀ _ hu0']
    obtain ⟨b, hb⟩ := F1
    have hbK : algebraMap B q.ResidueField b ∉
        (algebraMap (q.under A).ResidueField q.ResidueField).range := fun hmem => by
      obtain ⟨u, hu, huR⟩ := L b hmem
      exact hb u hu huR
    obtain ⟨ℓ, hℓ⟩ := ExpChar.exists (q.under A).ResidueField
    have hex : ∃ n : ℕ, algebraMap B q.ResidueField b ^ ℓ ^ n ∈
        (algebraMap (q.under A).ResidueField q.ResidueField).range :=
      IsPurelyInseparable.pow_mem _ ℓ _
    have hℓp : ℓ.Prime := by
      rcases expChar_is_prime_or_one (q.under A).ResidueField ℓ with h | rfl
      · exact h
      · exfalso
        obtain ⟨n, hn⟩ := hex
        rw [one_pow, pow_one] at hn
        exact hbK hn
    have : CharP (q.under A).ResidueField ℓ := by
      cases hℓ with
      | zero => exact absurd hℓp Nat.not_prime_one
      | prime _ => assumption
    have hN : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, pow_one] at this
      exact hbK this
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hb'1 : algebraMap B q.ResidueField (b ^ ℓ ^ k) ∉
        (algebraMap (q.under A).ResidueField q.ResidueField).range := by
      rw [map_pow]
      exact Nat.find_min hex (by omega)
    have hb'2 : algebraMap B q.ResidueField ((b ^ ℓ ^ k) ^ ℓ) ∈
        (algebraMap (q.under A).ResidueField q.ResidueField).range := by
      rw [map_pow, map_pow, ← pow_mul, ← pow_succ, ← hk]
      exact Nat.find_spec hex
    have ha : ∀ u ∈ (q.under A).primeCompl, algebraMap A B u * b ^ ℓ ^ k ∉ R :=
      fun u hu huR => hb'1 (L' _ u hu huR)
    obtain ⟨t₁, ht₁, ht₁R⟩ := L _ hb'2
    have hℓq : (ℓ : B) * b ^ ℓ ^ k ∈ q := by
      apply q.mul_mem_right
      rw [← map_natCast (algebraMap A B), ← Ideal.mem_comap]
      change (ℓ : A) ∈ q.under A
      rw [← Ideal.algebraMap_residueField_eq_zero, map_natCast, CharP.cast_eq_zero]
    obtain ⟨t₂, ht₂, ht₂R⟩ := C1 _ hℓq
    obtain ⟨s, -, hsb, hpow⟩ := exists_mul_not_mem_and_mul_pow_mem (q.under A).primeCompl ha
      (Finset.univ : Finset (Fin 2)) ![(ℓ : B), 1] ![1, ℓ]
      (by intro j _; fin_cases j <;> simp [hℓp.ne_zero]) (by
        intro j _
        fin_cases j
        · exact ⟨t₂, ht₂, by simpa [hR] using ht₂R⟩
        · exact ⟨t₁, ht₁, by simpa [hR] using ht₁R⟩)
    exact ⟨_, hsb, Or.inr ⟨ℓ, hℓp, by simpa [hR] using hpow 0 (by simp),
      by simpa [hR] using hpow 1 (by simp)⟩⟩

/-- **Stacks 0CNC (structure lemma).** Let `A ⊆ B` be a radicial integral extension
(`EnvelopeProperty.Algebra.IsRadicialIntegral`). If `A ≠ B`, there is `b ∈ B ∖ A` with either
`b², b³ ∈ A`, or `ℓ b, b^ℓ ∈ A` for some prime number `ℓ`. We reduce to `B = A[b₀]` for some
`b₀ ∉ A` (0CN7: `EnvelopeProperty.Algebra.IsRadicialIntegral.subalgebra`), which is finite over
`A`, and apply `EnvelopeProperty.exists_sq_cube_or_prime_of_finite`. -/
theorem Algebra.IsRadicialIntegral.exists_sq_cube_or_prime (h : Algebra.IsRadicialIntegral A B)
    (hne : ¬ Function.Surjective (algebraMap A B)) :
    ∃ b : B, b ∉ (algebraMap A B).range ∧
      ((b ^ 2 ∈ (algebraMap A B).range ∧ b ^ 3 ∈ (algebraMap A B).range) ∨
        ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : B) * b ∈ (algebraMap A B).range ∧
          b ^ ℓ ∈ (algebraMap A B).range) := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : B, b₀ ∉ (algebraMap A B).range := by
    by_contra! H
    exact hne fun b => H b
  let S := Algebra.adjoin A {b₀}
  have hS := h.subalgebra S
  have : Module.Finite A S :=
    Algebra.finite_adjoin_simple_of_isIntegral (h.isIntegral.isIntegral b₀)
  have hneS : ¬ Function.Surjective (algebraMap A S) := fun hs => by
    obtain ⟨a, ha⟩ := hs ⟨b₀, Algebra.subset_adjoin rfl⟩
    exact hb₀ ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨b, hb, hcases⟩ :=
    exists_sq_cube_or_prime_of_finite hS.bijective_comap hS.isPurelyInseparable hneS
  have hmem : ∀ x : S, (x : B) ∈ (algebraMap A B).range ↔ x ∈ (algebraMap A S).range :=
    fun x => ⟨fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩, fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩⟩
  refine ⟨b, (hmem b).not.2 hb, ?_⟩
  rcases hcases with ⟨h2, h3⟩ | ⟨ℓ, hℓ, h1, h2⟩
  · exact Or.inl ⟨(hmem (b ^ 2)).2 h2, (hmem (b ^ 3)).2 h3⟩
  · exact Or.inr ⟨ℓ, hℓ, (hmem ((ℓ : S) * b)).2 h1, (hmem (b ^ ℓ)).2 h2⟩

end EnvelopeProperty
