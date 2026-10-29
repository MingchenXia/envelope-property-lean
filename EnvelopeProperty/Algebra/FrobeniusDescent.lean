/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Algebra.RadicialStructure

/-!
# Frobenius descent for radicial integral extensions (Stacks 0CNF, characteristic `p`)

This file proves `thm:gl-frobenius-descent` of the global chapter (`global.tex`; FHX,
*The envelope property for unibranch projective varieties*, proof of Theorem 8.3
(`thm:normalization-reflection`) in positive characteristic, which cites [Stacks, Tag 0CNF]).

Let `p` be a prime and `A ⊆ B` a radicial integral extension
(`EnvelopeProperty.Algebra.IsRadicialIntegral`: integral, bijective on spectra, purely
inseparable residue field extensions) with `A` of characteristic `p`. Then every `b ∈ B` has
`b^{pⁿ} ∈ A` for some `n` (`EnvelopeProperty.Algebra.IsRadicialIntegral.exists_pow_pow_mem`), i.e.
`A → B` is `p`-radical in Mathlib's sense
(`EnvelopeProperty.Algebra.IsRadicialIntegral.isPRadical`). This is the direction (1) ⇒ (2) of
Stacks 0CNF (Lemma 29.47.9) in the case `p = 0` in `A`.

## Proof (Stacks 0CNF, simplified in characteristic `p`)

The set `B' = {b : b^{pⁿ} ∈ A for some n}` is an `A`-subalgebra of `B`, because Frobenius is
additive in characteristic `p` (this replaces Stacks 0545; the condition `pⁿ b ∈ A` of Stacks is
automatic since `p = 0`). If `B' ≠ B`, the extension `B' ⊆ B` is again radicial integral
(`EnvelopeProperty.Algebra.IsRadicialIntegral.over_subalgebra`; in Stacks this is the implicit
universal-homeomorphism step) and the structure lemma 0CNC
(`EnvelopeProperty.Algebra.IsRadicialIntegral.exists_sq_cube_or_prime`) gives `b ∉ B'` with
`b², b³ ∈ B'` or `ℓ b, b^ℓ ∈ B'` for a prime `ℓ`. In the first case and for `ℓ = p`, `b^p ∈ B'`,
so `b ∈ B'`. For `ℓ ≠ p`, `ℓ` is a unit of `A`, so `b ∈ B'`. Both contradict `b ∉ B'`.

`EnvelopeProperty.exists_pow_pow_mem_of_maxSpec_injective` is the model form
`thm:gl-frobenius-descent` with the hypotheses of `lem:gl-radicial`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Frobenius descent** (Stacks 0CNF, (1) ⇒ (2), characteristic `p`). If `A` has
characteristic `p` and `A ⊆ B` is radicial integral, then every `b ∈ B` has a `p`-power power
`b^{pⁿ}` in `A`. -/
theorem Algebra.IsRadicialIntegral.exists_pow_pow_mem (p : ℕ) [hp : Fact p.Prime] [CharP A p]
    (h : Algebra.IsRadicialIntegral A B) (b : B) :
    ∃ n : ℕ, b ^ p ^ n ∈ (algebraMap A B).range := by
  have : CharP B p := charP_of_injective_algebraMap h.injective p
  have hmono : ∀ {x : B} {n : ℕ} (k : ℕ), x ^ p ^ n ∈ (algebraMap A B).range →
      x ^ p ^ (n + k) ∈ (algebraMap A B).range := by
    intro x n k hx
    rw [pow_add, pow_mul]
    exact pow_mem hx _
  let B' : Subalgebra A B :=
    { carrier := {x | ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap A B).range}
      mul_mem' := fun {x y} ⟨n, hx⟩ ⟨m, hy⟩ => ⟨n + m, by
        rw [mul_pow]
        exact mul_mem (hmono m hx) (add_comm m n ▸ hmono n hy)⟩
      add_mem' := fun {x y} ⟨n, hx⟩ ⟨m, hy⟩ => ⟨n + m, by
        rw [add_pow_char_pow]
        exact add_mem (hmono m hx) (add_comm m n ▸ hmono n hy)⟩
      algebraMap_mem' := fun a => ⟨0, by
        rw [pow_zero, pow_one]
        exact RingHom.mem_range_self _ _⟩ }
  have hmem : ∀ x : B, x ∈ B' ↔ ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap A B).range := fun x => Iff.rfl
  suffices hB' : B' = ⊤ from (hmem b).1 (hB' ▸ Algebra.mem_top)
  by_contra hne
  have hns : ¬ Function.Surjective (algebraMap B' B) := fun hs =>
    hne (eq_top_iff.2 fun x _ => by
      obtain ⟨y, rfl⟩ := hs x
      exact y.2)
  obtain ⟨c, hc, hcases⟩ := (h.over_subalgebra B').exists_sq_cube_or_prime hns
  simp only [mem_range_algebraMap_subalgebra_iff] at hc hcases
  have hpow : c ^ p ∉ B' := fun hcp => by
    obtain ⟨n, hn⟩ := (hmem _).1 hcp
    refine hc ((hmem c).2 ⟨n + 1, ?_⟩)
    rw [pow_succ', pow_mul]
    exact hn
  rcases hcases with ⟨h2, h3⟩ | ⟨ℓ, hℓ, h1, hℓpow⟩
  · exact hpow (pow_mem_of_sq_mem_of_cube_mem h2 h3 hp.out.two_le)
  · by_cases hℓp : ℓ = p
    · subst hℓp
      exact hpow hℓpow
    · have hu : IsUnit (ℓ : A) := (CharP.isUnit_natCast_iff hp.out).2 fun hdvd =>
        hℓp ((Nat.prime_dvd_prime_iff_eq hp.out hℓ).1 hdvd).symm
      obtain ⟨u, hu'⟩ := hu.exists_left_inv
      apply hc
      have hc' : c = algebraMap A B u * ((ℓ : B) * c) := by
        rw [← mul_assoc, ← map_natCast (algebraMap A B), ← map_mul, hu', map_one, one_mul]
      rw [hc']
      exact B'.mul_mem (B'.algebraMap_mem u) h1

/-- **Frobenius descent, `IsPRadical` form.** If `A` has characteristic `p` and `A ⊆ B` is
radicial integral, then `A → B` is `p`-radical (Mathlib's `IsPRadical`); its kernel condition is
trivial since `A → B` is injective. -/
theorem Algebra.IsRadicialIntegral.isPRadical (p : ℕ) [Fact p.Prime] [CharP A p]
    (h : Algebra.IsRadicialIntegral A B) : IsPRadical (algebraMap A B) p where
  pow_mem' x := by
    obtain ⟨n, a, ha⟩ := h.exists_pow_pow_mem p x
    exact ⟨n, a, ha⟩
  ker_le' := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 h.injective]
    exact bot_le

/-- **Frobenius descent, model form** (`thm:gl-frobenius-descent`). Let `k` be an algebraically
closed field of characteristic `p > 0` and `A ⊆ B` algebras over `k` with `A` of finite type
and `B` finite over `A`. If `MaxSpec B → MaxSpec A` is injective (the hypothesis of
`lem:gl-radicial`), then every `b ∈ B` has `b^{pⁿ} ∈ A` for some `n`. -/
theorem exists_pow_pow_mem_of_maxSpec_injective {k : Type*} [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [Algebra k A] [Algebra k B] [IsScalarTower k A B]
    [Algebra.FiniteType k A] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') (b : B) :
    ∃ n : ℕ, b ^ p ^ n ∈ (algebraMap A B).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton B := (algebraMap A B).codomain_trivial
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  exact (Algebra.IsRadicialIntegral.of_maxSpec_injective (k := k) hinj hmax).exists_pow_pow_mem p b

end EnvelopeProperty
