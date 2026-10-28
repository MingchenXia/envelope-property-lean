/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Algebra.RadicialStructure

/-!
# Subintegral towers (Stacks 0CND, characteristic `0`)

This file defines the tower form of subintegrality and proves that a radicial integral
extension of `ℚ`-algebras is subintegral in this sense (Stacks 0CND, (1) ⇒ (2)). It supplies the
hypothesis of the imported additive-powers theorem (`thm:gl-additive-powers`, FHX Lemma 8.2,
Roberts–Singh Theorem 4.17) in the proof of FHX Theorem 8.3 in characteristic `0`
(`thm:normalization-reflection`, "`A_α ⊆ B_α` is subintegral [Stacks, Tag 0CND]"); decision
D-H3′.

## Definitions

* `EnvelopeProperty.IsSubintegralChain A l`: the list `l = [b₁, …, bₙ]` of elements of `B`
  satisfies `bᵢ², bᵢ³ ∈ A[b₁, …, b_{i-1}]` for all `i`, i.e. `A ⊆ A[b₁] ⊆ … ⊆ A[b₁, …, bₙ]` is a
  finite succession of elementary subintegral extensions `Aᵢ ⊆ Aᵢ[eᵢ]`, `eᵢ², eᵢ³ ∈ Aᵢ`
  (Roberts–Singh, p. 257).
* `EnvelopeProperty.Algebra.IsSubintegralTower A B`: every finite subset of `B` lies in
  `A[b₁, …, bₙ]` for a subintegral chain `[b₁, …, bₙ]` (Stacks 0CND (2)). Equivalently
  (`EnvelopeProperty.Algebra.isSubintegralTower_iff_forall_mem`) `B` is the union of the
  subrings obtained from `A` by finite successions of elementary subintegral extensions, which is
  Roberts–Singh's definition of a subintegral extension (p. 258, after Swan).

## Main results

* `EnvelopeProperty.Algebra.IsRadicialIntegral.exists_sq_cube_of_algebraRat` (Stacks 0CNB over
  `ℚ`): if `A` is a `ℚ`-algebra and `A ⊊ B` is radicial integral, some `b ∈ B ∖ A` has
  `b², b³ ∈ A`.
* `EnvelopeProperty.Algebra.IsRadicialIntegral.isSubintegralTower` (Stacks 0CND, (1) ⇒ (2)): if
  `A` is a `ℚ`-algebra and `A ⊆ B` is radicial integral
  (`EnvelopeProperty.Algebra.IsRadicialIntegral`; over `ℚ` the residue field extensions are then
  isomorphisms), then `A ⊆ B` is a subintegral tower.
* `EnvelopeProperty.isSubintegralTower_of_maxSpec_injective`: the model form with the hypotheses of
  `lem:gl-radicial` (lane G12a) over an algebraically closed field of characteristic `0`.

## Proof and deviations from Stacks

Stacks proves 0CNB separately (with the same argument as 0CNC, using residue field
isomorphisms). Over `ℚ` we deduce it from 0CNC
(`EnvelopeProperty.Algebra.IsRadicialIntegral.exists_sq_cube_or_prime`): the second alternative
`ℓ b, b^ℓ ∈ A` gives `b ∈ A`, since the prime `ℓ` is a unit of `A`.

For 0CND, Stacks builds an ordinal-indexed chain of subalgebras by transfinite recursion. We avoid
ordinals: the union `B'` of all subalgebras `A[b₁, …, bₙ]` given by subintegral chains is an
`A`-subalgebra (two chains concatenate to a chain, `EnvelopeProperty.IsSubintegralChain.append`).
If `B' ≠ B`, then `B' ⊆ B` is radicial integral
(`EnvelopeProperty.Algebra.IsRadicialIntegral.over_subalgebra`) and `B'` is a `ℚ`-algebra, so
0CNB gives `b ∉ B'` with `b², b³ ∈ B'`; appending `b` to the concatenation of chains containing
`b²` and `b³` shows `b ∈ B'`, a contradiction. Hence `B' = B`, and finitely many elements lie in
one tower by concatenation.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A list `[b₁, …, bₙ]` of elements of `B` is a *subintegral chain* over `A` if
`bᵢ², bᵢ³ ∈ A[b₁, …, b_{i-1}]` for every `i` (Stacks 0CND (2); Roberts–Singh's finite succession
of elementary subintegral extensions). The list is built by appending its last element. -/
inductive IsSubintegralChain : List B → Prop
  /-- The empty chain (`A₀ = A`). -/
  | nil : IsSubintegralChain []
  /-- Appending `e` with `e², e³ ∈ A[l]` (`A_{n+1} = A_n[e]`). -/
  | concat {l : List B} {e : B} : IsSubintegralChain l →
      e ^ 2 ∈ Algebra.adjoin A {x | x ∈ l} → e ^ 3 ∈ Algebra.adjoin A {x | x ∈ l} →
      IsSubintegralChain (l ++ [e])

/-- **Subintegral towers** (tower form of subintegrality; Stacks 0CND (2), Roberts–Singh §4).
Every finite subset of `B` is contained in `A[b₁, …, bₙ]` for a subintegral chain
`[b₁, …, bₙ]`, i.e. `bᵢ², bᵢ³ ∈ A[b₁, …, b_{i-1}]`. -/
def Algebra.IsSubintegralTower (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ E : Finset B, ∃ l : List B, IsSubintegralChain A l ∧
    (E : Set B) ⊆ Algebra.adjoin A {x | x ∈ l}

variable {A}

/-- `A[l₁] ⊆ A[l₁ ++ l₂]`. -/
theorem adjoin_le_adjoin_append_left (l₁ l₂ : List B) :
    Algebra.adjoin A {x | x ∈ l₁} ≤ Algebra.adjoin A {x | x ∈ l₁ ++ l₂} :=
  Algebra.adjoin_mono fun _ hx => List.mem_append_left _ hx

/-- `A[l₂] ⊆ A[l₁ ++ l₂]`. -/
theorem adjoin_le_adjoin_append_right (l₁ l₂ : List B) :
    Algebra.adjoin A {x | x ∈ l₂} ≤ Algebra.adjoin A {x | x ∈ l₁ ++ l₂} :=
  Algebra.adjoin_mono fun _ hx => List.mem_append_right _ hx

/-- Two subintegral chains concatenate to a subintegral chain. -/
theorem IsSubintegralChain.append {l₁ l₂ : List B} (h₁ : IsSubintegralChain A l₁)
    (h₂ : IsSubintegralChain A l₂) : IsSubintegralChain A (l₁ ++ l₂) := by
  induction h₂ with
  | nil => simpa using h₁
  | @concat l e _ he2 he3 ih =>
    rw [← List.append_assoc]
    exact ih.concat (adjoin_le_adjoin_append_right l₁ l he2)
      (adjoin_le_adjoin_append_right l₁ l he3)

/-- The union form of `EnvelopeProperty.Algebra.IsSubintegralTower` (Roberts–Singh's
definition): every element of `B` lies in `A[b₁, …, bₙ]` for some subintegral chain. -/
theorem Algebra.isSubintegralTower_iff_forall_mem :
    Algebra.IsSubintegralTower A B ↔
      ∀ b : B, ∃ l : List B, IsSubintegralChain A l ∧ b ∈ Algebra.adjoin A {x | x ∈ l} := by
  classical
  refine ⟨fun h b => ?_, fun h E => ?_⟩
  · obtain ⟨l, hl, hE⟩ := h {b}
    exact ⟨l, hl, hE (by simp)⟩
  · induction E using Finset.induction_on with
    | empty => exact ⟨[], .nil, by simp⟩
    | insert e E _ ih =>
      obtain ⟨l₁, h₁, hE⟩ := ih
      obtain ⟨l₂, h₂, he⟩ := h e
      refine ⟨l₁ ++ l₂, h₁.append h₂, ?_⟩
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨adjoin_le_adjoin_append_right l₁ l₂ he,
        hE.trans (adjoin_le_adjoin_append_left l₁ l₂)⟩

/-- **Stacks 0CNB over `ℚ`.** If `A` is a `ℚ`-algebra and `A ⊊ B` is radicial integral, there is
`b ∈ B ∖ A` with `b², b³ ∈ A`. The second alternative of 0CNC
(`EnvelopeProperty.Algebra.IsRadicialIntegral.exists_sq_cube_or_prime`) cannot occur: `ℓ b ∈ A`
implies `b ∈ A` since the prime `ℓ` is a unit of `A`. -/
theorem Algebra.IsRadicialIntegral.exists_sq_cube_of_algebraRat [Algebra ℚ A]
    (h : Algebra.IsRadicialIntegral A B) (hne : ¬ Function.Surjective (algebraMap A B)) :
    ∃ b : B, b ∉ (algebraMap A B).range ∧ b ^ 2 ∈ (algebraMap A B).range ∧
      b ^ 3 ∈ (algebraMap A B).range := by
  obtain ⟨c, hc, hcases⟩ := h.exists_sq_cube_or_prime hne
  rcases hcases with h23 | ⟨ℓ, hℓ, ⟨a, ha⟩, -⟩
  · exact ⟨c, hc, h23⟩
  · exfalso
    have hu : IsUnit (ℓ : A) := by
      rw [← map_natCast (algebraMap ℚ A)]
      exact (Ne.isUnit (Nat.cast_ne_zero.2 hℓ.ne_zero)).map _
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine hc ⟨u * a, ?_⟩
    rw [map_mul, ha, ← mul_assoc, ← map_natCast (algebraMap A B), ← map_mul, hu', map_one,
      one_mul]

/-- **Stacks 0CND, (1) ⇒ (2), over `ℚ`.** If `A` is a `ℚ`-algebra and `A ⊆ B` is radicial
integral, then `A ⊆ B` is a subintegral tower: every finite subset of `B` lies in
`A[b₁, …, bₙ] ⊆ B` with `bᵢ², bᵢ³ ∈ A[b₁, …, b_{i-1}]`. -/
theorem Algebra.IsRadicialIntegral.isSubintegralTower [Algebra ℚ A]
    (h : Algebra.IsRadicialIntegral A B) : Algebra.IsSubintegralTower A B := by
  let B' : Subalgebra A B :=
    { carrier := {b | ∃ l : List B, IsSubintegralChain A l ∧ b ∈ Algebra.adjoin A {x | x ∈ l}}
      mul_mem' := fun {x y} ⟨l₁, h₁, hx⟩ ⟨l₂, h₂, hy⟩ => ⟨l₁ ++ l₂, h₁.append h₂,
        mul_mem (adjoin_le_adjoin_append_left l₁ l₂ hx) (adjoin_le_adjoin_append_right l₁ l₂ hy)⟩
      add_mem' := fun {x y} ⟨l₁, h₁, hx⟩ ⟨l₂, h₂, hy⟩ => ⟨l₁ ++ l₂, h₁.append h₂,
        add_mem (adjoin_le_adjoin_append_left l₁ l₂ hx) (adjoin_le_adjoin_append_right l₁ l₂ hy)⟩
      algebraMap_mem' := fun a => ⟨[], .nil, Subalgebra.algebraMap_mem _ a⟩ }
  have hmem : ∀ x : B, x ∈ B' ↔
      ∃ l : List B, IsSubintegralChain A l ∧ x ∈ Algebra.adjoin A {x | x ∈ l} := fun x => Iff.rfl
  suffices hB' : B' = ⊤ from
    Algebra.isSubintegralTower_iff_forall_mem.2 fun b => (hmem b).1 (hB' ▸ Algebra.mem_top)
  by_contra hne
  have hns : ¬ Function.Surjective (algebraMap B' B) := fun hs =>
    hne (eq_top_iff.2 fun x _ => by
      obtain ⟨y, rfl⟩ := hs x
      exact y.2)
  let : Algebra ℚ B' := ((algebraMap A B').comp (algebraMap ℚ A)).toAlgebra
  obtain ⟨c, hc, h2, h3⟩ := (h.over_subalgebra B').exists_sq_cube_of_algebraRat hns
  simp only [mem_range_algebraMap_subalgebra_iff] at hc h2 h3
  obtain ⟨l₁, h₁, hc2⟩ := (hmem _).1 h2
  obtain ⟨l₂, h₂, hc3⟩ := (hmem _).1 h3
  refine hc ((hmem c).2 ⟨l₁ ++ l₂ ++ [c], (h₁.append h₂).concat
    (adjoin_le_adjoin_append_left l₁ l₂ hc2) (adjoin_le_adjoin_append_right l₁ l₂ hc3), ?_⟩)
  exact Algebra.subset_adjoin (List.mem_append_right _ (List.mem_singleton_self c))

/-- **Subintegrality, model form** (characteristic `0` case of FHX Theorem 8.3, "`A_α ⊆ B_α` is
subintegral [Stacks, Tag 0CND]"). Let `k` be an algebraically closed field of characteristic `0`
and `A ⊆ B` algebras over `k` with `A` of finite type and `B` finite over `A`. If
`MaxSpec B → MaxSpec A` is injective (the hypothesis of `lem:gl-radicial`), then `A ⊆ B` is a
subintegral tower. -/
theorem isSubintegralTower_of_maxSpec_injective {k : Type*} [Field k] [IsAlgClosed k]
    [CharZero k] [Algebra k A] [Algebra k B] [IsScalarTower k A B] [Algebra.FiniteType k A]
    [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    Algebra.IsSubintegralTower A B :=
  letI : Algebra ℚ A := ((algebraMap k A).comp (algebraMap ℚ k)).toAlgebra
  (Algebra.IsRadicialIntegral.of_maxSpec_injective (k := k) hinj hmax).isSubintegralTower

end EnvelopeProperty
