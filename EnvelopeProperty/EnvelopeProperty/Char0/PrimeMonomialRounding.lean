/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# Intrinsic rounding of actual finite prime monomials

Only uniqueness for finite products of known primes is used. No unique-factorization
instance, factorization of arbitrary elements, or supplied matching of the two families occurs.
-/
noncomputable section
namespace EnvelopeProperty.Char0.PrimeMonomialRounding
open scoped Classical

private def factors {A ι : Type*} [Fintype ι] (p : ι → A) (a : ι → ℕ) : Multiset A :=
  ∑ i, Multiset.replicate (a i) (p i)

private theorem factors_prod {A ι : Type*} [CommMonoid A] [Fintype ι]
    (p : ι → A) (a : ι → ℕ) : (factors p a).prod = ∏ i, p i ^ a i := by
  simp only [factors, Multiset.prod_sum, Multiset.prod_replicate]

private theorem factors_map {A B ι : Type*} [Fintype ι]
    (p : ι → A) (a : ι → ℕ) (g : A → B) :
    (factors p a).map g = factors (g ∘ p) a := by
  unfold factors
  have hmap (s : Finset ι) : (∑ i ∈ s, Multiset.replicate (a i) (p i)).map g =
      ∑ i ∈ s, Multiset.replicate (a i) (g (p i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi, Multiset.map_add, Multiset.map_replicate, ih]
  exact hmap Finset.univ

private theorem count_factors {A ι : Type*} [Fintype ι] [DecidableEq A]
    (p : ι → A) (hp : Function.Injective p) (a : ι → ℕ) (i : ι) :
    (factors p a).count (p i) = a i := by
  classical
  change (Multiset.countAddMonoidHom (p i)) (∑ j, Multiset.replicate (a j) (p j)) = _
  rw [map_sum]
  change (∑ j, Multiset.count (p i) (Multiset.replicate (a j) (p j))) = _
  simp only [Multiset.count_replicate, hp.eq_iff]
  simp

private def roundedClassProduct {A : Type*} [CommMonoid A] [DecidableEq A]
    (s : Multiset A) (q : ℚ) : A :=
  ∏ x ∈ s.toFinset, x ^ ⌊q * (s.count x : ℚ)⌋₊

private theorem roundedClassProduct_factors {A ι : Type*} [CommMonoid A] [DecidableEq A]
    [Fintype ι] (p : ι → A) (hp : Function.Injective p) (a : ι → ℕ) (q : ℚ) :
    roundedClassProduct (factors p a) q = ∏ i, p i ^ ⌊q * (a i : ℚ)⌋₊ := by
  classical
  have hs : (factors p a).toFinset ⊆ Finset.univ.image p := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp (Multiset.mem_toFinset.mp hx)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Multiset.mem_replicate.mp hi).2.symm⟩
  calc roundedClassProduct (factors p a) q =
      ∏ x ∈ Finset.univ.image p, x ^ ⌊q * ((factors p a).count x : ℚ)⌋₊ := by
        apply Finset.prod_subset hs
        intro x _ hx
        rw [Multiset.count_eq_zero_of_notMem (fun h => hx (Multiset.mem_toFinset.mpr h))]
        simp
    _ = ∏ i, p i ^ ⌊q * ((factors p a).count (p i) : ℚ)⌋₊ :=
      Finset.prod_image (fun i _ j _ hij => hp hij)
    _ = ∏ i, p i ^ ⌊q * (a i : ℚ)⌋₊ := by simp only [count_factors p hp]

private theorem factors_prime {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] (p : ι → R) (hp : ∀ i, Prime (p i))
    (a : ι → ℕ) : ∀ x ∈ factors p a, Prime x := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp hx
  exact (Multiset.mem_replicate.mp hi).2 ▸ hp i

/-- Association of original prime monomials forces association after rounding EVERY exponent.
The two families need only be pairwise nonassociated internally. -/
theorem associated_rounded_products {R ι κ : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [Fintype κ] (p : ι → R) (r : κ → R)
    (hp : ∀ i, Prime (p i)) (hr : ∀ j, Prime (r j))
    (hpi : Function.Injective (fun i => Associates.mk (p i)))
    (hri : Function.Injective (fun j => Associates.mk (r j)))
    (a : ι → ℕ) (b : κ → ℕ)
    (h : Associated (∏ i, p i ^ a i) (∏ j, r j ^ b j)) (q : ℚ) :
    Associated (∏ i, p i ^ ⌊q * (a i : ℚ)⌋₊) (∏ j, r j ^ ⌊q * (b j : ℚ)⌋₊) := by
  classical
  have hfac := prime_factors_unique (f := factors p a) (g := factors r b)
    (factors_prime p hp a) (factors_prime r hr b)
    (by simpa only [factors_prod] using h)
  have heq := Associates.rel_associated_iff_map_eq_map.mp hfac
  rw [factors_map, factors_map] at heq
  have he := congrArg (fun s : Multiset (Associates R) => roundedClassProduct s q) heq
  change roundedClassProduct (factors (fun i => Associates.mk (p i)) a) q =
    roundedClassProduct (factors (fun j => Associates.mk (r j)) b) q at he
  rw [roundedClassProduct_factors _ hpi, roundedClassProduct_factors _ hri] at he
  apply Associates.mk_eq_mk_iff_associated.mp
  change Associates.mkMonoidHom _ = Associates.mkMonoidHom _
  simpa only [map_prod, map_pow, Associates.mkMonoidHom_apply] using he

end EnvelopeProperty.Char0.PrimeMonomialRounding
