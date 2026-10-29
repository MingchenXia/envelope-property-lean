/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Divisors of boundary monomials

A divisor of a product of prime elements is associated to a subproduct. This elementary
factorization needs primality of the boundary parameters and cancellation in the domain; it
requires no unique-factorization hypothesis. It is the algebraic core of the relative-Jacobian
monomial step in `hironaka-charts.tex`.
-/

noncomputable section

namespace EnvelopeProperty.Char0

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A divisor of a finite product of prime elements is associated to an indexed subproduct. -/
theorem exists_sublist_associated_prod {ι : Type*} (p : ι → R) :
    ∀ l : List ι, (∀ i ∈ l, Prime (p i)) → ∀ f : R, f ∣ (l.map p).prod →
      ∃ t : List ι, t.Sublist l ∧ Associated f (t.map p).prod := by
  intro l
  induction l with
  | nil =>
    intro _ f hf
    exact ⟨[], List.Sublist.refl _, associated_of_dvd_dvd hf (one_dvd f)⟩
  | cons i l ih =>
    intro hp f hf
    have hpi : Prime (p i) := hp i (List.mem_cons_self)
    have hpl : ∀ j ∈ l, Prime (p j) := fun j hj => hp j (List.mem_cons_of_mem i hj)
    obtain ⟨q, hq⟩ := hf
    have heq : p i * (l.map p).prod = f * q := by
      simpa only [List.map_cons, List.prod_cons] using hq
    have hdiv : p i ∣ f * q := ⟨(l.map p).prod, heq.symm⟩
    rcases hpi.dvd_or_dvd hdiv with hpf | hpq
    · obtain ⟨f', hf'⟩ := hpf
      have hfd : f' ∣ (l.map p).prod := by
        refine ⟨q, ?_⟩
        apply mul_left_cancel₀ hpi.ne_zero
        calc p i * (l.map p).prod = f * q := heq
          _ = p i * (f' * q) := by rw [hf', mul_assoc]
      obtain ⟨t, ht, hta⟩ := ih hpl f' hfd
      refine ⟨i :: t, List.Sublist.cons_cons i ht, ?_⟩
      simpa only [List.map_cons, List.prod_cons, hf'] using Associated.mul_left (p i) hta
    · obtain ⟨q', hq'⟩ := hpq
      have hfd : f ∣ (l.map p).prod := by
        refine ⟨q', ?_⟩
        apply mul_left_cancel₀ hpi.ne_zero
        calc p i * (l.map p).prod = f * q := heq
          _ = f * (p i * q') := by rw [hq']
          _ = p i * (f * q') := mul_left_comm _ _ _
      obtain ⟨t, ht, hta⟩ := ih hpl f hfd
      exact ⟨t, List.Sublist.cons i ht, hta⟩

omit [IsDomain R] in
/-- Collect an indexed list product by multiplicity, including indices absent from the list. -/
theorem list_prod_eq_prod_pow_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → R) (l : List ι) : (l.map p).prod = ∏ i, p i ^ l.count i := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.count_eq_zero_of_not_mem (fun h => hi (List.mem_toFinset.mpr h)), pow_zero]

/-- A divisor of a boundary monomial has bounded nonnegative exponents, up to a unit. -/
theorem exists_exponents_associated_of_dvd_monomial {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → R) (hp : ∀ i, Prime (p i)) (e : ι → ℕ) {f : R}
    (hf : f ∣ ∏ i, p i ^ e i) :
    ∃ a : ι → ℕ, (∀ i, a i ≤ e i) ∧ Associated f (∏ i, p i ^ a i) := by
  let s : Multiset ι := ∑ i, Multiset.replicate (e i) i
  let l : List ι := s.toList
  have hcount (i : ι) : l.count i = e i := by
    change s.toList.count i = e i
    rw [← Multiset.coe_count, Multiset.coe_toList]
    change (Multiset.countAddMonoidHom i) (∑ j, Multiset.replicate (e j) j) = e i
    rw [map_sum]
    change (∑ j, Multiset.count i (Multiset.replicate (e j) j)) = e i
    simp [Multiset.count_replicate]
  have hl : (l.map p).prod = ∏ i, p i ^ e i := by
    rw [list_prod_eq_prod_pow_count]
    simp only [hcount]
  obtain ⟨t, ht, hta⟩ := exists_sublist_associated_prod p l (fun i _ => hp i) f
    (hl.symm ▸ hf)
  refine ⟨fun i => t.count i, fun i => ?_, ?_⟩
  · exact (List.Sublist.count_le i ht).trans_eq (hcount i)
  · simpa only [list_prod_eq_prod_pow_count] using hta

/-- A function invertible off a prime boundary is a boundary monomial, up to a unit. -/
theorem exists_exponents_associated_of_isUnit_away_product {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → R) (hp : ∀ i, Prime (p i))
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away (∏ i, p i) S]
    {f : R} (hf : IsUnit (algebraMap R S f)) :
    ∃ a : ι → ℕ, Associated f (∏ i, p i ^ a i) := by
  obtain ⟨N, hN⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (∏ i, p i)).mp hf
  have hdiv : f ∣ ∏ i, p i ^ N := by simpa only [Finset.prod_pow] using hN
  obtain ⟨a, _, ha⟩ := exists_exponents_associated_of_dvd_monomial p hp (fun _ => N) hdiv
  exact ⟨a, ha⟩

/-- The preceding conclusion in the form used for a local Jacobian generator. -/
theorem exists_unit_mul_monomial_of_isUnit_away_product {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → R) (hp : ∀ i, Prime (p i))
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away (∏ i, p i) S]
    {f : R} (hf : IsUnit (algebraMap R S f)) :
    ∃ (u : Rˣ) (a : ι → ℕ), f = (u : R) * ∏ i, p i ^ a i := by
  obtain ⟨a, ha⟩ := exists_exponents_associated_of_isUnit_away_product p hp S hf
  obtain ⟨u, hu⟩ := ha.symm
  exact ⟨u, a, by rw [← hu, mul_comm]⟩

end EnvelopeProperty.Char0
