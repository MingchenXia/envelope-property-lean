/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.RegularPrincipalDVR

/-!
# Fixed finite prime-localization detection of all boundary monomials

A finite family of original nonzero elements supplies a single finite
prime family which detects every principal monomial with arbitrary
natural exponents. The family does not depend on those exponents.
-/

noncomputable section
namespace EnvelopeProperty
open Ideal
open scoped Classical

variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

/-- The actual fixed boundary prime family, independent of all monomial exponents. -/
def boundaryMinimalPrimes (p : ι → E) : Set (Ideal E) :=
  ⋃ i, (span {p i}).minimalPrimes

/-- The actual boundary prime family is finite over a Noetherian base. -/
theorem finite_boundaryMinimalPrimes [IsNoetherianRing E] (p : ι → E) :
    (boundaryMinimalPrimes p).Finite := by
  exact Set.finite_iUnion fun i => Ideal.finite_minimalPrimes_of_isNoetherianRing E (span {p i})

/-- Every actual minimal prime of every boundary monomial belongs to the same
fixed boundary prime family; the exponents are arbitrary. -/
theorem minimalPrimes_prod_pow_subset_boundaryMinimalPrimes (p : ι → E) (e : ι → ℕ) :
    (span {∏ i, p i ^ e i}).minimalPrimes ⊆ boundaryMinimalPrimes p := by
  intro P hP
  have : P.IsPrime := hP.1.1
  have hgP : (∏ i, p i ^ e i) ∈ P := hP.1.2 (Ideal.mem_span_singleton_self _)
  have hi : ∃ i, e i ≠ 0 ∧ p i ∈ P := by
    by_contra hnone
    have hprod : (∏ i, p i ^ e i) ∈ P.primeCompl := by
      apply Submonoid.prod_mem
      intro i _
      by_cases he : e i = 0
      · rw [he, pow_zero]
        exact P.primeCompl.one_mem
      · apply pow_mem
        change p i ∉ P
        intro hp
        exact hnone ⟨i, he, hp⟩
    exact hprod hgP
  obtain ⟨i, hei, hiP⟩ := hi
  apply Set.mem_iUnion.mpr
  refine ⟨i, ⟨⟨hP.1.1, (Ideal.span_singleton_le_iff_mem _).mpr hiP⟩, ?_⟩⟩
  intro Q ⟨hQ, hiQ⟩ hQP
  apply hP.2 _ hQP
  refine ⟨hQ, (Ideal.span_singleton_le_iff_mem _).mpr ?_⟩
  have hdiv : p i ∣ ∏ j, p j ^ e j :=
    (dvd_pow_self (p i) hei).trans (Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i))
  obtain ⟨a, ha⟩ := hdiv
  rw [ha]
  exact Q.mul_mem_right a (hiQ (Ideal.mem_span_singleton_self _))

/-- The same fixed finite family of actual prime localizations detects every
principal boundary monomial in an actual regular domain. -/
theorem mem_span_prod_pow_iff_boundary_localizations [IsDomain E] [IsRegularRing E]
    (p : ι → E) (hp : ∀ i, p i ≠ 0) (e : ι → ℕ) (f : E) :
    f ∈ span {∏ i, p i ^ e i} ↔
      ∀ (P : Ideal E) [P.IsPrime], P ∈ boundaryMinimalPrimes p →
        algebraMap E (Localization.AtPrime P) (∏ i, p i ^ e i) ∣
          algebraMap E (Localization.AtPrime P) f := by
  have hg : (∏ i, p i ^ e i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i)
  constructor
  · intro hf P _ _
    exact map_dvd (algebraMap E (Localization.AtPrime P)) (Ideal.mem_span_singleton.mp hf)
  · intro H
    apply (mem_span_singleton_iff_forall_minimalPrimes_dvd_of_isRegularRing hg f).mpr
    intro P _ hP
    exact H P (minimalPrimes_prod_pow_subset_boundaryMinimalPrimes p e hP)

end EnvelopeProperty
