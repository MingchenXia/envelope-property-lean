/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.NormalDVR
import Hironaka.Algebra.Local.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Principal-associated localizations in actual regular domains

Prime avoidance and actual regular-parameter quotients give the DVR
property directly, without assuming normality or unique factorization.
-/

noncomputable section

namespace EnvelopeProperty

open IsLocalRing Ideal IsDiscreteValuationRing
open scoped Classical

universe u

/-- An actual principal associated maximal ideal of a regular local domain forces
the actual ring to be a DVR. No normality or dimension premise is assumed. -/
theorem isDiscreteValuationRing_of_regular_local_principal_associated
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {g b : R} (hg : g ≠ 0) (hb : b ∉ span {g})
    (hmb : ∀ x ∈ IsLocalRing.maximalIdeal R, x * b ∈ span {g}) : IsDiscreteValuationRing R := by
  classical
  have hdimle : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 := by
    by_contra hlarge
    have hdim : 1 < ringKrullDim R := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
      exact_mod_cast Nat.lt_of_not_ge hlarge
    have hfin : ((span {g} : Ideal R).minimalPrimes).Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing R _
    let S : Finset (Ideal R) := insert (IsLocalRing.maximalIdeal R ^ 2) hfin.toFinset
    have hprime : ∀ P ∈ S, P ≠ IsLocalRing.maximalIdeal R ^ 2 → P ≠ IsLocalRing.maximalIdeal R ^ 2 → P.IsPrime := by
      intro P hP hne _
      rcases Finset.mem_insert.mp hP with hP | hP
      · exact (hne hP).elim
      · exact (hfin.mem_toFinset.mp hP).1.1
    have havoid : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ P ∈ (S : Set (Ideal R)), (P : Set R)) := by
      rw [Ideal.subset_union_prime (IsLocalRing.maximalIdeal R ^ 2) (IsLocalRing.maximalIdeal R ^ 2) hprime]
      rintro ⟨P, hP, hle⟩
      rcases Finset.mem_insert.mp hP with rfl | hP
      · have hnonzero : ringKrullDim R ≠ 0 := ne_of_gt (lt_trans zero_lt_one hdim)
        exact lt_irrefl _
          ((IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hnonzero).trans_le hle)
      · have hmin : P ∈ (span {g} : Ideal R).minimalPrimes := hfin.mem_toFinset.mp hP
        have hp : P.IsPrime := hmin.1.1
        have heq : P = IsLocalRing.maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
        have hheight : P.height ≤ 1 := by
          simpa only [Set.ncard_singleton, Nat.cast_one] using
            Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_singleton g) hmin
        have hdimle' : ringKrullDim R ≤ 1 := by
          rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← heq]
          exact_mod_cast hheight
        exact (not_le_of_gt hdim) hdimle'
    obtain ⟨x, hx, hnot⟩ := Set.not_subset.mp havoid
    have hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
      intro hx2
      exact hnot (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hx2)
    have hxavoid (P : Ideal R) (hP : P ∈ (span {g} : Ideal R).minimalPrimes) : x ∉ P := by
      intro hxP
      exact hnot (Set.mem_biUnion
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hP))) hxP)
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hx2 (hx0 ▸ Ideal.zero_mem _)
    let := (IsRegularLocalRing.quotient_span_singleton hx hx2).1
    have hxp : (span {x} : Ideal R).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    have hgnot : g ∉ (span {x} : Ideal R) := by
      intro hgx
      have hspanrank : (span {x} : Ideal R).spanFinrank ≤ 1 := by
        simpa only [Set.ncard_singleton] using
          (Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton x))
      have hheight : (span {x} : Ideal R).height ≤ 1 :=
        (Ideal.height_le_spanFinrank _ hxp.ne_top).trans (by exact_mod_cast hspanrank)
      have hmin : (span {x} : Ideal R) ∈ (span {g} : Ideal R).minimalPrimes :=
        Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hgx)
          (hheight.trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero hg)))
      exact hxavoid _ hmin (Ideal.mem_span_singleton_self x)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hmb x hx)
    have hcmem : c ∈ (span {x} : Ideal R) :=
      (hxp.mem_or_mem (Ideal.mem_span_singleton.mpr ⟨b, hc.symm⟩)).resolve_left hgnot
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hcmem
    apply hb
    apply Ideal.mem_span_singleton.mpr
    refine ⟨d, ?_⟩
    apply mul_left_cancel₀ hx0
    calc
      x * b = g * c := hc
      _ = x * (g * d) := by rw [hd]; ring
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := by
    obtain ⟨s, hcard, hspan⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    by_cases hs : s = ∅
    · refine ⟨⟨0, ?_⟩⟩
      rw [← hspan, hs]
      simp
    · have hcardone : s.card = 1 := by
        have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        omega
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcardone
      exact ⟨⟨x, by simpa only [Finset.coe_singleton] using hspan.symm⟩⟩
  have hnotfield : ¬ IsField R := by
    intro hF
    let _ := hF.toField
    exact hb (by rw [Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr hg)]; trivial)
  exact ((IsDiscreteValuationRing.TFAE R hnotfield).out 0 4).mpr hprincipal

section RegularDomain

variable {E : Type*} [CommRing E] [IsDomain E] [IsRegularRing E]

/-- Associated primes of an actual principal quotient in a regular domain have
actual DVR localizations, with no normality premise. -/
theorem isDiscreteValuationRing_localization_of_isAssociatedPrime_of_isRegularRing
    {g : E} (hg : g ≠ 0) {P : Ideal E} [P.IsPrime]
    (hP : IsAssociatedPrime P (E ⧸ span {g})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨b, hb⟩ := exists_mem_iff_mul_mem_of_isAssociatedPrime hP
  let R := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap E R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have hspan : span {algebraMap E R g} = (span {g}).map (algebraMap E R) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine isDiscreteValuationRing_of_regular_local_principal_associated
    (g := algebraMap E R g) (b := algebraMap E R b)
    ((map_ne_zero_iff _ hinj).mpr hg) ?_ ?_
  · rw [hspan, ← IsLocalization.mk'_one (M := P.primeCompl),
      IsLocalization.mk'_mem_map_algebraMap_iff]
    rintro ⟨t, ht, htb⟩
    exact ht ((hb t).mpr htb)
  · intro m hm
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl m
    have hr : r ∈ P := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff (S := R) (I := P)] at hm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hb r).mp hr)
    have hdiv : ∃ z : R, z * algebraMap E R g =
        algebraMap E R b * IsLocalization.mk' R r t := by
      refine ⟨IsLocalization.mk' R c t, ?_⟩
      rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
        IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm g, hc, mul_comm]
    obtain ⟨z, hz⟩ := hdiv
    exact Ideal.mem_span_singleton'.mpr ⟨z, hz.trans (mul_comm _ _)⟩

theorem mem_minimalPrimes_of_isAssociatedPrime_of_isRegularRing {h : E} (hh : h ≠ 0) {P : Ideal E}
    (hP : IsAssociatedPrime P (E ⧸ Ideal.span {h})) : P ∈ (Ideal.span {h}).minimalPrimes := by
  have := hP.isPrime
  have := isDiscreteValuationRing_localization_of_isAssociatedPrime_of_isRegularRing hh hP
  let R := Localization.AtPrime P
  have hle : Ideal.span {h} ≤ P := by
    have := hP.annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at this
  refine ⟨⟨hP.isPrime, hle⟩, fun Q ⟨hQ, hhQ⟩ hQP => ?_⟩
  -- A prime `hE ⊆ Q ⊆ P` gives a nonzero prime of the discrete valuation ring `E_P`.
  have hdisj : Disjoint (P.primeCompl : Set E) Q := by
    rw [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset]
    exact hQP
  have hQR : (Q.map (algebraMap E R)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl R Q hQ hdisj
  have hinj : Function.Injective (algebraMap E R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have hQ0 : Q.map (algebraMap E R) ≠ ⊥ := by
    intro h0
    have : algebraMap E R h ∈ Q.map (algebraMap E R) :=
      Ideal.mem_map_of_mem _ (hhQ (Ideal.mem_span_singleton_self h))
    rw [h0, Ideal.mem_bot, map_eq_zero_iff _ hinj] at this
    exact hh this
  have hmax : Q.map (algebraMap E R) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (hQR.isMaximal hQ0)
  have := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl R hQ hdisj
  rw [hmax, IsLocalization.AtPrime.under_maximalIdeal R P] at this
  exact this.le

/-- The associated primes of `E ⧸ hE` are exactly the minimal primes of `hE` (`E` an actual regular domain, `h ≠ 0`). They form a finite set
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`). -/
theorem associatedPrimes_eq_minimalPrimes_of_isRegularRing {h : E} (hh : h ≠ 0) :
    associatedPrimes E (E ⧸ Ideal.span {h}) = (Ideal.span {h}).minimalPrimes := by
  refine subset_antisymm (fun P hP => mem_minimalPrimes_of_isAssociatedPrime_of_isRegularRing hh hP) ?_
  have := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes E
    (E ⧸ Ideal.span {h})
  rwa [Ideal.annihilator_quotient] at this

/-- **`lem:bj-dvr-minimal`, DVR part.** If `P` is a minimal prime of `hE`, where `E` is a
regular domain and `h ≠ 0`, then `E_P` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localization_of_mem_minimalPrimes_of_isRegularRing {h : E} (hh : h ≠ 0)
    {P : Ideal E} [P.IsPrime] (hP : P ∈ (Ideal.span {h}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  rw [← associatedPrimes_eq_minimalPrimes_of_isRegularRing hh] at hP
  exact isDiscreteValuationRing_localization_of_isAssociatedPrime_of_isRegularRing hh hP

/-- **`lem:bj-dvr-minimal`, divisibility criterion.** For `E` an actual regular domain and `h ≠ 0`: `f ∈ hE` if and only if for every minimal prime `P` of `hE` there is
`s ∉ P` with `s f ∈ hE`. -/
theorem mem_span_singleton_iff_forall_minimalPrimes_of_isRegularRing {h : E} (hh : h ≠ 0) (f : E) :
    f ∈ Ideal.span {h} ↔
      ∀ P ∈ (Ideal.span {h}).minimalPrimes, ∃ s ∉ P, s * f ∈ Ideal.span {h} := by
  refine ⟨fun hf P hP => ⟨1, hP.1.1.ne_top ∘ (Ideal.eq_top_iff_one P).mpr, by simpa using hf⟩,
    fun H => ?_⟩
  by_contra hf
  have hx : (Ideal.Quotient.mk (Ideal.span {h}) f) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing E _ hx
  obtain ⟨s, hs, hsf⟩ := H P (mem_minimalPrimes_of_isAssociatedPrime_of_isRegularRing hh hP)
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact hsf

/-- **`lem:bj-dvr-minimal`, divisibility criterion in the local rings.** For `E` an actual regular domain and `h ≠ 0`: `f ∈ hE` if and only if `h ∣ f` in the discrete valuation
ring `E_P` for every minimal prime `P` of `hE`. -/
theorem mem_span_singleton_iff_forall_minimalPrimes_dvd_of_isRegularRing {h : E} (hh : h ≠ 0) (f : E) :
    f ∈ Ideal.span {h} ↔
      ∀ (P : Ideal E) [P.IsPrime], P ∈ (Ideal.span {h}).minimalPrimes →
        algebraMap E (Localization.AtPrime P) h ∣ algebraMap E (Localization.AtPrime P) f := by
  rw [mem_span_singleton_iff_forall_minimalPrimes_of_isRegularRing hh]
  refine ⟨fun H P _ hP => (algebraMap_dvd_algebraMap_atPrime_iff P h f).mpr (H P hP), fun H P hP => ?_⟩
  have := hP.1.1
  exact (algebraMap_dvd_algebraMap_atPrime_iff P h f).mp (H P hP)


end RegularDomain

end EnvelopeProperty
