import EnvelopeProperty.AffineDimension
import EnvelopeProperty.Algebra.FiniteHeightOnePrimeSeparation
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.Ideal

/-! # Exact dimension and horizontal obstructions for original cut components

The minimal prime is isolated by an internally constructed principal
open. Finite-type localization dimension yields the exact dimension
of every original principal component. No selected family or dimension
comparison certificate occurs.
-/
noncomputable section
open scoped Classical nonZeroDivisors
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionDimension

/-- The whole nonzero proper principal quotient drops dimension by one. -/
theorem principal_quotient_dimension_add_one
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (f : A) (hf : f ≠ 0) (hproper : Ideal.span {f} ≠ ⊤) :
    ringKrullDim (A ⧸ Ideal.span {f}) + 1 = ringKrullDim A := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {f}) hproper
  let : M.IsMaximal := hM
  exact Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf)
    (maximalHeight_eq_ringKrullDim_of_finiteType_domain k A M)
    (hle (Ideal.mem_span_singleton_self f))

/-- An original separator internally isolates a selected minimal prime after localization. -/
theorem exists_away_radical_map_eq {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I P : Ideal A) (hP : P ∈ I.minimalPrimes) :
    ∃ g : A, g ∉ P ∧
      (I.map (algebraMap A (Localization.Away g))).radical =
        P.map (algebraMap A (Localization.Away g)) := by
  let : P.IsPrime := hP.isPrime
  let T := {Q : Ideal A // Q ∈ I.minimalPrimes}
  let : Fintype T := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).fintype
  let p : T := ⟨P, hP⟩
  obtain ⟨g, hgP, hothers⟩ := exists_finite_prime_separator
    (fun q : T => q.1) p (by
      intro q hqp hle
      have heq : q.1 = P := le_antisymm hle (hP.2 ⟨q.2.isPrime, q.2.le⟩ hle)
      exact hqp (Subtype.ext heq))
  refine ⟨g, hgP, ?_⟩
  let B := Localization.Away g
  let φ := algebraMap A B
  let PB := P.map φ
  have hdisj : Disjoint (Submonoid.powers g : Set A) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgP
  have hPBunder : PB.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) B hP.isPrime hdisj
  have hPB : PB ∈ (I.map φ).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map (Submonoid.powers g) B]
    change PB.under A ∈ I.minimalPrimes
    rwa [hPBunder]
  have hsingle : (I.map φ).minimalPrimes = {PB} := by
    ext Q
    constructor
    · intro hQ
      have hQu : Q.under A ∈ I.minimalPrimes := by
        rw [IsLocalization.minimalPrimes_map (Submonoid.powers g) B I] at hQ
        exact hQ
      have hunder : Q.under A = P := by
        by_contra hne
        have hgQ : φ g ∈ Q := hothers ⟨Q.under A, hQu⟩
          (fun he => hne (congrArg Subtype.val he))
        have hone : (1 : B) ∈ Q := by
          simpa only [φ, IsLocalization.Away.mul_invSelf] using
            Q.mul_mem_right (IsLocalization.Away.invSelf g) hgQ
        exact hQ.isPrime.ne_top ((Ideal.eq_top_iff_one Q).mpr hone)
      have heq : Q = PB := by
        rw [← IsLocalization.map_under (Submonoid.powers g) B Q, hunder]
      exact Set.mem_singleton_iff.mpr heq
    · intro he
      exact (Set.mem_singleton_iff.mp he) ▸ hPB
  rw [← Ideal.sInf_minimalPrimes, hsingle, sInf_singleton]

/-- Every minimal component of a nonzero original principal cut has exact dimension. -/
theorem principal_component_dimension_add_one
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (f : A) (hf : f ≠ 0) (P : Ideal A) (hP : P ∈ (Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : P.IsPrime := hP.isPrime
  obtain ⟨g, hgP, hrad⟩ := exists_away_radical_map_eq (Ideal.span {f}) P hP
  have hg : g ≠ 0 := fun he => hgP (he ▸ P.zero_mem)
  let B := Localization.Away g
  let φ := algebraMap A B
  let PB := P.map φ
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers g) B
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))
  have : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k A) (inferInstance : Algebra.FiniteType A B)
  have hinj : Function.Injective φ := IsLocalization.injective B
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))
  have hfB : φ f ≠ 0 := (map_ne_zero_iff φ hinj).mpr hf
  have hdisj : Disjoint (Submonoid.powers g : Set A) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgP
  have hPBprime : PB.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers g) B P hP.isPrime hdisj
  let : PB.IsPrime := hPBprime
  have hfPB : φ f ∈ PB := Ideal.mem_map_of_mem φ (hP.le (Ideal.mem_span_singleton_self f))
  have hproper : Ideal.span {φ f} ≠ ⊤ := by
    intro he
    apply hPBprime.ne_top
    exact top_unique (he ▸ (Ideal.span_singleton_le_iff_mem _).mpr hfPB)
  have hdB := principal_quotient_dimension_add_one k B (φ f) hfB hproper
  have hradB : (Ideal.span {φ f}).radical = PB := by
    simpa only [Ideal.map_span, Set.image_singleton] using hrad
  have hdimrad : ringKrullDim (B ⧸ Ideal.span {φ f}) = ringKrullDim (B ⧸ PB) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient,
      ← PrimeSpectrum.zeroLocus_radical, hradB]
  let : IsLocalization.Away (Ideal.Quotient.mk P g) (B ⧸ PB) := by
    simpa only [IsLocalization.Away, Algebra.algebraMapSubmonoid, Submonoid.map_powers,
      Ideal.Quotient.algebraMap_eq] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid (A ⧸ P) (Submonoid.powers g)) (B ⧸ PB))
  let e := IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk P g))
    (Localization.Away (Ideal.Quotient.mk P g)) (B ⧸ PB)
  have hgQ : Ideal.Quotient.mk P g ≠ 0 := by
    intro he
    exact hgP (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have hdQ : ringKrullDim (B ⧸ PB) = ringKrullDim (A ⧸ P) :=
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans
      (ringKrullDim_localizationAway_of_finiteType_domain k (A ⧸ P) (Ideal.Quotient.mk P g) hgQ)
  rw [hdimrad, hdQ, ringKrullDim_localizationAway_of_finiteType_domain k A g hg] at hdB
  exact hdB

/-- Avoidance of central minimal primes excludes the parameter from every cut component. -/
theorem parameter_notMem_cut_minimalPrime {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (t f : A) (ht : t ≠ 0)
    (havoid : ∀ Q ∈ (Ideal.span {t}).minimalPrimes, f ∉ Q)
    (P : Ideal A) (hP : P ∈ (Ideal.span {f}).minimalPrimes) : t ∉ P := by
  let : P.IsPrime := hP.isPrime
  intro htP
  have hheight : P.height ≤ 1 := by
    simpa only [Set.ncard_singleton, Nat.cast_one] using
      Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_singleton f) hP
  have hmin : P ∈ (Ideal.span {t}).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr htP)
      (hheight.trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ht)))
  exact havoid P hmin (hP.le (Ideal.mem_span_singleton_self f))

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionDimension
