/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Generic smoothness: a reduced variety over a perfect field has a smooth closed point

This file proves the input from generic smoothness used in the proof of Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, Theorem 5.25
(`thm:normal-local-regularization`): "since `W` is reduced and `k` is perfect, `W` is smooth at
some closed point `z`".

`exists_isMaximal_isSmoothAt`: if `R ≠ 0` is a reduced algebra of finite type over a perfect field
`k`, some maximal ideal `z` of `R` lies in the smooth locus (`Algebra.IsSmoothAt k z`, i.e. `R_z`
is formally smooth over `k`; by Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth` this is
smoothness of `Spec R → Spec k` at `z` in the sense of the Stacks project).

## Proof

Let `P` be a minimal prime of `R`. As `R` is reduced, `R_P` is a field (its maximal ideal is the
nilradical, `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`), essentially of finite type
over `k`, hence formally smooth over the perfect field `k`
(`Algebra.FormallySmooth.of_perfectField`).
So `P` lies in the smooth locus, which is open (`Algebra.isOpen_smoothLocus`): there is `f ∉ P`
with `D(f)` in the smooth locus. As `f ≠ 0` and `R` is reduced and Jacobson
(`isJacobsonRing_of_finiteType`), some maximal ideal `z` misses `f`, and `z ∈ D(f)`.
-/

namespace EnvelopeProperty

/-- In a reduced ring, the zero ideal is radical. -/
theorem radical_bot_of_isReduced (S : Type*) [CommRing S] [IsReduced S] :
    (⊥ : Ideal S).radical = ⊥ :=
  nilradical_eq_zero S

/-- The localization of a reduced ring at a minimal prime is a field. -/
theorem isField_localization_atPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] [IsReduced R]
    (P : Ideal R) [P.IsPrime] (hP : P ∈ minimalPrimes R) :
    IsField (Localization.AtPrime P) := by
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime P) P ⊥ hP
  rw [Ideal.map_bot, radical_bot_of_isReduced, Localization.AtPrime.map_eq_maximalIdeal] at h
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h.symm

/-- **Generic smoothness** (existence of a smooth closed point). A nonzero reduced algebra `R` of
finite type over a perfect field `k` has a maximal ideal `z` at which it is smooth over `k`. -/
theorem exists_isMaximal_isSmoothAt (k R : Type*) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] [IsReduced R] [Nontrivial R] :
    ∃ (z : Ideal R) (_ : z.IsMaximal), Algebra.IsSmoothAt k z := by
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := m) bot_le
  have hPprime : P.IsPrime := hP.1.1
  -- `R_P` is a field, essentially of finite type over `k`, hence formally smooth.
  have hsmP : Algebra.IsSmoothAt k P := by
    let := (isField_localization_atPrime_of_mem_minimalPrimes P hP).toField
    have : Algebra.EssFiniteType R (Localization.AtPrime P) :=
      .of_isLocalization _ P.primeCompl
    have : Algebra.EssFiniteType k (Localization.AtPrime P) := .comp k R _
    exact Algebra.FormallySmooth.of_perfectField
  obtain ⟨f, hfP, hf⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k P
  have hD : ↑(PrimeSpectrum.basicOpen f) ⊆ Algebra.smoothLocus k R :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hf
  -- A maximal ideal missing `f`, by the Jacobson property.
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hf0 : f ∉ (⊥ : Ideal R).jacobson := by
    rw [IsJacobsonRing.out' (⊥ : Ideal R) (by
      rw [Ideal.IsRadical, radical_bot_of_isReduced])]
    intro h
    exact hfP ((Ideal.mem_bot.mp h).symm ▸ P.zero_mem)
  simp only [Ideal.jacobson, Ideal.mem_sInf, Set.mem_ofPred_eq, bot_le, true_and, not_forall]
    at hf0
  obtain ⟨z, hz, hfz⟩ := hf0
  exact ⟨z, hz, hD (show (⟨z, hz.isPrime⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen f from hfz)⟩

end EnvelopeProperty
