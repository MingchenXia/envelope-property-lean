/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Actual affine-domain heights and dimensions

True Noether normalization and normal-base going-down derive the common
maximal height of finite-type field domains and identify it with their actual
Krull dimension. These give positive-dimensional prime quotients, true
normal-integral dimension comparison and preservation under nonzero principal
localization. An integral positive-dimensional domain algebra over a genuine
dimension-at-most-one domain has injective coefficient map.

No component-dimension or geometric-integrality certificate is assumed.
-/

noncomputable section
namespace EnvelopeProperty

/-- Actual integral incomparability makes the residue-quotient height zero, so genuine going-down preserves the entire prime height. -/
theorem height_eq_under_of_isIntegral_of_hasGoingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  let I : Ideal S := (P.under R).map (algebraMap R S)
  have hm : P ∈ I.minimalPrimes := Ideal.IsIntegral.mem_minimalPrimes_map_under P
  rw [Ideal.minimalPrimes_eq_comap] at hm
  obtain ⟨q, hq, he⟩ := hm
  have : q.IsPrime := hq.isPrime
  have hmap : P.map (Ideal.Quotient.mk I) = q := by
    rw [← he, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hzero : (P.map (Ideal.Quotient.mk I)).height = 0 := by
    rw [hmap]
    exact Ideal.height_eq_zero_iff.mpr hq
  have ht := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P
  rw [hzero, add_zero] at ht
  exact ht

/-- A faithful integral domain extension of a genuinely normal base preserves every whole prime height. -/
theorem height_eq_under_of_normal_integral
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.IsIntegral R S]
    [IsDomain S] [FaithfulSMul R S] [IsIntegrallyClosed R]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height :=
  height_eq_under_of_isIntegral_of_hasGoingDown P

/-- Every actual maximal polynomial prime over any field has the full original coordinate height. -/
theorem maximalHeight_mvPolynomialFin (F : Type*) [Field F] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) F)) [M.IsMaximal] : M.height = (n : ℕ) := by
  induction n with
  | zero =>
    let e := (MvPolynomial.isEmptyAlgEquiv F (Fin 0)).toRingEquiv
    have : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M]
    apply bot_unique
    have ht := Ideal.height_le_ringKrullDim_of_isPrime (I := M.map e)
    have h0 : ((M.map e).height : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by
      simpa only [ringKrullDim_eq_zero_of_field, WithBot.coe_zero] using ht
    exact WithBot.coe_le_coe.mp h0
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv F n).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := P.under (MvPolynomial (Fin n) F)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    rw [← e.height_map M]
    change P.height = (n + 1 : ℕ)
    rw [Polynomial.height_eq_height_add_one p P, ih p]
    simp only [Nat.cast_add, Nat.cast_one]

/-- True Noether normalization and normal-base going-down derive a common genuine height for all maximal ideals of any finite-type field domain. -/
theorem exists_constant_maximalHeight_of_finiteType_domain
    (F R : Type*) [Field F] [CommRing R] [IsDomain R] [Algebra F R] [Algebra.FiniteType F R] :
    ∃ n : ℕ, ∀ (M : Ideal R), M.IsMaximal → M.height = (n : ℕ) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg F R
  let A := MvPolynomial (Fin n) F
  let : Algebra A R := g.toRingHom.toAlgebra
  have : Module.Finite A R := hfin
  have : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing F R
  refine ⟨n, ?_⟩
  intro M hM
  have : M.IsMaximal := hM
  have : (M.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M
  rw [height_eq_under_of_normal_integral (R := A) M]
  exact maximalHeight_mvPolynomialFin F n (M.under A)

/-- Every maximal ideal of a genuine finite-type field domain has the entire dimension of that original domain. -/
theorem maximalHeight_eq_ringKrullDim_of_finiteType_domain
    (F R : Type*) [Field F] [CommRing R] [IsDomain R] [Algebra F R] [Algebra.FiniteType F R]
    (M : Ideal R) [M.IsMaximal] : (M.height : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨n, hn⟩ := exists_constant_maximalHeight_of_finiteType_domain F R
  have hu : ringKrullDim R ≤ (n : WithBot ℕ∞) := by
    apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
    intro N hN
    rw [hn N hN]
    exact le_refl _
  have hl : (n : WithBot ℕ∞) ≤ ringKrullDim R := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    rw [hn M inferInstance] at h
    exact h
  have hd : ringKrullDim R = (n : WithBot ℕ∞) := le_antisymm hu hl
  rw [hn M inferInstance, hd]
  exact WithBot.coe_natCast n

/-- A prime of genuinely smaller height than the original affine-domain dimension has an actual positive-dimensional quotient. -/
theorem positive_dim_quotient_of_height_lt_of_finiteType_domain
    (F R : Type*) [Field F] [CommRing R] [IsDomain R] [Algebra F R] [Algebra.FiniteType F R]
    (P : Ideal R) [P.IsPrime] (hP : (P.height : WithBot ℕ∞) < ringKrullDim R) :
    0 < ringKrullDim (R ⧸ P) := by
  have hnmax : ¬ P.IsMaximal := by
    intro hM
    have : P.IsMaximal := hM
    exact (ne_of_lt hP) (maximalHeight_eq_ringKrullDim_of_finiteType_domain F R P)
  apply lt_of_not_ge
  intro hd
  have : Ring.KrullDimLE 0 (R ⧸ P) := Ring.krullDimLE_iff.mpr hd
  have hfield : IsField (R ⧸ P) := Ring.KrullDimLE.isField_of_isDomain
  exact hnmax ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr hfield)

/-- An integral domain algebra with genuinely positive dimension cannot annihilate a nonzero element of a dimension-at-most-one domain base. -/
theorem injective_algebraMap_of_isIntegral_of_positive_dim
    {C D : Type*} [CommRing C] [IsDomain C] [Ring.KrullDimLE 1 C]
    [CommRing D] [IsDomain D] [Algebra C D] [Algebra.IsIntegral C D]
    (hd : 0 < ringKrullDim D) : Function.Injective (algebraMap C D) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  by_contra hk
  have hprime : (RingHom.ker (algebraMap C D)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap C D)).IsMaximal := hprime.isMaximal_of_ne_bot hk
  have hbmax : (⊥ : Ideal D).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := C) _ hmax
  have hfield : IsField D := Ring.isField_iff_maximal_bot.mpr hbmax
  rw [ringKrullDim_eq_zero_of_isField hfield] at hd
  exact (lt_irrefl _ hd)

/-- Integral faithful extensions of a genuinely normal finite-type field domain preserve its actual original dimension. -/
theorem ringKrullDim_eq_of_normal_integral_finiteType_domain
    (F R S : Type*) [Field F] [CommRing R] [CommRing S] [IsDomain S]
    [Algebra F R] [Algebra F S] [Algebra R S]
    [Algebra.FiniteType F R] [Algebra.FiniteType F S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] [IsIntegrallyClosed R] :
    ringKrullDim S = ringKrullDim R := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R S)
    ((faithfulSMul_iff_algebraMap_injective R S).mp inferInstance)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing F R
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing F S
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := S)
  have : M.IsMaximal := hM
  have : (M.under R).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) M
  rw [← maximalHeight_eq_ringKrullDim_of_finiteType_domain F S M,
    height_eq_under_of_normal_integral (R := R) M,
    maximalHeight_eq_ringKrullDim_of_finiteType_domain F R (M.under R)]

/-- A genuine nonempty principal open of an affine finite-type field domain has the entire original dimension. -/
theorem ringKrullDim_localizationAway_of_finiteType_domain
    (F R : Type*) [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] [Algebra.FiniteType F R] (r : R) (hr : r ≠ 0) :
    ringKrullDim (Localization.Away r) = ringKrullDim R := by
  let S := Localization.Away r
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers r) S
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hr))
  have : Algebra.FinitePresentation R S := IsLocalization.Away.finitePresentation r
  have : Algebra.FiniteType F S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R S)
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := F)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := S)
  have : M.IsMaximal := hM
  have : (M.under R).IsMaximal :=
    ((IsLocalization.isMaximal_iff_isMaximal_disjoint (y := r) S M).mp hM).1
  rw [← maximalHeight_eq_ringKrullDim_of_finiteType_domain F S M,
    ← IsLocalization.height_under (Submonoid.powers r) M,
    maximalHeight_eq_ringKrullDim_of_finiteType_domain F R (M.under R)]

end EnvelopeProperty
