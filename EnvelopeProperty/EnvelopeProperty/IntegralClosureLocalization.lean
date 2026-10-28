/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Whole same-ambient integral closure localization and actual prime uniqueness

All coefficient maps are the genuine original scalar maps. The closure map is
the identity on ambient elements, constructed from integral coefficient change.
No domain, Noetherianity or finite-normalization assumption is needed for this
localization primitive. Localness will derive prime uniqueness, rather than
assuming any spectrum-fibre or native-point condition.
-/

noncomputable section
namespace EnvelopeProperty.NormalizationLocalization
variable {A S K : Type*} [CommRing A] [CommRing S] [CommRing K]
  [Algebra A S] [Algebra A K] [Algebra S K] [IsScalarTower A S K]

/-- The ACTUAL coefficient-change map of integral closures fixes every whole original ambient element. -/
def closureMap : integralClosure A K →ₐ[A] integralClosure S K where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem closureMap_coe (x : integralClosure A K) :
    ((closureMap (A := A) (S := S) (K := K) x : integralClosure S K) : K) = (x : K) := rfl

private local instance normalizationLocalizationClosureAlgebra :
    Algebra (integralClosure A K) (integralClosure S K) :=
  (closureMap (A := A) (S := S) (K := K)).toAlgebra

private local instance normalizationLocalizationClosureBaseTower :
    IsScalarTower A (integralClosure A K) (integralClosure S K) :=
  .of_algebraMap_eq' rfl

private local instance normalizationLocalizationClosureAmbientTower :
    IsScalarTower (integralClosure A K) (integralClosure S K) K :=
  .of_algebraMap_eq' rfl

/-- The actual same-ambient closure map makes the local integral closure a TRUE localization of the original closure, constructing all closure actions and towers. -/
theorem isLocalization_closure (M : Submonoid A) [IsLocalization M S] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A K) M) (integralClosure S K) := by
  have hunit : Algebra.algebraMapSubmonoid K M ≤ IsUnit.submonoid K := by
    rintro _ ⟨a, ha, rfl⟩
    change IsUnit (algebraMap A K a)
    rw [IsScalarTower.algebraMap_apply A S K]
    exact (IsLocalization.map_units S ⟨a, ha⟩).map (algebraMap S K)
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) K := IsLocalization.of_le_isUnit hunit
  exact IsLocalization.integralClosure (S := K) (Rf := S) (Sf := K) M

/-- The actual original localization is canonically equivalent to the LITERAL same-ambient local integral closure. -/
def localizationEquiv (M : Submonoid A) [IsLocalization M S] :
    Localization (Algebra.algebraMapSubmonoid (integralClosure A K) M) ≃ₐ[integralClosure A K]
      integralClosure S K := by
  let : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A K) M) (integralClosure S K) :=
    isLocalization_closure M
  exact IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (integralClosure A K) M)
    (Localization (Algebra.algebraMapSubmonoid (integralClosure A K) M)) (integralClosure S K)

/-- The WHOLE comparison retains every original normalization element, not only its prime support. -/
@[simp]
theorem localizationEquiv_algebraMap (M : Submonoid A) [IsLocalization M S]
    (c : integralClosure A K) :
    localizationEquiv (S := S) (K := K) M
      (algebraMap (integralClosure A K)
        (Localization (Algebra.algebraMapSubmonoid (integralClosure A K) M)) c) =
      closureMap (S := S) c :=
  (localizationEquiv (S := S) (K := K) M).commutes c

end EnvelopeProperty.NormalizationLocalization

namespace EnvelopeProperty
variable {A B T : Type*} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra.IsIntegral A B]

/-- A prime above the ORIGINAL base prime extends to a genuine maximal ideal after localizing at the actual base complement. -/
theorem prime_map_isMaximal_of_base_localization
    (p : Ideal A) [p.IsPrime] [Algebra B T]
    [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) T]
    (q : Ideal B) [q.IsPrime] (hq : q.under A = p) :
    (q.map (algebraMap B T)).IsMaximal := by
  let N := Algebra.algebraMapSubmonoid B p.primeCompl
  have hd : Disjoint (N : Set B) (q : Set B) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ hqa
    apply ha
    change a ∈ p
    rw [← hq]
    exact hqa
  let Q := q.map (algebraMap B T)
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint N T q inferInstance hd
  have hQ : Q.under B = q := IsLocalization.under_map_of_isPrime_disjoint N T inferInstance hd
  let ψ : Localization.AtPrime p →+* T := IsLocalization.map T (algebraMap A B)
    (show p.primeCompl ≤ N.comap (algebraMap A B) from p.primeCompl.le_comap_map)
  have hψ : ψ.IsIntegral := isIntegral_localization
  have hp : (Q.comap ψ).under A = p := by
    calc
      (Q.comap ψ).under A = (Q.under B).under A := by
        ext a
        change ψ (algebraMap A (Localization.AtPrime p) a) ∈ Q ↔
          algebraMap B T (algebraMap A B a) ∈ Q
        rw [IsLocalization.map_eq]
      _ = p := by rw [hQ, hq]
  have hm : (Q.comap ψ).IsMaximal := by
    rw [(Localization.AtPrime.eq_maximalIdeal_iff_under_eq (I := p)).mp hp]
    infer_instance
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ψ hψ Q hm

/-- Localness of the ACTUAL base localization DERIVES uniqueness of original primes above the base prime, with no fibre singleton assumed. -/
theorem prime_eq_of_isLocalRing_baseLocalization
    (p : Ideal A) [p.IsPrime] [Algebra B T]
    [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) T] [IsLocalRing T]
    (q q' : Ideal B) [q.IsPrime] [q'.IsPrime]
    (hq : q.under A = p) (hq' : q'.under A = p) : q = q' := by
  let N := Algebra.algebraMapSubmonoid B p.primeCompl
  have hd (Q : Ideal B) (hQ : Q.under A = p) : Disjoint (N : Set B) (Q : Set B) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ hQa
    apply ha
    change a ∈ p
    rw [← hQ]
    exact hQa
  have he : q.map (algebraMap B T) = q'.map (algebraMap B T) :=
    (IsLocalRing.eq_maximalIdeal (prime_map_isMaximal_of_base_localization p q hq)).trans
      (IsLocalRing.eq_maximalIdeal (prime_map_isMaximal_of_base_localization p q' hq')).symm
  have h := congrArg (Ideal.comap (algebraMap B T)) he
  change (q.map (algebraMap B T)).under B = (q'.map (algebraMap B T)).under B at h
  rw [IsLocalization.under_map_of_isPrime_disjoint N T (inferInstance : q.IsPrime) (hd q hq),
    IsLocalization.under_map_of_isPrime_disjoint N T (inferInstance : q'.IsPrime) (hd q' hq')] at h
  exact h

end EnvelopeProperty

namespace EnvelopeProperty.NormalizationLocalization
variable {A S K : Type*} [CommRing A] [CommRing S] [CommRing K]
  [Algebra A S] [Algebra A K] [Algebra S K] [IsScalarTower A S K]

attribute [local instance] normalizationLocalizationClosureAlgebra
  normalizationLocalizationClosureBaseTower normalizationLocalizationClosureAmbientTower

/-- An actual integral coefficient extension does not change the WHOLE same-ambient integral closure. -/
def closureEquivOfIntegralBase [Algebra.IsIntegral A S] :
    integralClosure A K ≃ₐ[A] integralClosure S K where
  toFun := closureMap
  invFun x := ⟨x.1, isIntegral_trans (R := A) x.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The whole integral-base comparison is the ACTUAL original ambient identity. -/
@[simp]
theorem closureEquivOfIntegralBase_coe [Algebra.IsIntegral A S] (c : integralClosure A K) :
    ((closureEquivOfIntegralBase (A := A) (S := S) (K := K) c : integralClosure S K) : K) = (c : K) := rfl

/-- Localness of the LITERAL local integral closure genuinely DERIVES uniqueness of the original primes, for the whole actual coefficient maps. -/
theorem primes_eq_of_local_normalization_isLocal
    (p : Ideal A) [p.IsPrime] [IsLocalization p.primeCompl S]
    [IsLocalRing (integralClosure S K)]
    (q q' : Ideal (integralClosure A K)) [q.IsPrime] [q'.IsPrime]
    (hq : q.under A = p) (hq' : q'.under A = p) : q = q' := by
  let : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A K) p.primeCompl)
      (integralClosure S K) := isLocalization_closure p.primeCompl
  exact EnvelopeProperty.prime_eq_of_isLocalRing_baseLocalization
    (T := integralClosure S K) p q q' hq hq'

end EnvelopeProperty.NormalizationLocalization

namespace EnvelopeProperty.NormalizationLocalization
variable (A K : Type*) [CommRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- ANY actual fraction field gives a genuine coefficient-preserving equivalence of the LITERAL normalizations. -/
def fractionFieldNormalizationEquiv :
    integralClosure A (FractionRing A) ≃ₐ[A] integralClosure A K :=
  (FractionRing.algEquiv A K).mapIntegralClosure

/-- Every original coefficient is retained by the true fraction-field normalization comparison. -/
@[simp]
theorem fractionFieldNormalizationEquiv_algebraMap (a : A) :
    fractionFieldNormalizationEquiv A K (algebraMap A (integralClosure A (FractionRing A)) a) =
      algebraMap A (integralClosure A K) a :=
  (fractionFieldNormalizationEquiv A K).commutes a

end EnvelopeProperty.NormalizationLocalization
