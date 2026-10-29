/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.DomainLocalNormalization
import EnvelopeProperty.IntegralResidueLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.RingHom

noncomputable section
namespace EnvelopeProperty.NormalizationLocalization
variable {A : Type*} [CommRing A] [IsDomain A]
  (p : Ideal A) [p.IsPrime]

private local instance domainNormalizationLocalClosureAlgebra :
    Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
  (closureMap (A := A) (S := Localization.AtPrime p) (K := FractionRing A)).toAlgebra

private local instance domainNormalizationLocalClosureBaseTower :
    IsScalarTower A (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) := .of_algebraMap_eq' rfl

private local instance domainNormalizationLocalClosureAmbientTower :
    IsScalarTower (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) (FractionRing A) :=
  .of_algebraMap_eq' rfl

/-- STANDARD local unibranchness makes the ACTUAL original same-field local normalization local. -/
theorem isLocalRing_atPrime_normalization [IsUnibranchLocalRing (Localization.AtPrime p)] :
    IsLocalRing (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
  LocalNormalization.isLocalRing_domainNormalization (Localization.AtPrime p) (FractionRing A)

private local instance domainNormalizationLocalClosureLocal
    [IsUnibranchLocalRing (Localization.AtPrime p)] :
    IsLocalRing (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
  isLocalRing_atPrime_normalization p

/-- Structural local unibranchness DERIVES equality of original normalization primes over p. -/
theorem primes_eq_of_isUnibranch_atPrime [IsUnibranchLocalRing (Localization.AtPrime p)]
    (q q' : Ideal (integralClosure A (FractionRing A))) [q.IsPrime] [q'.IsPrime]
    (hq : q.under A = p) (hq' : q'.under A = p) : q = q' :=
  primes_eq_of_local_normalization_isLocal (S := Localization.AtPrime p) p q q' hq hq'

/-- STANDARD geometric unibranchness gives pure inseparability of the ACTUAL original prime residue map. -/
theorem residueFieldMap_isPurelyInseparable_of_isGeometricallyUnibranch_atPrime
    [IsGeometricallyUnibranchLocalRing (Localization.AtPrime p)]
    (q : Ideal (integralClosure A (FractionRing A))) [q.IsPrime] (hq : q.under A = p) :
    (Ideal.ResidueField.map p q (algebraMap A (integralClosure A (FractionRing A))) hq.symm).IsPurelyInseparable := by
  let D := integralClosure (Localization.AtPrime p) (FractionRing A)
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl) D :=
    isLocalization_closure p.primeCompl
  have hmap : EnvelopeProperty.baseLocalizationHom (T := D) p q hq =
      algebraMap (Localization.AtPrime p) D := by
    rw [EnvelopeProperty.baseLocalizationHom_eq_map]
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro a
    change IsLocalization.map
      (T := Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl)
      D (algebraMap A (integralClosure A (FractionRing A)))
      (show p.primeCompl ≤ (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A))
        p.primeCompl).comap (algebraMap A (integralClosure A (FractionRing A))) from
          p.primeCompl.le_comap_map)
      (algebraMap A (Localization.AtPrime p) a) =
        algebraMap (Localization.AtPrime p) D (algebraMap A (Localization.AtPrime p) a)
    rw [IsLocalization.map_eq]
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A) a
  apply EnvelopeProperty.residueFieldMap_isPurelyInseparable_of_local_baseLocalization
    (T := D) p q hq
  have hlocal : IsLocalHom (algebraMap (Localization.AtPrime p) D) :=
    LocalNormalization.domainNormalization_isLocalHom (Localization.AtPrime p) (FractionRing A)
  have hpure := LocalNormalization.domainResidueFieldMap_isPurelyInseparable
    (Localization.AtPrime p) (FractionRing A)
  change (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime p) D)).IsPurelyInseparable at hpure
  convert hpure using 1
  apply Ideal.Quotient.ringHom_ext
  ext r
  exact congrArg (IsLocalRing.residue D) (RingHom.congr_fun hmap r)

/-- Whole prime contraction of the LITERAL normalization is injective, DERIVED from structural local unibranchness at every original prime. -/
theorem injective_primeSpectrumComap_of_isUnibranch
    (h : ∀ p : PrimeSpectrum A, IsUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    Function.Injective (PrimeSpectrum.comap (algebraMap A (integralClosure A (FractionRing A)))) := by
  intro q q' hqq'
  let p := PrimeSpectrum.comap (algebraMap A (integralClosure A (FractionRing A))) q
  let : IsUnibranchLocalRing (Localization.AtPrime p.asIdeal) := h p
  apply PrimeSpectrum.ext
  exact primes_eq_of_isUnibranch_atPrime p.asIdeal q.asIdeal q'.asIdeal rfl
    (congrArg PrimeSpectrum.asIdeal hqq').symm

end EnvelopeProperty.NormalizationLocalization
