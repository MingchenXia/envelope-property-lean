/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.DomainLocalNormalization
import EnvelopeProperty.IntegralResidueLocalization

/-!
# Genuine normal local domains are standard geometrically unibranch

All reductions, fraction fields, integral closures and residue maps are the
literal original objects. No endpoint/fibre or normalization certificate is
assumed, and no Noetherianity, field or finiteness hypothesis is used.
-/
noncomputable section
namespace EnvelopeProperty.LocalNormalization
variable (R : Type*) [CommRing R] [IsIntegrallyClosed R]

/-- Actual integral closedness identifies the WHOLE closure in ANY original total fraction ring with the original coefficient ring. -/
def integralClosureEquivOfIntegrallyClosed (K : Type*) [CommRing K] [Algebra R K]
    [IsFractionRing R K] : integralClosure R K ≃ₐ[R] R :=
  (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot (R := R) (K := K))).trans
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K))

/-- Every original coefficient follows the actual integral-closure equivalence. -/
@[simp]
theorem integralClosureEquivOfIntegrallyClosed_algebraMap (K : Type*) [CommRing K] [Algebra R K]
    [IsFractionRing R K] (r : R) :
    integralClosureEquivOfIntegrallyClosed R K (algebraMap R (integralClosure R K) r) = r :=
  (integralClosureEquivOfIntegrallyClosed R K).commutes r

/-- The actual original total-fraction-ring integral-closure coefficient map is genuinely bijective. -/
theorem algebraMap_integralClosure_bijective_of_isIntegrallyClosed (K : Type*)
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Function.Bijective (algebraMap R (integralClosure R K)) := by
  let e := integralClosureEquivOfIntegrallyClosed R K
  constructor
  · intro a b hab
    simpa only [e, integralClosureEquivOfIntegrallyClosed_algebraMap] using congrArg e hab
  · intro y
    refine ⟨e y, e.injective ?_⟩
    exact e.commutes _

variable [IsDomain R]

/-- The actual literal reduced normalization of a normal domain is the ORIGINAL ring. -/
def normalDomainEquiv : Ring R ≃ₐ[R] R :=
  (domainNormalizationEquiv R (FractionRing R)).trans
    (integralClosureEquivOfIntegrallyClosed R (FractionRing R))

/-- The entire original coefficient map is retained by the genuine normal-domain equivalence. -/
@[simp]
theorem normalDomainEquiv_coefficientMap (r : R) :
    normalDomainEquiv R (coefficientMap R r) = r :=
  (normalDomainEquiv R).commutes r

/-- Genuine normality makes the ACTUAL original normalization coefficient map bijective. -/
theorem coefficientMap_bijective_of_isIntegrallyClosed : Function.Bijective (coefficientMap R) := by
  constructor
  · intro a b hab
    simpa only [normalDomainEquiv_coefficientMap] using congrArg (normalDomainEquiv R) hab
  · intro y
    refine ⟨normalDomainEquiv R y, ?_⟩
    apply (normalDomainEquiv R).injective
    exact normalDomainEquiv_coefficientMap R _

end EnvelopeProperty.LocalNormalization
namespace EnvelopeProperty
variable (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]

/-- Real normality of the ORIGINAL local domain derives STANDARD structural unibranchness. -/
theorem IsUnibranchLocalRing.of_isIntegrallyClosed : IsUnibranchLocalRing R where
  isDomain_reduced := LocalNormalization.reduced_isDomain R
  isLocalRing_normalization := (LocalNormalization.normalDomainEquiv R).toRingEquiv.symm.isLocalRing

namespace LocalNormalization

/-- The induced ORIGINAL residue map is genuinely bijective, not just an isomorphic residue field. -/
theorem residueFieldMap_bijective_of_isIntegrallyClosed :
    letI : IsUnibranchLocalRing R := IsUnibranchLocalRing.of_isIntegrallyClosed R
    Function.Bijective (residueFieldMap R) := by
  let : IsUnibranchLocalRing R := IsUnibranchLocalRing.of_isIntegrallyClosed R
  refine ⟨RingHom.injective _, ?_⟩
  intro z
  obtain ⟨n, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨r, rfl⟩ := (coefficientMap_bijective_of_isIntegrallyClosed R).surjective n
  exact ⟨IsLocalRing.residue R r, residueFieldMap_residue R r⟩

end LocalNormalization

/-- Genuine normal local-domain algebra DERIVES the STANDARD geometric-unibranch class. -/
theorem IsGeometricallyUnibranchLocalRing.of_isIntegrallyClosed :
    IsGeometricallyUnibranchLocalRing R := by
  let : IsUnibranchLocalRing R := IsUnibranchLocalRing.of_isIntegrallyClosed R
  exact {
    toIsUnibranchLocalRing := inferInstance
    residueFieldMap_isPurelyInseparable := isPurelyInseparable_of_surjective_fieldHom
      (LocalNormalization.residueFieldMap R)
      (LocalNormalization.residueFieldMap_bijective_of_isIntegrallyClosed R).surjective }

end EnvelopeProperty
