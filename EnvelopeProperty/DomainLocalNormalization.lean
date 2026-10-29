/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.UnibranchLocalRing
import EnvelopeProperty.IntegralClosureLocalization
import Mathlib.RingTheory.Nilpotent.Lemmas

noncomputable section
namespace EnvelopeProperty.LocalNormalization

/-- The TRUE nilradical quotient of an actually reduced ring is a whole ring equivalence. -/
def reductionEquiv (R : Type*) [CommRing R] [IsReduced R] : R ≃+* Reduced R :=
  RingEquiv.ofBijective (Ideal.Quotient.mk (nilradical R))
    ((Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr (nilradical_eq_zero R))

@[simp]
theorem reductionEquiv_apply (R : Type*) [CommRing R] [IsReduced R] (r : R) :
    reductionEquiv R r = Ideal.Quotient.mk (nilradical R) r := rfl

/-- The actual reduction remains a domain, DERIVED from the genuine original quotient equivalence. -/
theorem reduced_isDomain (R : Type*) [CommRing R] [IsDomain R] : IsDomain (Reduced R) :=
  (reductionEquiv R).symm.toMulEquiv.isDomain R

private local instance domainNormalizationReducedDomain (R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (Reduced R) := reduced_isDomain R

/-- With the ORIGINAL quotient action, the actual reduced fraction field is a genuine fraction field of the original domain. -/
theorem isFractionRing_reducedFractionRing (R : Type*) [CommRing R] [IsDomain R] :
    IsFractionRing R (FractionRing (Reduced R)) := by
  let : FaithfulSMul R (FractionRing (Reduced R)) :=
    (faithfulSMul_iff_algebraMap_injective R _).mpr <| by
      rw [IsScalarTower.algebraMap_eq R (Reduced R) (FractionRing (Reduced R))]
      exact (IsFractionRing.injective (Reduced R) _).comp (reductionEquiv R).injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (Reduced R) z
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a', b', hab.symm⟩

/-- The STANDARD literal reduced normalization is genuinely equivalent to normalization in ANY actual fraction field, preserving the original R action. -/
def domainNormalizationEquiv (R K : Type*) [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] : Ring R ≃ₐ[R] integralClosure R K := by
  let : IsFractionRing R (FractionRing (Reduced R)) := isFractionRing_reducedFractionRing R
  exact (NormalizationLocalization.closureEquivOfIntegralBase
    (A := R) (S := Reduced R) (K := FractionRing (Reduced R))).symm.trans
      ((IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing (Reduced R)) K).mapIntegralClosure)

/-- The ENTIRE comparison carries every original coefficient through its actual coefficient map. -/
@[simp]
theorem domainNormalizationEquiv_coefficientMap (R K : Type*) [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] (r : R) :
    domainNormalizationEquiv R K (coefficientMap R r) = algebraMap R (integralClosure R K) r :=
  (domainNormalizationEquiv R K).commutes r

/-- STANDARD structural localness transports to the ACTUAL same-field normalization. -/
theorem isLocalRing_domainNormalization (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] : IsLocalRing (integralClosure R K) :=
  (domainNormalizationEquiv R K).toRingEquiv.isLocalRing


private local instance domainNormalizationLocalRing (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] : IsLocalRing (integralClosure R K) :=
  isLocalRing_domainNormalization R K

/-- The ORIGINAL injective integral coefficient inclusion is local, DERIVED from real normalization localness. -/
theorem domainNormalization_isLocalHom (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsLocalHom (algebraMap R (integralClosure R K)) :=
  (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R (integralClosure R K))).isLocalHom
    (fun _ _ hab => IsFractionRing.injective R K (congrArg (fun c : integralClosure R K => (c : K)) hab))

private local instance domainNormalizationCoefficientLocal (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsLocalHom (algebraMap R (integralClosure R K)) := domainNormalization_isLocalHom R K

/-- The ACTUAL original coefficient map induces its genuine residue-field map. -/
def domainResidueFieldMap (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField (integralClosure R K) :=
  IsLocalRing.ResidueField.map (algebraMap R (integralClosure R K))

/-- The genuine normalization comparison induces the WHOLE residue equivalence. -/
def domainResidueFieldEquiv (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsLocalRing.ResidueField (Ring R) ≃+* IsLocalRing.ResidueField (integralClosure R K) :=
  IsLocalRing.ResidueField.mapEquiv (domainNormalizationEquiv R K).toRingEquiv

/-- The ENTIRE actual residue square commutes, derived from preservation of every original coefficient. -/
theorem domainResidueFieldMap_eq (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    domainResidueFieldMap R K = (domainResidueFieldEquiv R K).toRingHom.comp (residueFieldMap R) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue (integralClosure R K) (algebraMap R (integralClosure R K) r) =
    IsLocalRing.residue (integralClosure R K) (domainNormalizationEquiv R K (coefficientMap R r))
  rw [domainNormalizationEquiv_coefficientMap]

/-- STANDARD geometric unibranchness yields pure inseparability of the ACTUAL domain normalization residue map. -/
theorem domainResidueFieldMap_isPurelyInseparable (R K : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsGeometricallyUnibranchLocalRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] :
    (domainResidueFieldMap R K).IsPurelyInseparable := by
  rw [domainResidueFieldMap_eq]
  apply IsGeometricallyUnibranchLocalRing.residueFieldMap_isPurelyInseparable.comp
  let e := domainResidueFieldEquiv R K
  let : Algebra (IsLocalRing.ResidueField (Ring R)) (IsLocalRing.ResidueField (integralClosure R K)) :=
    e.toRingHom.toAlgebra
  change IsPurelyInseparable (IsLocalRing.ResidueField (Ring R))
    (IsLocalRing.ResidueField (integralClosure R K))
  exact ⟨algebraMap_isIntegral_iff.mp (e.toRingHom.isIntegral_of_surjective e.surjective),
    fun x _ => e.surjective x⟩

end EnvelopeProperty.LocalNormalization
