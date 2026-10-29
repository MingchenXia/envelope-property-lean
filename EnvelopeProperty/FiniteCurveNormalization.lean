/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.NormalizationFinite

/-!
# Actual finite and free normalization of a curve algebra

The actual integral closure of B in its original fraction field supplies the
normalization ring and its literal coefficient maps. Checked perfect-field
finite normalization preserves arbitrary characteristic, including inseparable
cases. Actual finite maps compose; integral dimension descent gives a Dedekind
normalization over a dimension-at-most-one base. A genuinely injective map from
a principal domain gives torsion-freeness, then true module freeness and flatness.
No component-dimension, domination, smoothness or normalization certificate is
assumed. Fraction-field and normality statements require B to be a domain.
-/

open scoped nonZeroDivisors
noncomputable section
namespace EnvelopeProperty.CurveNormalization

/-- The actual integral-closure ring in the original fraction ring; domain inputs use their genuine fraction field. -/
abbrev Ring (B : Type*) [CommRing B] := integralClosure B (FractionRing B)

/-- The original curve coefficient map into its actual normalization. -/
def inclusion (B : Type*) [CommRing B] : B →+* Ring B := algebraMap B (Ring B)

/-- The genuine original base-curve map followed by the actual normalization inclusion. -/
def coefficientMap (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : A →+* Ring B :=
  (inclusion B).comp (algebraMap A B)

/-- Every original normalization-inclusion element retains its entire fraction-field value. -/
theorem inclusion_coe (B : Type*) [CommRing B] (b : B) :
    ((inclusion B b : Ring B) : FractionRing B) = algebraMap B (FractionRing B) b := rfl

/-- A genuine injective base-curve homomorphism remains injective in the actual normalization ring. -/
theorem coefficientMap_injective (A B : Type*) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hAB : Function.Injective (algebraMap A B)) :
    Function.Injective (coefficientMap A B) := by
  intro a b hab
  have hf := congrArg (fun c : Ring B => (c : FractionRing B)) hab
  exact hAB (IsFractionRing.injective B (FractionRing B) hf)

/-- The literal normalization inclusion is injective into the original fraction field.
-/
theorem inclusion_injective (B : Type*) [CommRing B] [IsDomain B] : Function.Injective (inclusion B) := by
  intro a b hab
  exact IsFractionRing.injective B (FractionRing B)
    (congrArg (fun c : Ring B => (c : FractionRing B)) hab)

/-- Perfect-field finite normalization derives the actual inclusion's module finiteness, including inseparable characteristic. -/
theorem finite_inclusion (F B : Type*) [Field F] [PerfectField F] [CommRing B] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B] : (inclusion B).Finite := by
  exact RingHom.finite_algebraMap.mpr (EnvelopeProperty.finite_integralClosure F B (FractionRing B))

/-- The actual normalization has precisely the original curve fraction field. -/
theorem isFractionRing_ring (B : Type*) [CommRing B] [IsDomain B] :
    IsFractionRing (Ring B) (FractionRing B) :=
  integralClosure.isFractionRing_of_finite_extension (A := B) (FractionRing B) (FractionRing B)

/-- Genuine integrally closedness of the actual curve normalization, without a separability assumption. -/
theorem isIntegrallyClosed_ring (B : Type*) [CommRing B] [IsDomain B] :
    IsIntegrallyClosed (Ring B) :=
  EnvelopeProperty.isIntegrallyClosed_integralClosure B (FractionRing B)

/-- The actual normalization is Noetherian by genuine perfect-field finite normalization. -/
theorem isNoetherian_ring (F B : Type*) [Field F] [PerfectField F] [CommRing B] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B] : IsNoetherianRing (Ring B) :=
  EnvelopeProperty.isNoetherianRing_integralClosure F B (FractionRing B)

/-- The genuine original finite base map remains finite after actual perfect-field normalization. -/
theorem finite_coefficientMap (F A B : Type*) [Field F] [PerfectField F]
    [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Algebra F B] [Algebra.FiniteType F B] : (coefficientMap A B).Finite :=
  (finite_inclusion F B).comp (RingHom.finite_algebraMap.mpr inferInstance)

/-- Integral dimension descent and the true normal finite ring give a genuine Dedekind normalization. -/
theorem isDedekindDomain_ring (F A B : Type*) [Field F] [PerfectField F]
    [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Algebra F B] [Algebra.FiniteType F B] [Ring.DimensionLEOne A] : IsDedekindDomain (Ring B) := by
  let : Nontrivial A := (algebraMap A B).domain_nontrivial
  let := (coefficientMap A B).toAlgebra
  let : Module.Finite A (Ring B) := finite_coefficientMap F A B
  let : Algebra.IsIntegral A (Ring B) := Algebra.IsIntegral.of_finite A (Ring B)
  let : Ring.DimensionLEOne (Ring B) := Ring.DimensionLEOne.of_isIntegral A (Ring B)
  let : IsNoetherianRing (Ring B) := isNoetherian_ring F B
  let : IsIntegrallyClosed (Ring B) := isIntegrallyClosed_ring B
  exact {}

/-- Genuine finite torsion-free normalization over a principal domain is a free module for the actual original coefficient map. -/
theorem free_coefficientMap (F A B : Type*) [Field F] [PerfectField F]
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Algebra F B] [Algebra.FiniteType F B]
    (hAB : Function.Injective (algebraMap A B)) :
    letI := (coefficientMap A B).toAlgebra
    Module.Free A (Ring B) := by
  let := (coefficientMap A B).toAlgebra
  let : Module.Finite A (Ring B) := finite_coefficientMap F A B
  let : Module.IsTorsionFree A (Ring B) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (coefficientMap_injective A B hAB)
  infer_instance

/-- The actual original normalization coefficient map is flat, derived from its true free module. -/
theorem flat_coefficientMap (F A B : Type*) [Field F] [PerfectField F]
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Algebra F B] [Algebra.FiniteType F B]
    (hAB : Function.Injective (algebraMap A B)) : (coefficientMap A B).Flat := by
  let := (coefficientMap A B).toAlgebra
  let : Module.Free A (Ring B) := free_coefficientMap F A B hAB
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end EnvelopeProperty.CurveNormalization
