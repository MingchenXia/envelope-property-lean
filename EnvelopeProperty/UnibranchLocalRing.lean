/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Standard structural local-ring unibranchness

The definition is Stacks Project, More on Algebra, `definition-unibranch`,
citing EGA IV, Chapter 0 (23.2.1): the actual reduction is a domain, its
literal normalization is local, and geometric unibranchness additionally
requires the actual induced residue extension to be purely inseparable.
The separate strict-henselization characterization is not asserted.
No spectrum-fibre or native-point-injectivity condition is an input.
-/

noncomputable section
namespace EnvelopeProperty
namespace LocalNormalization

/-- The actual reduction, retaining every original coefficient through its true quotient map. -/
abbrev Reduced (R : Type*) [CommRing R] := R ⧸ nilradical R

/-- The LITERAL normalization of the actual reduction in its actual fraction ring. -/
abbrev Ring (R : Type*) [CommRing R] :=
  integralClosure (Reduced R) (FractionRing (Reduced R))

/-- The actual original local-ring coefficient map through reduction and literal normalization. -/
def coefficientMap (R : Type*) [CommRing R] : R →+* Ring R :=
  (algebraMap (Reduced R) (Ring R)).comp (Ideal.Quotient.mk (nilradical R))

/-- Every actual reduced coefficient remains distinct in its literal normalization when the reduction is a domain. -/
theorem reduced_inclusion_injective (R : Type*) [CommRing R] [IsDomain (Reduced R)] :
    Function.Injective (algebraMap (Reduced R) (Ring R)) := by
  intro a b hab
  exact IsFractionRing.injective (Reduced R) (FractionRing (Reduced R))
    (congrArg (fun c : Ring R => (c : FractionRing (Reduced R))) hab)

end LocalNormalization

/-- STANDARD local-ring unibranchness: the literal reduction is a domain and its literal normalization is local (Stacks `definition-unibranch`, EGA IV 0,23.2.1). -/
class IsUnibranchLocalRing (R : Type*) [CommRing R] [IsLocalRing R] : Prop where
  isDomain_reduced : IsDomain (LocalNormalization.Reduced R)
  isLocalRing_normalization : IsLocalRing (LocalNormalization.Ring R)

attribute [instance] IsUnibranchLocalRing.isDomain_reduced
  IsUnibranchLocalRing.isLocalRing_normalization

namespace LocalNormalization

/-- The actual original coefficient map is local, DERIVED from the real reduction quotient and injective integral normalization inclusion. -/
instance coefficientMap_isLocalHom (R : Type*) [CommRing R] [IsLocalRing R]
    [IsUnibranchLocalRing R] : IsLocalHom (coefficientMap R) := by
  let : IsLocalHom (Ideal.Quotient.mk (nilradical R)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap (Reduced R) (Ring R)) :=
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral (Reduced R) (Ring R))).isLocalHom
      (reduced_inclusion_injective R)
  change IsLocalHom ((algebraMap (Reduced R) (Ring R)).comp (Ideal.Quotient.mk (nilradical R)))
  infer_instance

/-- The GENUINE residue-field map of the original coefficient homomorphism; no unrelated residue action is supplied. -/
def residueFieldMap (R : Type*) [CommRing R] [IsLocalRing R] [IsUnibranchLocalRing R] :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField (Ring R) :=
  IsLocalRing.ResidueField.map (coefficientMap R)

/-- Every original residue evaluation follows the entire actual original coefficient map. -/
@[simp]
theorem residueFieldMap_residue (R : Type*) [CommRing R] [IsLocalRing R]
    [IsUnibranchLocalRing R] (r : R) :
    residueFieldMap R (IsLocalRing.residue R r) =
      IsLocalRing.residue (Ring R) (coefficientMap R r) :=
  IsLocalRing.ResidueField.map_residue _ r

end LocalNormalization

/-- STANDARD geometric unibranchness adds pure inseparability of the ACTUAL original residue-field map, not a scheme or native singleton-fibre hypothesis. -/
class IsGeometricallyUnibranchLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    : Prop extends IsUnibranchLocalRing R where
  residueFieldMap_isPurelyInseparable : (LocalNormalization.residueFieldMap R).IsPurelyInseparable

end EnvelopeProperty
