import EnvelopeProperty.Berkovich.SchemeNormalizationDominantLift
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Actual whole native normalization lift of an original DVR trait -/
open AlgebraicGeometry CategoryTheory Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeDVRNormalizationLift
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{u}} [IsIntegral X] (q : Spec (.of V) ⟶ X) [IsDominant q]

private theorem trait_stalk_normal (x : Spec (.of V)) :
    IsIntegrallyClosed ((Spec (.of V)).presheaf.stalk x) := by
  let : IsIntegrallyClosed V := inferInstance
  let : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime x.asIdeal)
      x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of V) x).commRingCatIsoToRingEquiv.symm

/-- Every ORIGINAL dominant DVR trait internally derives its unique whole actual normalization lift. -/
theorem existsUnique_lift : ∃! a : Spec (.of V) ⟶ IntegralSchemeNormalization.normalization X,
    a ≫ IntegralSchemeNormalization.projection X = q :=
  IntegralSchemeNormalization.existsUnique_dominant_normalization_lift q trait_stalk_normal

/-- The actual same original whole DVR trait map to the native normalization. -/
def lift : Spec (.of V) ⟶ IntegralSchemeNormalization.normalization X :=
  Classical.choose (existsUnique_lift q)

/-- The actual normalized trait retains EXACTLY its whole original projection. -/
theorem lift_projection : lift q ≫ IntegralSchemeNormalization.projection X = q :=
  (Classical.choose_spec (existsUnique_lift q)).1

end EnvelopeProperty.SchemeDVRNormalizationLift
