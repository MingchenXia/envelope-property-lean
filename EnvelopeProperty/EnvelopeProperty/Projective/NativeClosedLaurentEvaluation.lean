/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeClosedParameterMaps

/-!
# Whole Laurent evaluation maps and actual unit sections

Genuine Laurent evaluation provides entire closed-family maps, with exact
composition formulas against the actual universal action and projection.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The whole actual universal Laurent unit maps to the prescribed actual unit. -/
theorem parameterLaurentUnit_map_eval (f : R →+* S) (v : Sˣ) :
    Units.map (LaurentPolynomial.eval₂ f v).toMonoidHom (parameterLaurentUnit R) = v := by
  apply Units.ext
  simp [parameterLaurentUnit]

namespace ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual Laurent evaluation preserves the whole original homogeneous ideal
image, without any ideal-comparison assumption. -/
theorem homogeneousIdeal_coefficient_map_laurentEval
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) (v : Sˣ) :
    (J.map (coefficientGradedMap LaurentPolynomial.C)).map
        (coefficientGradedMap (LaurentPolynomial.eval₂ f v)) = J.map (coefficientGradedMap f) := by
  rw [homogeneousIdeal_coefficient_map_map]
  have h : (LaurentPolynomial.eval₂ f v).comp LaurentPolynomial.C = f := by
    ext r
    exact LaurentPolynomial.eval₂_C f v r
  rw [h]

/-- An actual whole Laurent evaluation and independent parameter-unit scaling
between the prescribed original closed families. -/
def nativeClosedLaurentEvaluationMap
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : R →+* S)
    (h : J.map (coefficientGradedMap f) = K) (v u : Sˣ) :
    (nativeConstantIdeal K).subscheme ⟶
      (nativeConstantIdeal (J.map (coefficientGradedMap LaurentPolynomial.C))).subscheme :=
  nativeClosedParameterMapOfIdealMap _ _ (LaurentPolynomial.eval₂ f v)
    ((homogeneousIdeal_coefficient_map_laurentEval J f v).trans h) u

/-- The whole Laurent evaluation map has the exact composition formula with
every entire original Laurent-family map, including action and projection. -/
theorem nativeClosedLaurentEvaluationMap_comp_family
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : R →+* S)
    (h : J.map (coefficientGradedMap f) = K) (v u : Sˣ) (w : R[T;T⁻¹]ˣ) :
    nativeClosedLaurentEvaluationMap J K f h v u ≫
        nativeClosedParameterFamilyMap J LaurentPolynomial.C w =
      nativeClosedParameterMapOfIdealMap J K f h
        (u * Units.map (LaurentPolynomial.eval₂ f v).toMonoidHom w) := by
  apply (cancel_mono (nativeConstantIdeal J).subschemeι).mp
  rw [Category.assoc, nativeClosedParameterFamilyMap_ι, ← Category.assoc]
  change (nativeClosedParameterMapOfIdealMap _ _ _ _ u ≫ _) ≫ _ = _
  rw [nativeClosedParameterMapOfIdealMap_ι, Category.assoc,
    ← nativeParameterFamilyMap_comp, nativeClosedParameterMapOfIdealMap_ι]
  have hc : (LaurentPolynomial.eval₂ f v).comp LaurentPolynomial.C = f := by
    ext r
    exact LaurentPolynomial.eval₂_C f v r
  rw [hc]

/-- The actual unit section from the original whole closed family into its
entire Laurent product, constructed through true Laurent evaluation. -/
def nativeClosedLaurentUnitSection (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    (nativeConstantIdeal J).subscheme ⟶
      (nativeConstantIdeal (J.map (coefficientGradedMap LaurentPolynomial.C))).subscheme :=
  nativeClosedLaurentEvaluationMap J J (RingHom.id R)
    (homogeneousIdeal_coefficient_map_id J) 1 1

/-- The whole unit section composes with the actual product projection to identity. -/
theorem nativeClosedLaurentUnitSection_projection
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    nativeClosedLaurentUnitSection J ≫ nativeClosedParameterFamilyMap J LaurentPolynomial.C 1 =
      𝟙 _ := by
  rw [nativeClosedLaurentUnitSection, nativeClosedLaurentEvaluationMap_comp_family]
  simp only [map_one, one_mul, nativeClosedParameterMapOfIdealMap_id]

/-- The entire universal action at the actual unit section is identity. -/
theorem nativeClosedLaurentUnitSection_action
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    nativeClosedLaurentUnitSection J ≫
        nativeClosedParameterFamilyMap J LaurentPolynomial.C (parameterLaurentUnit R) = 𝟙 _ := by
  rw [nativeClosedLaurentUnitSection, nativeClosedLaurentEvaluationMap_comp_family,
    parameterLaurentUnit_map_eval, one_mul, nativeClosedParameterMapOfIdealMap_id]

end ProjBerk
end EnvelopeProperty
