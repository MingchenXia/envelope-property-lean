/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealActionLaws

/-!
# Actual whole Laurent action diagrams on the original ideal blowup

The universal Laurent family has whole unit, naturality and multiplication
diagrams on the constructed blowup. Actual Laurent evaluation maps and genuine
blowup uniqueness supply them, before normalization or line-bundle positivity.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ}
variable (J : HomogeneousIdeal (ProjectiveGrading k n))
variable (I L : HomogeneousIdeal (ProjectiveGrading k[X] n))
variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hL : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

private local instance familyProjectionFlat {S : Type u} [CommRing S] (f : k →+* S) :
    Flat (nativeClosedParameterFamilyMap J f 1) :=
  nativeClosedParameterFamilyProjection_flat J f

/-- The actual family map of the genuine original blowup, constructed from
the proved whole coefficient-unit ideal equalities. -/
def nativeClosedProductIdealFamilyLift {S : Type u} [CommRing S] (f : k →+* S) (u : Sˣ) :
    pullback (nativeClosedProductIdeal J I L).blowUpπ (nativeClosedParameterFamilyMap J f 1) ⟶
      (nativeClosedProductIdeal J I L).blowUp :=
  (nativeClosedProductIdeal J I L).parameterFamilyLift _ _
    (nativeClosedProductIdeal_family_invariant J I L f u (hI S f u) (hL S f u))

/-- The true original projection triangle of the whole constructed family lift. -/
@[reassoc]
theorem nativeClosedProductIdealFamilyLift_π {S : Type u} [CommRing S] (f : k →+* S) (u : Sˣ) :
    nativeClosedProductIdealFamilyLift J I L hI hL f u ≫ (nativeClosedProductIdeal J I L).blowUpπ =
      pullback.snd _ _ ≫ nativeClosedParameterFamilyMap J f u :=
  (nativeClosedProductIdeal J I L).parameterFamilyLift_π _ _ _

/-- The genuine unit action diagram on the whole constructed blowup. -/
theorem nativeClosedProductIdealFamilyLift_unit :
    (nativeClosedProductIdeal J I L).parameterFamilyUnitSection
        (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1)
        (nativeClosedLaurentUnitSection J) (nativeClosedLaurentUnitSection_projection J) ≫
      nativeClosedProductIdealFamilyLift J I L hI hL LaurentPolynomial.C (parameterLaurentUnit k) =
        𝟙 _ :=
  (nativeClosedProductIdeal J I L).parameterFamilyLift_unit _ _ _ _
    (nativeClosedLaurentUnitSection_projection J) (nativeClosedLaurentUnitSection_action J)

/-- Every actual coefficient-extended unit family is the whole true pullback
of the same single universal Laurent action. -/
theorem nativeClosedProductIdealFamilyLift_naturality {S : Type u} [CommRing S]
    (f : k →+* S) (u : Sˣ) :
    (nativeClosedProductIdeal J I L).parameterFamilyBaseChangeMap
        (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1)
        (nativeClosedParameterFamilyMap J f 1)
        (nativeClosedLaurentEvaluationMap J (J.map (coefficientGradedMap f)) f rfl u 1)
        (by rw [nativeClosedLaurentEvaluationMap_comp_family, map_one, one_mul,
          nativeClosedParameterMapOfIdealMap_eq_family]) ≫
      nativeClosedProductIdealFamilyLift J I L hI hL LaurentPolynomial.C (parameterLaurentUnit k) =
        nativeClosedProductIdealFamilyLift J I L hI hL f u := by
  apply (nativeClosedProductIdeal J I L).parameterFamilyLift_naturality
  rw [nativeClosedLaurentEvaluationMap_comp_family, parameterLaurentUnit_map_eval, one_mul,
    nativeClosedParameterMapOfIdealMap_eq_family]

/-- The entire sequential lifted action is the single product action. Choosing
the two independent Laurent units gives the universal whole action diagram. -/
theorem nativeClosedProductIdealFamilyLift_multiplication {S : Type u} [CommRing S]
    (f : k →+* S) (u v : Sˣ) :
    (nativeClosedProductIdeal J I L).parameterFamilyThenMap
        (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1)
        (nativeClosedParameterFamilyMap J f 1) (nativeClosedParameterFamilyMap J f u)
        (nativeClosedProductIdeal_family_invariant J I L f u (hI S f u) (hL S f u))
        (nativeClosedLaurentEvaluationMap J (J.map (coefficientGradedMap f)) f rfl v u)
        (by rw [nativeClosedLaurentEvaluationMap_comp_family, map_one, mul_one,
          nativeClosedParameterMapOfIdealMap_eq_family]) ≫
      nativeClosedProductIdealFamilyLift J I L hI hL LaurentPolynomial.C (parameterLaurentUnit k) =
        nativeClosedProductIdealFamilyLift J I L hI hL f (u * v) := by
  apply (nativeClosedProductIdeal J I L).parameterFamilyLift_composition
  rw [nativeClosedLaurentEvaluationMap_comp_family, parameterLaurentUnit_map_eval,
    nativeClosedParameterMapOfIdealMap_eq_family]

end EnvelopeProperty.ProjBerk
