import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceNormalization
import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceParameterCurve
import EnvelopeProperty.AlgGeom.SchemeDominantPointNormalization
import EnvelopeProperty.AlgGeom.SchemeGenericFieldCoefficients

/-! # The SAME original K and EVERY coefficient in the actual normalized coefficient slice -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceNormalizedField
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)
local notation "Y" => SchemePolynomialCoefficientSlice.model V f q t hq E hEV
local notation "N" => SchemeCoefficientSliceNormalization.model V f q t hq E hEV
local notation "gS" => SchemePolynomialCoefficientSlice.genericPointMap V f q t hq E hEV
private local instance slice_integral : IsIntegral Y :=
  SchemePolynomialCoefficientSlice.model_isIntegral V f q t hq E hEV
private local instance normalized_integral : IsIntegral N :=
  SchemeCoefficientSliceNormalization.model_isIntegral V f q t hq E hEV
private local instance slice_point_dominant : IsDominant gS :=
  SchemePolynomialCoefficientSlice.genericPointMap_isDominant V f q t hq E hEV

/-- The SAME original SpecK point in the actual normalized original coefficient slice. -/
def genericPointMap : Spec X.functionField ⟶ N := SchemeDominantPointNormalization.lift gS

/-- The SAME actual original generic-field lift is genuinely dominant. -/
theorem genericPointMap_isDominant : IsDominant (genericPointMap V f q t hq E hEV) :=
  SchemeDominantPointNormalization.lift_isDominant gS

/-- The normalized original generic point retains its WHOLE original model projection. -/
theorem genericPointMap_projection : genericPointMap V f q t hq E hEV ≫
    SchemeCoefficientSliceNormalization.projection V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q := by
  dsimp only [genericPointMap,SchemeCoefficientSliceNormalization.projection]
  rw [← Category.assoc,SchemeDominantPointNormalization.lift_projection]
  exact SchemePolynomialCoefficientSlice.genericPointMap_projection V f q t hq E hEV

/-- EVERY original E-polynomial and SAME original parameter retain their whole field point. -/
theorem genericPointMap_structure : genericPointMap V f q t hq E hEV ≫
    SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := E) (t : X.functionField)).toRingHom) := by
  dsimp only [genericPointMap,SchemeCoefficientSliceNormalization.structureMap]
  rw [← Category.assoc,SchemeDominantPointNormalization.lift_projection]
  exact SchemeCoefficientSliceParameterCurve.genericPointMap_structure V f q t hq E hEV

/-- The SAME actual original E coefficient structure of the normalized slice. -/
def coefficientBaseMap : N ⟶ Spec (.of E) :=
  SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))

/-- The WHOLE actual original E coefficient square is retained in unchanged K. -/
theorem genericPointMap_coefficientBaseMap : genericPointMap V f q t hq E hEV ≫
    coefficientBaseMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (algebraMap E X.functionField)) := by
  rw [coefficientBaseMap,← Category.assoc,genericPointMap_structure,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact Polynomial.aeval_C _ _

/-- The SAME actual native normalized coefficient-slice function field is unchanged original K, as actual E-algebra. -/
def functionFieldAlgEquiv
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
      X.fromSpecStalk (genericPoint X)) :
    letI := (coefficientBaseMap V f q t hq E hEV).stalkAlgebra (genericPoint N)
    (N).functionField ≃ₐ[E] X.functionField := by
  let := genericPointMap_isDominant V f q t hq E hEV
  exact SchemeGenericFieldCoefficients.functionFieldAlgEquiv
    (genericPointMap V f q t hq E hEV)
    (SchemeCoefficientSliceNormalization.projection V f q t hq E hEV)
    ((genericPointMap_projection V f q t hq E hEV).trans hgen)
    (coefficientBaseMap V f q t hq E hEV)
    (genericPointMap_coefficientBaseMap V f q t hq E hEV)

end EnvelopeProperty.SchemeCoefficientSliceNormalizedField
