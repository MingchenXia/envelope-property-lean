import EnvelopeProperty.AlgGeom.SchemeDVRNormalizationLift
import EnvelopeProperty.AlgGeom.SchemePolynomialCoefficientSlice
import EnvelopeProperty.AlgGeom.FiniteSchemeNormalization
import EnvelopeProperty.AlgGeom.NormalSchemeNormalization

/-! # SAME original coefficient-slice finite normalization and WHOLE original DVR trait -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceNormalization
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]
    (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)
local notation "Y" => SchemePolynomialCoefficientSlice.model V f q t hq E hEV
local notation "ℓ" => SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV
local notation "fS" => SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV

private local instance slice_integral : IsIntegral Y :=
  SchemePolynomialCoefficientSlice.model_isIntegral V f q t hq E hEV

omit [IsDiscreteValuationRing V] in
private theorem fraction_centerLift :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ =
      SchemePolynomialCoefficientSlice.genericPointMap V f q t hq E hEV :=
  SchemeDVRBaseChangeImage.fraction_centerLift f (Polynomial.mapRingHom (algebraMap k E)) q
    (SchemePolynomialCoefficientSlice.polynomialMap V t E hEV)
    (by rw [SchemePolynomialCoefficientSlice.polynomialMap_comp]; exact hq)

private local instance trait_dominant : IsDominant ℓ := by
  let := SchemePolynomialCoefficientSlice.genericPointMap_isDominant V f q t hq E hEV
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ) := by
    rw [fraction_centerLift]
    infer_instance
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) ℓ

/-- The actual ORIGINAL coefficient-slice normalization in its unchanged native function field. -/
def model : Scheme.{u} := IntegralSchemeNormalization.normalization Y

/-- Its actual WHOLE original model projection. -/
def projection : model V f q t hq E hEV ⟶ X :=
  IntegralSchemeNormalization.projection Y ≫
    SchemePolynomialCoefficientSlice.projection V f q t hq E hEV

/-- Its actual SAME original E-polynomial structure. -/
def structureMap : model V f q t hq E hEV ⟶ Spec (.of (Polynomial E)) :=
  IntegralSchemeNormalization.projection Y ≫ fS

/-- SAME original DVR trait genuinely lifts to the actual coefficient-slice normalization. -/
def centerLift : Spec (.of V) ⟶ model V f q t hq E hEV :=
  SchemeDVRNormalizationLift.lift ℓ

/-- The WHOLE original trait model square is retained EXACTLY. -/
theorem centerLift_projection : centerLift V f q t hq E hEV ≫ projection V f q t hq E hEV = q := by
  dsimp only [centerLift,projection]
  rw [← Category.assoc,SchemeDVRNormalizationLift.lift_projection]
  exact SchemePolynomialCoefficientSlice.centerLift_projection V f q t hq E hEV

/-- EVERY original polynomial coefficient and SAME parameter retain the WHOLE trait square. -/
theorem centerLift_structure : centerLift V f q t hq E hEV ≫ structureMap V f q t hq E hEV =
    Spec.map (CommRingCat.ofHom (SchemePolynomialCoefficientSlice.polynomialMap V t E hEV)) := by
  dsimp only [centerLift,structureMap]
  rw [← Category.assoc,SchemeDVRNormalizationLift.lift_projection]
  exact SchemePolynomialCoefficientSlice.centerLift_structure V f q t hq E hEV

omit [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
/-- The actual original coefficient-slice normalization is genuinely integral. -/
theorem model_isIntegral : IsIntegral (model V f q t hq E hEV) := by
  dsimp only [model]
  infer_instance

omit [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
/-- EVERY actual original normalized coefficient-slice stalk is genuinely integrally closed. -/
theorem stalk_isIntegrallyClosed (z : model V f q t hq E hEV) :
    IsIntegrallyClosed ((model V f q t hq E hEV).presheaf.stalk z) :=
  IntegralSchemeNormalization.stalk_isIntegrallyClosed Y z

omit [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
/-- The SAME original coefficient-slice normalization projection is FINITE, internally from actual field geometry. -/
theorem normalizationProjection_isFinite [IsProper f] :
    IsFinite (IntegralSchemeNormalization.projection Y) := by
  let : IsProper fS := SchemePolynomialCoefficientSlice.structureMap_isProper V f q t hq E hEV
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) :=
    HasRingHomProperty.Spec_iff.mpr (by
      change RingHom.FiniteType (algebraMap E (Polynomial E))
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  exact IntegralSchemeNormalization.projection_isFinite E Y
    (fS ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E)))

omit [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
/-- The SAME actual normalized coefficient slice remains proper over ORIGINAL E[t]. -/
theorem structure_isProper [IsProper f] : IsProper (structureMap V f q t hq E hEV) := by
  let := normalizationProjection_isFinite V f q t hq E hEV
  let : IsProper fS := SchemePolynomialCoefficientSlice.structureMap_isProper V f q t hq E hEV
  dsimp only [structureMap]
  infer_instance

end EnvelopeProperty.SchemeCoefficientSliceNormalization
