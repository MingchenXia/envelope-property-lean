import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceOriginalCenter

/-! # The SAME actual original residue field and proper native residual center curve -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeNormalizedCenterResidueCurve
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]
    (f : X ⟶ Spec (.of (Polynomial k))) [IsProper f]
    (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    [Algebra.EssFiniteType k V]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
      X.fromSpecStalk (genericPoint X))
    {ι : Type u} [Finite ι] (u : ι → V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      letI := (SchemeLocalResidueCoefficients.residueAlgHom
        (SchemeRelativeResidueSliceFinite.originalBaseMap f) q
        (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)).toAlgebra;
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
    (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V)
    (hL : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      Algebra.trdeg k (X.residueField (q (closedPoint V))) = 1)
local notation "E" => IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
local notation "N" => SchemeCoefficientSliceNormalization.model V f q t hq E hEV
local notation "ℓ" => SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV
local notation "c" => ℓ (closedPoint V)
private local instance normalized_integral : IsIntegral N :=
  SchemeCoefficientSliceNormalization.model_isIntegral V f q t hq E hEV


local notation "bN" => SchemeCoefficientSliceNormalizedField.coefficientBaseMap V f q t hq E hEV
local notation "C" => SchemePointClosureCurve.closure c

/-- The SAME original native normalized-center residue field is the unchanged κV,
as actual coefficient algebra and via the original canonical stalk quotient. -/
def residueAlgEquiv :
    letI := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
    letI := SchemePointClosureCurve.residueAlgebra c bN
    (N).residueField c ≃ₐ[E] ResidueField V := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  let := (bN).stalkAlgebra c
  let := SchemePointClosureCurve.residueAlgebra c bN
  let φ := SchemeLocalResidueCoefficients.stalkClosedPointToAlgHom bN ℓ
    (SchemeCoefficientSliceNormalizedDVR.centerLift_coefficientBaseMap V f q t hq E hEV)
  let e : (N).presheaf.stalk c ≃ₐ[E] V := AlgEquiv.ofBijective φ
    (SchemeCoefficientSliceOriginalCenter.stalkMap_bijective V f q t hq hgen u hu hEV hL)
  exact ResidueField.mapAlgEquiv e

/-- EVERY actual native residue retains its exact original residue value. -/
theorem residueAlgEquiv_residue (a : (N).presheaf.stalk c) :
    letI := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
    letI := SchemePointClosureCurve.residueAlgebra c bN
    residueAlgEquiv V f q t hq hgen u hu hEV hL ((N).residue c a) =
      residue V ((Scheme.stalkClosedPointTo ℓ) a) := rfl

/-- The actual native center-closure function field is unchanged original κV,
with EVERY original E coefficient retained. -/
def functionFieldAlgEquiv :
    letI := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
    letI := SchemePointClosureCurve.closure_isIntegral c
    letI := (SchemePointClosureCurve.structureMap c bN).stalkAlgebra (genericPoint C)
    (C).functionField ≃ₐ[E] ResidueField V := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  let := SchemePointClosureCurve.closure_isIntegral c
  let := (bN).stalkAlgebra c
  let := SchemePointClosureCurve.residueAlgebra c bN
  let := (SchemePointClosureCurve.structureMap c bN).stalkAlgebra (genericPoint C)
  exact (SchemePointClosureCurve.functionFieldAlgEquiv c bN).trans
    (residueAlgEquiv V f q t hq hgen u hu hEV hL)

omit [Algebra.EssFiniteType k V] [Finite ι] in
/-- The SAME actual residual center closure on the original normalized model
is genuinely proper over its unchanged coefficient field. -/
theorem closure_isProper (ht : t ∈ maximalIdeal V) :
    IsProper (SchemePointClosureCurve.structureMap c bN) := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  let : IsProper (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) :=
    SchemeCoefficientSliceNormalization.structure_isProper V f q t hq E hEV
  apply SchemePolynomialTraitClosure.closure_isProper
    (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) ℓ t
  · exact SchemeCoefficientSliceNormalization.centerLift_structure V f q t hq E hEV
  · exact ht

include hgen hu hL in
/-- The SAME actual original normalized-model residual center closure is
one-dimensional, internally from the actual original residue degree. -/
theorem closure_dimension_eq_one : topologicalKrullDim C = 1 := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  let : IsProper (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) :=
    SchemeCoefficientSliceNormalization.structure_isProper V f q t hq E hEV
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) :=
    HasRingHomProperty.Spec_iff.mpr (by
      change RingHom.FiniteType (algebraMap E (Polynomial E))
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType bN := by
    dsimp only [SchemeCoefficientSliceNormalizedField.coefficientBaseMap]
    infer_instance
  let := SchemePointClosureCurve.residueAlgebra c bN
  apply SchemePointClosureCurve.dimension_eq c bN 1
  apply (residueAlgEquiv V f q t hq hgen u hu hEV hL).trdeg_eq.trans
  let bX := SchemeRelativeResidueSliceFinite.originalBaseMap f
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) bX
  let α := SchemeLocalResidueCoefficients.residueAlgHom bX q
    (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)
  let := α.toAlgebra
  let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun a => (α.commutes a).symm
  exact (RelativeResidueTranscendenceDegree.trdeg_relativeResidue V
    (X.residueField (q (closedPoint V))) u hu).trans hL

end EnvelopeProperty.SchemeNormalizedCenterResidueCurve
