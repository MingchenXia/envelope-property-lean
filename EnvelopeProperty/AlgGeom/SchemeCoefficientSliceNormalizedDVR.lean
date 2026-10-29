import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceNormalizedTrait
import EnvelopeProperty.AlgGeom.SchemeTraitCenterTranscendence
import EnvelopeProperty.AlgGeom.SchemeRelativeResidueSliceDimension
import EnvelopeProperty.AlgGeom.SchemeSurfaceResidueDVR

/-! # The actual original center stalk on the normalized coefficient slice is a DVR -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceNormalizedDVR
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]
    (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)

/-- EVERY original coefficient survives the WHOLE actual normalized-trait square. -/
theorem centerLift_coefficientBaseMap :
    SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV ≫
      SchemeCoefficientSliceNormalizedField.coefficientBaseMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (SchemePolynomialCoefficientSlice.coefficientMap V E hEV)) := by
  rw [SchemeCoefficientSliceNormalizedField.coefficientBaseMap,← Category.assoc,
    SchemeCoefficientSliceNormalization.centerLift_structure,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Polynomial.eval₂_C _ _

omit E hEV in
/-- The SAME actual native normalization-center stalk is a DVR, internally
from the original finite residue basis and unchanged native fraction-field triangle. -/
theorem center_stalk_isDiscreteValuationRing [Algebra.EssFiniteType k V] [IsProper f]
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
      Algebra.trdeg k (X.residueField (q (closedPoint V))) = 1) :
    let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
    let N := SchemeCoefficientSliceNormalization.model V f q t hq E hEV
    let c := SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV (closedPoint V)
    letI := SchemeCoefficientSliceNormalization.model_isIntegral V f q t hq E hEV
    IsDiscreteValuationRing (N.presheaf.stalk c) := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
  let Y := SchemePolynomialCoefficientSlice.model V f q t hq E hEV
  let N := SchemeCoefficientSliceNormalization.model V f q t hq E hEV
  let ℓ := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV
  let ℓN := SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV
  let bY := SchemeRelativeResidueSliceDimension.coefficientBaseMap V f q t hq E hEV
  let bN := SchemeCoefficientSliceNormalizedField.coefficientBaseMap V f q t hq E hEV
  let c := ℓN (closedPoint V)
  let := SchemePolynomialCoefficientSlice.model_isIntegral V f q t hq E hEV
  let := SchemeCoefficientSliceNormalization.model_isIntegral V f q t hq E hEV
  let ν := IntegralSchemeNormalization.projection Y
  let : IsProper (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) :=
    SchemeCoefficientSliceNormalization.structure_isProper V f q t hq E hEV
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) :=
    HasRingHomProperty.Spec_iff.mpr (by
      change RingHom.FiniteType (algebraMap E (Polynomial E))
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType bN := by
    dsimp only [bN,SchemeCoefficientSliceNormalizedField.coefficientBaseMap]
    infer_instance
  let := SchemeCoefficientSliceNormalization.stalk_isIntegrallyClosed V f q t hq E hEV c
  have hfield : letI := bN.stalkAlgebra (genericPoint N); Algebra.trdeg E N.functionField = 2 := by
    let := bN.stalkAlgebra (genericPoint N)
    apply (SchemeCoefficientSliceNormalizedField.functionFieldAlgEquiv V f q t hq E hEV hgen).trdeg_eq.trans
    let bX := SchemeRelativeResidueSliceFinite.originalBaseMap f
    let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) bX
    let α := SchemeLocalResidueCoefficients.residueAlgHom bX q
      (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)
    let := α.toAlgebra
    let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
      IsScalarTower.of_algebraMap_eq fun a => (α.commutes a).symm
    exact SchemeCoefficientSliceParameterCurve.functionField_trdeg_two V
      (X.residueField (q (closedPoint V))) hL u hu
  let g := SchemePolynomialCoefficientSlice.genericPointMap V f q t hq E hEV
  let : IsDominant g := SchemePolynomialCoefficientSlice.genericPointMap_isDominant V f q t hq E hEV
  have hfraction : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ = g :=
    SchemeDVRBaseChangeImage.fraction_centerLift f (Polynomial.mapRingHom (algebraMap k E)) q
      (SchemePolynomialCoefficientSlice.polynomialMap V t E hEV)
      (by rw [SchemePolynomialCoefficientSlice.polynomialMap_comp]; exact hq)
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ) := by
    rw [hfraction]
    infer_instance
  let : IsDominant ℓ := IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) ℓ
  have hproj : ℓN ≫ ν = ℓ := SchemeDVRNormalizationLift.lift_projection ℓ
  have hb : bN = ν ≫ bY := by
    dsimp only [bN,bY,SchemeCoefficientSliceNormalizedField.coefficientBaseMap,
      SchemeCoefficientSliceNormalization.structureMap,
      SchemeRelativeResidueSliceDimension.coefficientBaseMap,
      SchemePolynomialTraitClosure.coefficientBaseMap]
    rw [Category.assoc]
  have hcenter : ν c = ℓ (closedPoint V) :=
    congrArg (fun a : Spec (.of V) ⟶ Y => a (closedPoint V)) hproj
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  have hresidue : letI := SchemePointClosureCurve.residueAlgebra c bN;
      Algebra.trdeg E (N.residueField c) = 1 := by
    rw [hb]
    change letI := SchemePointClosureCurve.residueAlgebra (ℓN (closedPoint V)) (ν ≫ bY);
      Algebra.trdeg E (N.residueField (ℓN (closedPoint V))) = 1
    apply SchemeTraitCenterTranscendence.trdeg_eq ν bY ℓN
      (by rw [hproj]; exact SchemeRelativeResidueSliceDimension.centerLift_coefficientBaseMap V f q t hq E hEV) 1
    · have hZ := SchemeRelativeResidueSliceDimension.centerResidue_trdeg V f q t hq u hu hEV
      change letI := SchemePointClosureCurve.residueAlgebra (ν c) bY;
        Algebra.trdeg E (Y.residueField (ν c)) = 1
      rw [hcenter]
      exact hZ.trans hL
    · let bX := SchemeRelativeResidueSliceFinite.originalBaseMap f
      let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) bX
      let α := SchemeLocalResidueCoefficients.residueAlgHom bX q
        (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)
      let := α.toAlgebra
      let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
        IsScalarTower.of_algebraMap_eq fun a => (α.commutes a).symm
      exact (RelativeResidueTranscendenceDegree.trdeg_relativeResidue V
        (X.residueField (q (closedPoint V))) u hu).trans hL
  exact SchemeSurfaceResidueDVR.stalk_isDiscreteValuationRing bN c hfield hresidue

end EnvelopeProperty.SchemeCoefficientSliceNormalizedDVR
