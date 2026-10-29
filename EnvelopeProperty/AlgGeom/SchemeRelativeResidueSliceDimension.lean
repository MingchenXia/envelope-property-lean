import EnvelopeProperty.AlgGeom.SchemeRelativeResidueSliceFinite
import EnvelopeProperty.AlgGeom.SchemePolynomialTraitClosure
import EnvelopeProperty.Algebra.RelativeResidueTranscendenceDegree

/-! # True actual coefficient-slice center residue dimension -/
open AlgebraicGeometry CategoryTheory IsLocalRing Cardinal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeRelativeResidueSliceDimension
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [Algebra k X.functionField] (V : Subalgebra k X.functionField)
  [IsFractionRing V X.functionField]
  (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
  (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)

/-- The ACTUAL original coefficient base map of the SAME native coefficient slice. -/
def coefficientBaseMap : SchemePolynomialCoefficientSlice.model V f q t hq E hEV ⟶ Spec (.of E) :=
  SchemePolynomialTraitClosure.coefficientBaseMap
    (SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV)

/-- The entire original lifted trait preserves the SAME literal coefficient inclusion. -/
theorem centerLift_coefficientBaseMap :
    SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV ≫
      coefficientBaseMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (SchemePolynomialCoefficientSlice.coefficientMap V E hEV)) := by
  dsimp only [coefficientBaseMap,SchemePolynomialTraitClosure.coefficientBaseMap]
  rw [← Category.assoc,SchemePolynomialCoefficientSlice.centerLift_structure,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change Polynomial.eval₂ (SchemePolynomialCoefficientSlice.coefficientMap V E hEV) t
    (Polynomial.C c) = SchemePolynomialCoefficientSlice.coefficientMap V E hEV c
  exact Polynomial.eval₂_C _ _

omit E hEV in
/-- The actual slice center retains EXACTLY the original center's residue
transcendence degree after removing the genuine relative coefficient basis. -/
theorem centerResidue_trdeg [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V]
    {ι : Type u} [Finite ι] (u : ι → V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      letI := (SchemeLocalResidueCoefficients.residueAlgHom
        (SchemeRelativeResidueSliceFinite.originalBaseMap f) q
        (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)).toAlgebra;
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
    (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V) :
    let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
    let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
    letI := SchemePointClosureCurve.residueAlgebra z (coefficientBaseMap V f q t hq E hEV)
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
    Algebra.trdeg E ((SchemePolynomialCoefficientSlice.model V f q t hq E hEV).residueField z) =
      Algebra.trdeg k (X.residueField (q (closedPoint V))) := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
  let Y := SchemePolynomialCoefficientSlice.model V f q t hq E hEV
  let ℓ := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV
  let z := ℓ (closedPoint V)
  let b := coefficientBaseMap V f q t hq E hEV
  let bX := SchemeRelativeResidueSliceFinite.originalBaseMap f
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) bX
  let α := SchemeLocalResidueCoefficients.residueAlgHom bX q
    (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)
  let := α.toAlgebra
  let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun c => (α.commutes c).symm
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  have hn : Algebra.trdeg E (ResidueField V) = Algebra.trdeg k (X.residueField (q (closedPoint V))) := by
    exact RelativeResidueTranscendenceDegree.trdeg_relativeResidue V
      (X.residueField (q (closedPoint V))) u hu
  let := SchemePointClosureCurve.residueAlgebra z b
  let γ : Y.residueField z →ₐ[E] ResidueField V :=
    SchemeLocalResidueCoefficients.residueAlgHom b ℓ
      (centerLift_coefficientBaseMap V f q t hq E hEV)
  let := γ.toAlgebra
  let : FiniteDimensional (Y.residueField z) (ResidueField V) :=
    SchemeRelativeResidueSliceFinite.finite_centerResidue_of_basis V f q t hq u hu hEV
  let : IsScalarTower E (Y.residueField z) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun c => (γ.commutes c).symm
  let : FaithfulSMul (Y.residueField z) (ResidueField V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 γ.injective
  have h := trdeg_add_eq E (Y.residueField z) (A := ResidueField V)
  rw [trdeg_eq_zero (R := Y.residueField z),add_zero] at h
  exact h.trans hn

/-- The actual original trait center closure on the SAME coefficient slice
is genuinely proper over the actual coefficient field. -/
theorem closure_isProper [IsLocalRing V] [IsProper f] (ht : t ∈ maximalIdeal V) :
    IsProper (SchemePointClosureCurve.structureMap
      (SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V))
      (coefficientBaseMap V f q t hq E hEV)) := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  let : IsProper (SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV) :=
    SchemePolynomialCoefficientSlice.structureMap_isProper V f q t hq E hEV
  apply SchemePolynomialTraitClosure.closure_isProper
    (SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV)
    (SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV) t
  · exact SchemePolynomialCoefficientSlice.centerLift_structure V f q t hq E hEV
  · exact ht

omit E hEV in
/-- The SAME actual native center closure has true whole dimension d,
derived from the ORIGINAL center's native residue transcendence degree. -/
theorem closure_dimension_eq [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] [IsProper f]
    {ι : Type u} [Finite ι] (u : ι → V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      letI := (SchemeLocalResidueCoefficients.residueAlgHom
        (SchemeRelativeResidueSliceFinite.originalBaseMap f) q
        (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)).toAlgebra;
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
    (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V)
    (d : ℕ) (hL : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      Algebra.trdeg k (X.residueField (q (closedPoint V))) = d) :
    let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
    let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
    topologicalKrullDim (SchemePointClosureCurve.closure z) = d := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
  let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
  let b := coefficientBaseMap V f q t hq E hEV
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V))
    (SchemeRelativeResidueSliceFinite.originalBaseMap f)
  let : IsProper (SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV) :=
    SchemePolynomialCoefficientSlice.structureMap_isProper V f q t hq E hEV
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) :=
    HasRingHomProperty.Spec_iff.mpr (by
      change RingHom.FiniteType (algebraMap E (Polynomial E))
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType b := by
    dsimp only [b,coefficientBaseMap,SchemePolynomialTraitClosure.coefficientBaseMap]
    infer_instance
  apply SchemePointClosureCurve.dimension_eq z b d
  exact (centerResidue_trdeg V f q t hq u hu hEV).trans hL

end EnvelopeProperty.SchemeRelativeResidueSliceDimension
