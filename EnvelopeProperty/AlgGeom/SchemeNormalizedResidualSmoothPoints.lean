import EnvelopeProperty.AlgGeom.SchemeNormalizedCenterSmooth
import EnvelopeProperty.AlgGeom.SchemeNormalizedCenterResidueCurve
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps

/-! # Actual dense common-smooth closed residual points on the SAME original normalized model -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeNormalizedResidualSmoothPoints
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
private local instance structure_proper :
    IsProper (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) :=
  SchemeCoefficientSliceNormalization.structure_isProper V f q t hq E hEV
private local instance polynomialCoefficients_finiteType :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) :=
  HasRingHomProperty.Spec_iff.mpr (by
    change RingHom.FiniteType (algebraMap E (Polynomial E))
    exact RingHom.finiteType_algebraMap.mpr inferInstance)
private local instance coefficientBaseMap_finiteType : LocallyOfFiniteType bN := by
  dsimp only [SchemeCoefficientSliceNormalizedField.coefficientBaseMap]
  infer_instance


local notation "C" => SchemePointClosureCurve.closure c
local notation "bC" => SchemePointClosureCurve.structureMap c bN
private local instance closure_integral : IsIntegral C := SchemePointClosureCurve.closure_isIntegral c
private local instance closure_inclusion_closed : IsClosedImmersion (SchemePointClosureCurve.inclusion c) := by
  dsimp only [SchemePointClosureCurve.inclusion]
  infer_instance
private local instance closure_structure_finiteType : LocallyOfFiniteType bC := by
  dsimp only [SchemePointClosureCurve.structureMap]
  infer_instance

include hgen hu hL in
/-- EVERY actual nonempty residual open contains a genuine original closed point
where both the actual residual curve and its actual ambient E-surface are smooth. -/
theorem exists_commonSmooth_closedPoint [CharZero k]
    (W : (C).Opens) (hW : (W : Set C).Nonempty) :
    ∃ z : C, z ∈ W ∧ IsClosed ({z} : Set C) ∧
      SchemePointClosureCurve.inclusion c z ∈ (bN).smoothLocus ∧
      z ∈ (bC).smoothLocus ∧
      IsClosed ({SchemePointClosureCurve.inclusion c z} : Set N) ∧
      (letI := SchemePointClosureCurve.residueAlgebra z bC; Module.Finite E ((C).residueField z)) := by
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace bC
  have hgeneric : SchemePointClosureCurve.inclusion c (genericPoint C) = c := by
    let g := SchemePointClosureCurve.genericMap c
    let : QuasiCompact ((N).fromSpecResidueField c) :=
      ⟨fun U _ _ => (Set.toFinite (((N).fromSpecResidueField c) ⁻¹' U)).isCompact⟩
    let : IsDominant g := by
      dsimp only [g,SchemePointClosureCurve.genericMap]
      infer_instance
    have hg : g (closedPoint ((N).residueField c)) = genericPoint C := by
      rw [show closedPoint ((N).residueField c) = genericPoint (Spec ((N).residueField c)) from
        Subsingleton.elim _ _]
      exact DominantFunctionFieldMaps.genericPoint_map g
    have hi := congrArg (fun a : Spec ((N).residueField c) ⟶ N =>
      a (closedPoint ((N).residueField c))) (SchemePointClosureCurve.genericMap_inclusion c)
    change SchemePointClosureCurve.inclusion c (g (closedPoint ((N).residueField c))) =
      (N).fromSpecResidueField c (closedPoint ((N).residueField c)) at hi
    rwa [hg,Scheme.fromSpecResidueField_apply] at hi
  let S := W ⊓ (SchemePointClosureCurve.inclusion c) ⁻¹ᵁ (bN).smoothLocus ⊓ (bC).smoothLocus
  have hS : genericPoint C ∈ S := by
    refine ⟨⟨((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr (by simpa only [Set.univ_inter] using hW),?_⟩,?_⟩
    · change SchemePointClosureCurve.inclusion c (genericPoint C) ∈ (bN).smoothLocus
      rw [hgeneric]
      exact SchemeNormalizedCenterSmooth.center_mem_smoothLocus V f q t hq hgen u hu hEV hL
    · exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField bC
  obtain ⟨z,hzS,hzc⟩ := nonempty_inter_closedPoints
    (show (S : Set C).Nonempty from ⟨genericPoint C,hS⟩) S.isOpen.isLocallyClosed
  have hzclosed : IsClosed ({z} : Set C) := hzc
  refine ⟨z,hzS.1.1,hzclosed,hzS.1.2,hzS.2,?_,?_⟩
  · simpa only [Set.image_singleton] using
      (SchemePointClosureCurve.inclusion c).isClosedEmbedding.isClosedMap ({z} : Set C) hzclosed
  · exact SchemeSurfaceResidueDVR.closedPoint_residue_finite bC z hzclosed

end EnvelopeProperty.SchemeNormalizedResidualSmoothPoints
