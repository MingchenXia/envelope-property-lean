import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceNormalizedDVR
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-! # Actual ambient smooth neighborhoods of the SAME original normalized center -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeNormalizedCenterSmooth
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

include hgen hu hL in
/-- The SAME actual original center is smooth for the ambient coefficient
surface over E in characteristic zero, without assuming a smooth parameter fibre. -/
theorem center_mem_smoothLocus [CharZero k] : c ∈ (bN).smoothLocus := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk c) :=
    SchemeCoefficientSliceNormalizedDVR.center_stalk_isDiscreteValuationRing V f q t hq hgen u hu hEV hL
  apply (Scheme.mem_smoothLocus_iff_isRegularAt bN c).mpr
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing ((N).presheaf.stalk c)

include hgen hu hL in
/-- An actual affine original neighborhood of the SAME center has genuinely
smooth E-structure, preserving the original model and all parameter multiplicities. -/
theorem exists_smooth_affine [CharZero k] :
    ∃ U : (N).Opens, IsAffineOpen U ∧ c ∈ U ∧ Smooth (U.ι ≫ bN) := by
  let S := (bN).smoothLocus
  let : Smooth (S.ι ≫ bN) := by
    apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    change x.1 ∈ S
    exact x.2
  obtain ⟨U,hU,hcU,hUS⟩ := exists_isAffineOpen_mem_and_subset
    (center_mem_smoothLocus V f q t hq hgen u hu hEV hL)
  refine ⟨U,hU,hcU,?_⟩
  rw [← (N).homOfLE_ι hUS,Category.assoc]
  infer_instance

end EnvelopeProperty.SchemeNormalizedCenterSmooth
