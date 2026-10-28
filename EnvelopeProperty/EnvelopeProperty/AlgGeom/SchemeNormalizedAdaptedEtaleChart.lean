import EnvelopeProperty.AlgGeom.SchemeNormalizedResidualSmoothPoints
import EnvelopeProperty.AlgGeom.SchemePointwiseRegularDivisorCoordinates
import EnvelopeProperty.AlgGeom.SchemePointClosureStalkIdeal
import EnvelopeProperty.AlgGeom.DominantFunctionFieldNaturality
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldPullbackCoefficients
import EnvelopeProperty.AlgGeom.SmoothNativeFunctionFieldDimension
import Hironaka.Scheme.Smooth.BlowUpSmoothChart

/-! # Genuine adapted etale charts on the SAME actual original normalized surface -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeNormalizedAdaptedEtaleChart

/-- The actual coefficient structure of the original affine E-plane. -/
def planeBaseMap (F : Type u) [Field F] :
    Spec (.of (MvPolynomial (Fin 2) F)) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F (MvPolynomial (Fin 2) F)))

private theorem smoothOpen_relativeDimension {F : Type u} [Field F] [PerfectField F]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of F))
    (U : Y.Opens) [Nonempty U] [Smooth (U.ι ≫ f)]
    (d : ℕ) (htr : letI := f.stalkAlgebra (genericPoint Y); Algebra.trdeg F Y.functionField = d) :
    SmoothOfRelativeDimension d (U.ι ≫ f) := by
  let : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense (by simpa using (inferInstance : Nonempty U)))
  let := f.stalkAlgebra (genericPoint Y)
  let := (U.ι ≫ f).stalkAlgebra (genericPoint (U : Scheme))
  let := f.sectionsAlgebra ⊤
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y,trivial⟩⟩
  let : Nonempty (U.ι ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨Classical.choice (inferInstance : Nonempty U),trivial⟩⟩
  let : IsIso (DominantFunctionFieldMaps.functionFieldMap U.ι) :=
    DominantFunctionFieldNaturality.functionFieldMap_isIso U.ι
  let φ : Y.functionField →ₐ[F] (U : Scheme).functionField :=
    { (DominantFunctionFieldMaps.functionFieldMap U.ι).hom with
      commutes' := fun a => by
        have h := (f.sectionsFunctionFieldAlgHom ⊤).commutes a
        rw [← h]
        change DominantFunctionFieldMaps.functionFieldMap U.ι
          (Y.germToFunctionField ⊤ (algebraMap F Γ(Y,⊤) a)) = _
        rw [DominantFunctionFieldMaps.functionFieldMap_section]
        exact (SchemeFunctionFieldPullbackCoefficients.genericMap U.ι f ⊤).commutes a }
  let e := AlgEquiv.ofBijective φ (ConcreteCategory.bijective_of_isIso
    (DominantFunctionFieldMaps.functionFieldMap U.ι))
  apply SmoothNativeFunctionFieldDimension.relativeDimension_eq_trdeg (U.ι ≫ f) d
  exact e.trdeg_eq.symm.trans htr

private theorem smoothOnLocus {F : Type u} [Field F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_unique
  intro x _
  exact x.2

private theorem closedSmooth_stalk_dimension {F : Type u} [Field F] [PerfectField F]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of F)) [LocallyOfFinitePresentation f]
    (d : ℕ) (htr : letI := f.stalkAlgebra (genericPoint Y); Algebra.trdeg F Y.functionField = d)
    (z : Y) (hz : IsClosed ({z} : Set Y)) (hzs : z ∈ f.smoothLocus) :
    ringKrullDim (Y.presheaf.stalk z) = d := by
  let T := f.smoothLocus
  let zT : (T : Scheme) := ⟨z,hzs⟩
  let : Nonempty T := ⟨zT⟩
  let : Smooth (T.ι ≫ f) := smoothOnLocus f
  let : SmoothOfRelativeDimension d (T.ι ≫ f) := smoothOpen_relativeDimension f T d htr
  have hzc : IsClosed ({zT} : Set (T : Scheme)) := by
    have hp : T.ι ⁻¹' ({z} : Set Y) = ({zT} : Set (T : Scheme)) := by
      ext y
      change y.1 = z ↔ y = zT
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [← hp]
    exact hz.preimage T.ι.continuous
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso (T.ι.stalkMap zT)).commRingCatIsoToRingEquiv).trans
      (Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed (T.ι ≫ f) d hzc)

private def openQuotientEquiv {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (S : Y.Opens) (x : (S : Scheme)) :
    Y.presheaf.stalk (S.ι x) ⧸ J.stalkIdeal (S.ι x) ≃+*
      (S : Scheme).presheaf.stalk x ⧸ (J.comap S.ι).stalkIdeal x :=
  Ideal.quotientEquiv _ _ (asIso (S.ι.stalkMap x)).commRingCatIsoToRingEquiv
    (J.stalkIdeal_comap S.ι x)

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
/-- The SAME original normalized model has a genuine adapted etale surface
chart containing the SAME original center and an actual original closed residual point. -/
theorem exists_adapted_etale_chart [CharZero k] :
    ∃ (A : Scheme.{u}) (j : A ⟶ N) (g : A ⟶ Spec (.of (MvPolynomial (Fin 2) E))),
      IsAffine A ∧ IsOpenImmersion j ∧ c ∈ Set.range j ∧ Etale g ∧
      g ≫ planeBaseMap E = j ≫ bN ∧
      ((N).fromSpecResidueField c).ker.comap j = (coordinateSubspace E 2 1).comap g ∧
      ∃ z : C, IsClosed ({z} : Set C) ∧
        SchemePointClosureCurve.inclusion c z ∈ Set.range j := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  have hfield : letI := (bN).stalkAlgebra (genericPoint N); Algebra.trdeg E (N).functionField = 2 := by
    let := (bN).stalkAlgebra (genericPoint N)
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
  have hcurve : letI := (bC).stalkAlgebra (genericPoint C); Algebra.trdeg E (C).functionField = 1 := by
    let := (bC).stalkAlgebra (genericPoint C)
    apply (SchemeNormalizedCenterResidueCurve.functionFieldAlgEquiv V f q t hq hgen u hu hEV hL).trdeg_eq.trans
    let bX := SchemeRelativeResidueSliceFinite.originalBaseMap f
    let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) bX
    let α := SchemeLocalResidueCoefficients.residueAlgHom bX q
      (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)
    let := α.toAlgebra
    let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
      IsScalarTower.of_algebraMap_eq fun a => (α.commutes a).symm
    exact (RelativeResidueTranscendenceDegree.trdeg_relativeResidue V
      (X.residueField (q (closedPoint V))) u hu).trans hL
  obtain ⟨z,-,hzc,hzN,hzC,hzNc,-⟩ :=
    SchemeNormalizedResidualSmoothPoints.exists_commonSmooth_closedPoint V f q t hq hgen u hu hEV hL ⊤
      ⟨genericPoint C,trivial⟩
  let S := (bN).smoothLocus
  let x : (S : Scheme) := ⟨SchemePointClosureCurve.inclusion c z,hzN⟩
  let : Nonempty S := ⟨x⟩
  let : Smooth (S.ι ≫ bN) := smoothOnLocus bN
  let : SmoothOfRelativeDimension 2 (S.ι ≫ bN) := smoothOpen_relativeDimension bN S 2 hfield
  let J := ((N).fromSpecResidueField c).ker
  let JS := J.comap S.ι
  let eQ : (S : Scheme).presheaf.stalk x ⧸ JS.stalkIdeal x ≃+* (C).presheaf.stalk z :=
    (openQuotientEquiv J S x).symm.trans (J.stalkQuotientEquiv z)
  let : IsRegularLocalRing ((C).presheaf.stalk z) := Scheme.isRegularAt_of_mem_smoothLocus bC hzC
  let : IsRegularLocalRing ((S : Scheme).presheaf.stalk x ⧸ JS.stalkIdeal x) :=
    IsRegularLocalRing.of_ringEquiv eQ.symm
  have hd : ringKrullDim ((S : Scheme).presheaf.stalk x ⧸ JS.stalkIdeal x) = 1 :=
    (ringKrullDim_eq_of_ringEquiv eQ).trans (closedSmooth_stalk_dimension bC 1 hcurve z hzc hzC)
  have hxc : IsClosed ({x} : Set (S : Scheme)) := by
    have hp : S.ι ⁻¹' ({SchemePointClosureCurve.inclusion c z} : Set N) = {x} := by
      ext y
      change y.1 = SchemePointClosureCurve.inclusion c z ↔ y = x
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [← hp]
    exact hzNc.preimage S.ι.continuous
  obtain ⟨W,hW,hxW,-⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : (S : Scheme).Opens) from trivial)
  obtain ⟨U,hxU,-,v,hE,hAd⟩ :=
    SchemePointwiseRegularDivisorCoordinates.exists_etale_chart_within (S.ι ≫ bN) JS x hxc hd ⟨W,hW⟩ hxW
  let j : (U.1 : Scheme) ⟶ N := U.1.ι ≫ S.ι
  let g := toAffineSpace (S.ι ≫ bN) U.1 v
  let : IsAffine (U.1 : Scheme) := U.2
  let : IsOpenImmersion j := inferInstance
  have hzj : SchemePointClosureCurve.inclusion c z ∈ Set.range j := ⟨⟨x,hxU⟩,rfl⟩
  have hsp : c ⤳ SchemePointClosureCurve.inclusion c z := by
    simpa only [SchemePointClosureStalkIdeal.inclusion_genericPoint] using
      (genericPoint_specializes z).map (SchemePointClosureCurve.inclusion c).continuous
  refine ⟨U.1,j,g,inferInstance,inferInstance,hsp.mem_open j.isOpenEmbedding.isOpen_range hzj,hE,?_,?_,z,hzc,hzj⟩
  · exact (toAffineSpace_comp_structure (S.ι ≫ bN) U.1 v).trans (Category.assoc _ _ _).symm
  · exact (Scheme.IdealSheafData.comap_comp J U.1.ι S.ι).trans hAd

end EnvelopeProperty.SchemeNormalizedAdaptedEtaleChart
