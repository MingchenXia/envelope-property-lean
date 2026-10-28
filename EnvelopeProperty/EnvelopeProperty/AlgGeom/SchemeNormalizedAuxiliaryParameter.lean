import EnvelopeProperty.AlgGeom.SchemeNormalizedAdaptedEtaleChart
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Actual auxiliary first-coordinate smoothness on the SAME original normalized model -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeNormalizedAuxiliaryParameter
variable (F : Type u) [Field F]
/-- The actual original first-coordinate polynomial map. -/
def coefficientMap : F[X] →+* MvPolynomial (Fin 2) F :=
  (Polynomial.aeval (MvPolynomial.X (0 : Fin 2))).toRingHom
private def planeEquiv : MvPolynomial (Fin 2) F ≃+* F[X][X] :=
  ((MvPolynomial.renameEquiv F (_root_.finSuccEquiv 1)).trans
    (MvPolynomial.optionEquivRight F (Fin 1))).toRingEquiv.trans
      (MvPolynomial.uniqueAlgEquiv F[X] (Fin 1)).toRingEquiv
private theorem planeEquiv_coefficients :
    (planeEquiv F).toRingHom.comp (coefficientMap F) = Polynomial.C := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [planeEquiv,coefficientMap,MvPolynomial.renameEquiv_apply,
      MvPolynomial.uniqueAlgEquiv_apply]
  · simp [planeEquiv,coefficientMap,MvPolynomial.renameEquiv_apply,
      MvPolynomial.uniqueAlgEquiv_apply]

/-- The actual auxiliary first-coordinate projection. -/
def parameterMap : Spec (.of (MvPolynomial (Fin 2) F)) ⟶ Spec (.of F[X]) :=
  Spec.map (CommRingCat.ofHom (coefficientMap F))
/-- The actual auxiliary projection is genuinely smooth of relative dimension one. -/
theorem parameterMap_smooth : SmoothOfRelativeDimension 1 (parameterMap F) := by
  have hC : RingHom.IsStandardSmoothOfRelativeDimension 1
      (Polynomial.C : F[X] →+* F[X][X]) := by
    have hm : Algebra.IsStandardSmoothOfRelativeDimension 1 F[X]
        (MvPolynomial (Fin 1) F[X]) := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
        (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card (Fin 1)) F[X]
          (MvPolynomial (Fin 1) F[X]))
    let := hm
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv F[X] (Fin 1)))
  have h := (RingHom.IsStandardSmoothOfRelativeDimension.equiv (planeEquiv F).symm).comp hC
  have he : (planeEquiv F).symm.toRingHom.comp (Polynomial.C : F[X] →+* F[X][X]) =
      coefficientMap F := by
    apply RingHom.ext
    intro a
    apply (planeEquiv F).injective
    change planeEquiv F ((planeEquiv F).symm (Polynomial.C a)) = _
    rw [(planeEquiv F).apply_symm_apply]
    exact (RingHom.congr_fun (planeEquiv_coefficients F) a).symm
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((planeEquiv F).symm.toRingHom.comp (Polynomial.C : F[X] →+* F[X][X])) at h
  rw [he] at h
  exact HasRingHomProperty.Spec_iff.mpr
    (RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)) _ h)

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
/-- A genuine auxiliary first coordinate on the SAME original model is smooth;
the ENTIRE original residual ideal and coefficient square are retained. -/
theorem exists_smooth_auxiliary_chart [CharZero k] :
    ∃ (A : Scheme.{u}) (j : A ⟶ N) (g : A ⟶ Spec (.of (MvPolynomial (Fin 2) E))),
      IsAffine A ∧ IsOpenImmersion j ∧ c ∈ Set.range j ∧ Etale g ∧
      SmoothOfRelativeDimension 1 (g ≫ parameterMap E) ∧
      g ≫ SchemeNormalizedAdaptedEtaleChart.planeBaseMap E = j ≫ bN ∧
      ((N).fromSpecResidueField c).ker.comap j = (coordinateSubspace E 2 1).comap g ∧
      ∃ z : C, IsClosed ({z} : Set C) ∧
        SchemePointClosureCurve.inclusion c z ∈ Set.range j := by
  obtain ⟨A,j,g,hA,hj,hc,hg,hbase,hres,hz⟩ :=
    SchemeNormalizedAdaptedEtaleChart.exists_adapted_etale_chart V f q t hq hgen u hu hEV hL
  let := hg
  let : SmoothOfRelativeDimension 1 (parameterMap E) := parameterMap_smooth E
  have hs : SmoothOfRelativeDimension (0+1) (g ≫ parameterMap E) := inferInstance
  exact ⟨A,j,g,hA,hj,hc,hg,hs,hbase,hres,hz⟩

end EnvelopeProperty.SchemeNormalizedAuxiliaryParameter
