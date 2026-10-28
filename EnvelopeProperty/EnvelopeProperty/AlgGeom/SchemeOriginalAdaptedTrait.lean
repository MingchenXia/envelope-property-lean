import EnvelopeProperty.AlgGeom.SchemeNormalizedAuxiliaryParameter
import EnvelopeProperty.AlgGeom.SchemeTraitCenterNativeOrders
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeOriginalAdaptedTrait
private theorem trait_range {V : Type u} [CommRing V] [IsLocalRing V]
    {A Y : Scheme.{u}} (j : A ⟶ Y) [IsOpenImmersion j]
    (q : Spec (.of V) ⟶ Y) (hc : q (closedPoint V) ∈ Set.range j) : Set.range q ⊆ Set.range j := by
  rintro _ ⟨x,rfl⟩
  exact ((specializes_closedPoint x).map q.continuous).mem_open j.isOpenEmbedding.isOpen_range hc

def lift {V : Type u} [CommRing V] [IsLocalRing V]
    {A Y : Scheme.{u}} (j : A ⟶ Y) [IsOpenImmersion j]
    (q : Spec (.of V) ⟶ Y) (hc : q (closedPoint V) ∈ Set.range j) : Spec (.of V) ⟶ A :=
  IsOpenImmersion.lift j q (trait_range j q hc)

theorem lift_projection {V : Type u} [CommRing V] [IsLocalRing V]
    {A Y : Scheme.{u}} (j : A ⟶ Y) [IsOpenImmersion j]
    (q : Spec (.of V) ⟶ Y) (hc : q (closedPoint V) ∈ Set.range j) :
    lift j q hc ≫ j = q := IsOpenImmersion.lift_fac _ _ _

private theorem firstCoordinate_stalkIdeal {F : Type u} [Field F] {A : Scheme.{u}}
    (g : A ⟶ Spec (.of (MvPolynomial (Fin 2) F))) (x : A) :
    ((coordinateSubspace F 2 1).comap g).stalkIdeal x =
      Ideal.span {SchemeStalkCoefficients.coefficientMap g x (MvPolynomial.X (0 : Fin 2))} := by
  rw [Scheme.IdealSheafData.stalkIdeal_comap,stalkIdeal_coordinateSubspace,
    Ideal.map_span,Set.image_image]
  have hi : {i : Fin 2 | i.val < 1} = {0} := by
    ext i
    simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,Fin.ext_iff]
    omega
  rw [hi,Set.image_singleton]
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

private theorem wholeTraitMap {R V : Type u} [CommRing R] [CommRing V] [IsLocalRing V]
    {A : Scheme.{u}} (g : A ⟶ Spec (.of R)) (q : Spec (.of V) ⟶ A) :
    q ≫ g = Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo q).hom.comp
      (SchemeStalkCoefficients.coefficientMap g (q (closedPoint V))))) := by
  change q ≫ g = Spec.map (CommRingCat.ofHom
    (SchemeStalkCoefficients.coefficientMap g (q (closedPoint V))) ≫ Scheme.stalkClosedPointTo q)
  rw [Spec.map_comp,← SchemeStalkCoefficients.fromSpecStalk_structureMap,
    ← Category.assoc,Scheme.Spec_stalkClosedPointTo_fromSpecStalk]


private theorem pulledOriginalIdeal_maximal {Y A : Scheme.{u}} [IsIntegral Y]
    (c : Y) (j : A ⟶ Y) [IsOpenImmersion j] (x : A) (hxc : j x = c) :
    (((Y.fromSpecResidueField c).ker).comap j).stalkIdeal x = maximalIdeal (A.presheaf.stalk x) := by
  rw [Scheme.IdealSheafData.stalkIdeal_comap]
  have hJ : (Y.fromSpecResidueField c).ker.stalkIdeal (j x) =
      maximalIdeal (Y.presheaf.stalk (j x)) := by
    subst c
    exact SchemePointClosureStalkIdeal.stalkIdeal_eq_maximalIdeal (j x)
  rw [hJ]
  exact map_maximalIdeal_of_surjective _ (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).2

private theorem canonical_bijective_congr {V : Type u} [CommRing V] [IsLocalRing V]
    {Y : Scheme.{u}} (q₁ q₂ : Spec (.of V) ⟶ Y) (h : q₁ = q₂)
    (hs : Function.Bijective (Scheme.stalkClosedPointTo q₂).hom) :
    Function.Bijective (Scheme.stalkClosedPointTo q₁).hom := by
  subst q₂
  exact hs

private theorem parameterMap_base (F : Type u) [Field F] :
    SchemeNormalizedAuxiliaryParameter.parameterMap F ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : F →+* F[X])) =
        SchemeNormalizedAdaptedEtaleChart.planeBaseMap F := by
  rw [SchemeNormalizedAuxiliaryParameter.parameterMap,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact Polynomial.aeval_C _ _

private theorem polynomial_eval_coefficients {F D : Type u} [Field F] [CommRing D] [Algebra F D]
    (α : MvPolynomial (Fin 2) F →+* D)
    (hcoeff : α.comp (MvPolynomial.C : F →+* MvPolynomial (Fin 2) F) = algebraMap F D) :
    α.comp (SchemeNormalizedAuxiliaryParameter.coefficientMap F) =
      (Polynomial.aeval (α (MvPolynomial.X (0 : Fin 2)))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    change α ((Polynomial.aeval (R := F) (MvPolynomial.X (0 : Fin 2))) (Polynomial.C a)) =
      (Polynomial.aeval (R := F) (α (MvPolynomial.X (0 : Fin 2)))) (Polynomial.C a)
    rw [Polynomial.aeval_C,Polynomial.aeval_C]
    exact RingHom.congr_fun hcoeff a
  · change α ((Polynomial.aeval (R := F) (MvPolynomial.X (0 : Fin 2))) Polynomial.X) =
      (Polynomial.aeval (R := F) (α (MvPolynomial.X (0 : Fin 2)))) Polynomial.X
    rw [Polynomial.aeval_X,Polynomial.aeval_X]

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
/-- The actual auxiliary coordinate is an irreducible element of the SAME original V,
with the WHOLE original trait and polynomial diagram and true unrestricted t-order. -/
theorem exists_original_uniformizer_trait [CharZero k] (ht0 : t ≠ 0) (ht : t ∈ maximalIdeal V) :
    letI := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
    ∃ (A : Scheme.{u}) (j : A ⟶ N) (g : A ⟶ Spec (.of (MvPolynomial (Fin 2) E)))
      (qA : Spec (.of V) ⟶ A) (π : V) (v : Vˣ) (e : ℕ),
      IsAffine A ∧ IsOpenImmersion j ∧ Etale g ∧
      SmoothOfRelativeDimension 1 (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E) ∧
      qA ≫ j = ℓ ∧ Function.Bijective (Scheme.stalkClosedPointTo qA).hom ∧ Irreducible π ∧
      qA ≫ g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval π).toRingHom) ∧
      ((N).fromSpecResidueField c).ker.comap j = (coordinateSubspace E 2 1).comap g ∧
      0 < e ∧ t = v * π ^ e ∧ Ring.ord V t = e := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  obtain ⟨A,j,g,hA,hj,hc,hg,hs,hbase,hres,-⟩ :=
    SchemeNormalizedAuxiliaryParameter.exists_smooth_auxiliary_chart V f q t hq hgen u hu hEV hL
  let := hj
  let qA := lift j ℓ hc
  have hqA : qA ≫ j = ℓ := lift_projection j ℓ hc
  let x := qA (closedPoint V)
  have hxc : j x = c := congrArg (fun a : Spec (.of V) ⟶ N => a (closedPoint V)) hqA
  have hbij : Function.Bijective (Scheme.stalkClosedPointTo qA).hom := by
    have hcomp := canonical_bijective_congr (qA ≫ j) ℓ hqA
      (SchemeCoefficientSliceOriginalCenter.stalkMap_bijective V f q t hq hgen u hu hEV hL)
    rw [Scheme.stalkClosedPointTo_comp] at hcomp
    exact (Function.Bijective.of_comp_iff (Scheme.stalkClosedPointTo qA).hom
      (ConcreteCategory.bijective_of_isIso (j.stalkMap x))).mp hcomp
  let α := (Scheme.stalkClosedPointTo qA).hom.comp (SchemeStalkCoefficients.coefficientMap g x)
  let π := α (MvPolynomial.X (0 : Fin 2))
  have hπ : Irreducible π := by
    have hm : maximalIdeal (A.presheaf.stalk x) =
        Ideal.span {SchemeStalkCoefficients.coefficientMap g x (MvPolynomial.X (0 : Fin 2))} := by
      rw [← pulledOriginalIdeal_maximal c j x hxc,hres]
      exact firstCoordinate_stalkIdeal g x
    have hmV := congrArg (Ideal.map (Scheme.stalkClosedPointTo qA).hom) hm
    rw [map_maximalIdeal_of_surjective _ hbij.2,Ideal.map_span,Set.image_singleton] at hmV
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hmV
  have hα : qA ≫ g = Spec.map (CommRingCat.ofHom α) := wholeTraitMap g qA
  have hcoeff : α.comp (MvPolynomial.C : E →+* MvPolynomial (Fin 2) E) = algebraMap E V := by
    have hc : CommRingCat.ofHom (α.comp (MvPolynomial.C : E →+* MvPolynomial (Fin 2) E)) =
        CommRingCat.ofHom (algebraMap E V) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (MvPolynomial.C : E →+* MvPolynomial (Fin 2) E) ≫
        CommRingCat.ofHom α) = _
      rw [Spec.map_comp,← hα,Category.assoc]
      change qA ≫ g ≫ SchemeNormalizedAdaptedEtaleChart.planeBaseMap E = _
      rw [hbase,← Category.assoc,hqA]
      exact SchemeCoefficientSliceNormalizedDVR.centerLift_coefficientBaseMap V f q t hq E hEV
    exact congrArg CommRingCat.Hom.hom hc
  have hpoly : α.comp (SchemeNormalizedAuxiliaryParameter.coefficientMap E) =
      (Polynomial.aeval π).toRingHom := polynomial_eval_coefficients α hcoeff

  have htrait : qA ≫ g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval π).toRingHom) := by
    rw [← Category.assoc,hα,SchemeNormalizedAuxiliaryParameter.parameterMap,← Spec.map_comp]
    exact congrArg (fun a : E[X] →+* V => Spec.map (CommRingCat.ofHom a)) hpoly
  obtain ⟨e,v,hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  have he0 : e ≠ 0 := by
    intro he
    have htu : IsUnit t := by simpa only [hv,he,pow_zero,mul_one] using v.isUnit
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal t).mp ht)) htu
  have hord : Ring.ord V t = e := by
    rw [Ring.ord_eq_addVal,hv,IsDiscreteValuationRing.addVal_def' v hπ]
  exact ⟨A,j,g,qA,π,v,e,hA,hj,hg,hs,hqA,hbij,hπ,htrait,hres,Nat.pos_of_ne_zero he0,hv,hord⟩

end EnvelopeProperty.SchemeOriginalAdaptedTrait
