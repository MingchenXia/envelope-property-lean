import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceNormalizedDVR
import EnvelopeProperty.AlgGeom.SchemeTraitCenterOriginalRing
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # SAME actual original DVR, EVERY coefficient and unrestricted parameter multiplicity -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing IsDiscreteValuationRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceOriginalCenter
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

include hgen hu hL in
/-- The actual SAME original native normalized-center local map is bijective. -/
theorem stalkMap_bijective : Function.Bijective (Scheme.stalkClosedPointTo ℓ).hom := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk c) :=
    SchemeCoefficientSliceNormalizedDVR.center_stalk_isDiscreteValuationRing V f q t hq hgen u hu hEV hL
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ) := by
    rw [SchemeCoefficientSliceNormalizedTrait.fraction_centerLift]
    exact SchemeCoefficientSliceNormalizedField.genericPointMap_isDominant V f q t hq E hEV
  apply SchemeTraitCenterOriginalRing.stalkClosedPointTo_bijective ℓ
    (SchemeCoefficientSliceNormalization.projection V f q t hq E hEV)
  rw [Category.assoc,SchemeCoefficientSliceNormalization.centerLift_projection]
  exact hgen

/-- The unchanged original V is the SAME actual native normalized-center stalk. -/
def stalkEquiv : (N).presheaf.stalk c ≃+* V := RingEquiv.ofBijective
  (Scheme.stalkClosedPointTo ℓ).hom (stalkMap_bijective V f q t hq hgen u hu hEV hL)

/-- EVERY actual original E-polynomial retains its whole original coefficient map. -/
theorem stalkEquiv_coefficients :
    (stalkEquiv V f q t hq hgen u hu hEV hL).toRingHom.comp
      (SchemeStalkCoefficients.coefficientMap
        (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) c) =
      SchemePolynomialCoefficientSlice.polynomialMap V t E hEV :=
  SchemeLocalResidueCoefficients.stalkClosedPointTo_coefficients
    (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) ℓ _
    (SchemeCoefficientSliceNormalization.centerLift_structure V f q t hq E hEV)

private theorem ord_map_equiv {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  rw [Ring.ord_eq_addVal,Ring.ord_eq_addVal]
  by_cases ha : a = 0
  · subst a
    simp
  obtain ⟨π,hπ⟩ := exists_irreducible A
  obtain ⟨n,w,rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  have hπB : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  rw [map_mul,map_pow,addVal_def' w hπ]
  exact addVal_def' (Units.map e.toMonoidHom w) hπB n

/-- EVERY actual original native stalk element retains its exact SAME original DVR order. -/
theorem stalkEquiv_ord (a : (N).presheaf.stalk c) :
    Ring.ord V (stalkEquiv V f q t hq hgen u hu hEV hL a) = Ring.ord ((N).presheaf.stalk c) a := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk c) :=
    SchemeCoefficientSliceNormalizedDVR.center_stalk_isDiscreteValuationRing V f q t hq hgen u hu hEV hL
  exact ord_map_equiv _ a

include hgen hu hL in
/-- The original nonzero special-fibre parameter keeps its ACTUAL positive
multiplicity on the SAME normalized native model; no reduced-fibre hypothesis is used. -/
theorem exists_positive_parameterOrder (ht0 : t ≠ 0) (ht : t ∈ IsLocalRing.maximalIdeal V) :
    ∃ e : ℕ, 0 < e ∧
      Ring.ord ((N).presheaf.stalk c) ((SchemeStalkCoefficients.coefficientMap
        (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) c) Polynomial.X) = e ∧
      Ring.ord V t = e := by
  let a := (SchemeStalkCoefficients.coefficientMap
    (SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV) c) Polynomial.X
  have ha : stalkEquiv V f q t hq hgen u hu hEV hL a = t := by
    have h := RingHom.congr_fun (stalkEquiv_coefficients V f q t hq hgen u hu hEV hL) Polynomial.X
    simpa only [a,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,SchemePolynomialCoefficientSlice.polynomialMap,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using h
  obtain ⟨e,he⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := V)).not.mpr ht0)
  have he0 : e ≠ 0 := by
    intro hz
    have hv : addVal V t = 0 := by rw [← he,hz,Nat.cast_zero]
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal t).mp ht)) (addVal_eq_zero_iff.mp hv)
  have htord : Ring.ord V t = e := (Ring.ord_eq_addVal t).trans he.symm
  refine ⟨e,Nat.pos_of_ne_zero he0,?_,htord⟩
  exact (stalkEquiv_ord V f q t hq hgen u hu hEV hL a).symm.trans (by rw [ha]; exact htord)

end EnvelopeProperty.SchemeCoefficientSliceOriginalCenter
