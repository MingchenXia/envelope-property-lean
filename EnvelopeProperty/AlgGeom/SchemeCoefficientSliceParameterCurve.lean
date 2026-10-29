import EnvelopeProperty.AlgGeom.SchemePolynomialCoefficientSlice
import EnvelopeProperty.Algebra.RelativeCoefficientParameterCurve

/-! # The SAME original coefficient slice has actual parameter evaluation and genuine curve field -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceParameterCurve
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [Algebra k X.functionField] (V : Subalgebra k X.functionField)
  [IsFractionRing V X.functionField]
  (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
  (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)

omit [IsFractionRing V X.functionField] in
/-- The WHOLE genuine schematic-image coefficient slice preserves original k[t] structure. -/
theorem projection_structure :
    SchemePolynomialCoefficientSlice.projection V f q t hq E hEV ≫ f =
      SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k E))) := by
  dsimp only [SchemePolynomialCoefficientSlice.projection,SchemePolynomialCoefficientSlice.structureMap,
    SchemeDVRBaseChangeImage.projection,SchemeDVRBaseChangeImage.structureMap]
  rw [Category.assoc,pullback.condition,← Category.assoc]

omit [IsFractionRing V X.functionField] in
/-- The SAME native original SpecK point has EXACT original E-parameter evaluation. -/
theorem genericPointMap_structure :
    SchemePolynomialCoefficientSlice.genericPointMap V f q t hq E hEV ≫
        SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := E) (t : X.functionField)).toRingHom) := by
  dsimp only [SchemePolynomialCoefficientSlice.genericPointMap,SchemePolynomialCoefficientSlice.structureMap,
    SchemeDVRBaseChangeImage.structureMap]
  rw [← Category.assoc,Scheme.Hom.toImage_imageι]
  dsimp only [SchemeDVRBaseChangeImage.genericMap]
  rw [Category.assoc]
  dsimp only [SchemeDVRBaseChangeImage.liftedMap]
  rw [pullback.lift_snd,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change algebraMap V X.functionField
      (Polynomial.eval₂ (SchemePolynomialCoefficientSlice.coefficientMap V E hEV) t (Polynomial.C c)) =
      Polynomial.eval₂ (algebraMap E X.functionField) (t : X.functionField) (Polynomial.C c)
    rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
    rfl
  · simp [SchemePolynomialCoefficientSlice.polynomialMap]

omit [IsFractionRing V X.functionField] in
include hEV in
/-- SAME actual nonzero maximal-ideal parameter is transcendental over ANY
actual coefficient subfield contained in the original DVR, no comparison premise. -/
theorem parameter_transcendental [IsDiscreteValuationRing V]
    (ht0 : t ≠ 0) (ht : t ∈ maximalIdeal V) : Transcendental E (t : X.functionField) := by
  let V' := Char0.extendScalarsOfLE V E hEV
  let e := Char0.extendScalarsOfLEEquiv V E hEV
  let t' : V' := e t
  have ht' : t' ≠ 0 := fun h => ht0 (e.injective (h.trans (map_zero e).symm))
  have hnt : ¬IsUnit t' := by
    intro h
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal t).mp ht)) (h.map e.symm.toMonoidHom)
  intro halg
  have hinv := V'.inv_mem_of_algebraic halg
  apply hnt
  refine IsUnit.of_mul_eq_one (⟨_,hinv⟩ : V') (Subtype.ext ?_)
  change (t : X.functionField) * (t : X.functionField)⁻¹ = 1
  exact mul_inv_cancel₀ (fun h => ht0 (Subtype.ext h))

omit f q t hq E hEV in
/-- Genuine finite relative residue lifts yield actual degree TWO over the
SAME lifted coefficient field inside the UNCHANGED original K. -/
theorem functionField_trdeg_two [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V]
    (L : Type u) [Field L] [Algebra k L] [Algebra L (ResidueField V)]
    [IsScalarTower k L (ResidueField V)] (hL : Algebra.trdeg k L = 1)
    {ι : Type u} [Finite ι] (u : ι → V) (hu : IsTranscendenceBasis L (residue V ∘ u)) :
    Algebra.trdeg (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))) X.functionField = 2 := by
  rw [RelativeResidueTranscendenceDegree.trdeg_relativeFractionField V L u hu,hL]
  norm_num

end EnvelopeProperty.SchemeCoefficientSliceParameterCurve
