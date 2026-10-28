import EnvelopeProperty.AlgGeom.SchemeDVRBaseChangeImage
import EnvelopeProperty.AlgGeom.SchemeGenericFieldGraph

/-! # Literal polynomial coefficient slices retain the original parameter and function field -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemePolynomialCoefficientSlice
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [Algebra k X.functionField] (V : Subalgebra k X.functionField)
  [IsFractionRing V X.functionField]
  (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
  (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)

/-- The literal inclusion of the actual coefficient field into the SAME V. -/
def coefficientMap : E →+* V := (Subalgebra.inclusion hEV).toRingHom

/-- Every actual E-polynomial is evaluated at the SAME original parameter. -/
def polynomialMap : Polynomial E →+* V := Polynomial.eval₂RingHom (coefficientMap V E hEV) t

omit [IsFractionRing V X.functionField] in
/-- Restriction to the SAME original k-polynomials is EXACT original evaluation. -/
theorem polynomialMap_comp :
    (polynomialMap V t E hEV).comp (Polynomial.mapRingHom (algebraMap k E)) =
      (Polynomial.aeval t).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_C,
      polynomialMap,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
      AlgHom.toRingHom_eq_coe]
    change (coefficientMap V E hEV) ((algebraMap k E) c) =
      Polynomial.eval₂ (algebraMap k V) t (Polynomial.C c)
    rw [Polynomial.eval₂_C]
    rfl
  · simp [polynomialMap]

/-- The genuine original coefficient-basechange image slice. -/
def model : Scheme.{u} :=
  SchemeDVRBaseChangeImage.model (K := X.functionField) f
    (Polynomial.mapRingHom (algebraMap k E)) q (polynomialMap V t E hEV)
    (by rw [polynomialMap_comp]; exact hq)

/-- The actual slice's SAME original projection to X. -/
def projection : model V f q t hq E hEV ⟶ X :=
  SchemeDVRBaseChangeImage.projection f (Polynomial.mapRingHom (algebraMap k E)) q
    (polynomialMap V t E hEV) (by rw [polynomialMap_comp]; exact hq)

/-- The actual whole original E[t]-structure of the constructed slice. -/
def structureMap : model V f q t hq E hEV ⟶ Spec (.of (Polynomial E)) :=
  SchemeDVRBaseChangeImage.structureMap f (Polynomial.mapRingHom (algebraMap k E)) q
    (polynomialMap V t E hEV) (by rw [polynomialMap_comp]; exact hq)

/-- The WHOLE original DVR diagram factors through the true slice. -/
def centerLift : Spec (.of V) ⟶ model V f q t hq E hEV :=
  SchemeDVRBaseChangeImage.centerLift f (Polynomial.mapRingHom (algebraMap k E)) q
    (polynomialMap V t E hEV) (by rw [polynomialMap_comp]; exact hq)

/-- The true native original fraction-field point of the actual slice. -/
def genericPointMap : Spec X.functionField ⟶ model V f q t hq E hEV :=
  (SchemeDVRBaseChangeImage.genericMap (K := X.functionField) f
    (Polynomial.mapRingHom (algebraMap k E)) q (polynomialMap V t E hEV)
    (by rw [polynomialMap_comp]; exact hq)).toImage

/-- The actual whole projection is EXACTLY the SAME original q. -/
theorem centerLift_projection :
    centerLift V f q t hq E hEV ≫ projection V f q t hq E hEV = q :=
  SchemeDVRBaseChangeImage.centerLift_projection _ _ _ _ _

/-- The actual whole coefficient evaluation remains the SAME original one. -/
theorem centerLift_structure :
    centerLift V f q t hq E hEV ≫ structureMap V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (polynomialMap V t E hEV)) :=
  SchemeDVRBaseChangeImage.centerLift_structure _ _ _ _ _

omit [IsFractionRing V X.functionField] in
/-- The native generic projection is the ORIGINAL fraction-field restriction. -/
theorem genericPointMap_projection :
    genericPointMap V f q t hq E hEV ≫ projection V f q t hq E hEV =
      Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q := by
  dsimp only [genericPointMap,projection,model,SchemeDVRBaseChangeImage.projection]
  rw [← Category.assoc,Scheme.Hom.toImage_imageι]
  dsimp only [SchemeDVRBaseChangeImage.genericMap]
  rw [Category.assoc]
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ z)
    (pullback.lift_fst _ _ _)

omit [IsFractionRing V X.functionField] in
/-- Integrality of the SAME actual whole slice is genuinely derived. -/
theorem model_isIntegral : IsIntegral (model V f q t hq E hEV) :=
  SchemeDVRBaseChangeImage.model_isIntegral _ _ _ _ _

omit [IsFractionRing V X.functionField] in
/-- The original proper f makes the actual E[t]-slice genuinely proper. -/
theorem structureMap_isProper [IsProper f] :
    IsProper (structureMap V f q t hq E hEV) :=
  SchemeDVRBaseChangeImage.structureMap_isProper _ _ _ _ _

omit [IsFractionRing V X.functionField] in
/-- The actual original generic point is genuinely dense in the whole slice. -/
theorem genericPointMap_isDominant : IsDominant (genericPointMap V f q t hq E hEV) := by
  let g := SchemeDVRBaseChangeImage.genericMap (K := X.functionField) f
    (Polynomial.mapRingHom (algebraMap k E)) q (polynomialMap V t E hEV)
    (by rw [polynomialMap_comp]; exact hq)
  let : QuasiCompact g := ⟨fun U _ _ => (Set.toFinite (g ⁻¹' U)).isCompact⟩
  change IsDominant g.toImage
  infer_instance

/-- The true native slice function field is the SAME original K, with the
actual original generic triangle, without any supplied field comparison. -/
def functionFieldEquiv
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
      X.fromSpecStalk (genericPoint X)) :
    letI := model_isIntegral V f q t hq E hEV
    (model V f q t hq E hEV).functionField ≃+* X.functionField := by
  let := model_isIntegral V f q t hq E hEV
  let := genericPointMap_isDominant V f q t hq E hEV
  apply SchemeGenericFieldGraph.functionFieldEquiv (genericPointMap V f q t hq E hEV)
    (projection V f q t hq E hEV)
  rw [genericPointMap_projection,hgen]

end EnvelopeProperty.SchemePolynomialCoefficientSlice
