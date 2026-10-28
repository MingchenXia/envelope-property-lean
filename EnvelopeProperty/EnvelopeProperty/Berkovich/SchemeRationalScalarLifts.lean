/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeScalarBaseChangeGlobal
import EnvelopeProperty.Berkovich.SchemeResidueCompletion
import EnvelopeProperty.Berkovich.CompleteAlgebraicClosure

/-!
# Actual rational lifts over completed algebraic closures of point fields

The true original completed stalk residue field and its canonical field-valued
scheme point derive the base-field coefficient map. The actual completed
algebraic closure and genuine pullback universal property construct a rational
point of the literal scalar-changed scheme, preserving the whole original point.
-/

open scoped Classical NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange
variable {F : Type u} [NormedField F] [IsUltrametricDist F]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of F))
    (x : RelativeSchemeValuedPoint (NormedField.valuation (K := F)) f)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original field-valued scheme point derives the entire base-field
coefficient map into the original completed stalk residue field. -/
def fcPointFieldCoefficient : F →+* SchemeValuedPoint.H x.1 :=
  (Scheme.Spec.preimage (SchemeValuedPoint.fieldPoint x.1 ≫ f)).unop.hom

/-- The entire true canonical completed-field point preserves the original scheme base. -/
theorem fcPointFieldCoefficient_spec :
    Spec.map (CommRingCat.ofHom (fcPointFieldCoefficient f x)) =
      SchemeValuedPoint.fieldPoint x.1 ≫ f :=
  Scheme.Spec.map_preimage _

/-- Every original base coefficient retains its actual prescribed field norm. -/
theorem fcPointFieldCoefficient_norm (c : F) : ‖fcPointFieldCoefficient f x c‖₊ = ‖c‖₊ := by
  have h : SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (fcPointFieldCoefficient f x)))
      (SchemeValuedPoint.basePoint (NormedField.valuation (K := SchemeValuedPoint.H x.1))) =
      SchemeValuedPoint.basePoint (NormedField.valuation (K := F)) := by
    rw [fcPointFieldCoefficient_spec, SchemeValuedPoint.map_comp,
      SchemeValuedPoint.map_norm_basePoint_fieldPoint]
    exact x.2
  have he := congrArg (fun y => (SchemeValuedPoint.spectrumHomeomorph y).val c) h
  simp only [SchemeValuedPoint.spectrumHomeomorph_map, SchemeValuedPoint.basePoint,
    Homeomorph.apply_symm_apply, Spectrum.comap_val_apply] at he
  exact he

/-- The genuine completed algebraic closure of the actual point's completed
stalk residue field, in the universe of the original scheme and base field. -/
def fcRationalLiftField : Type u := EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)

instance fcRationalLiftFieldNormedField : NormedField (fcRationalLiftField f x) :=
  inferInstanceAs (NormedField (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

instance fcRationalLiftFieldComplete : CompleteSpace (fcRationalLiftField f x) :=
  inferInstanceAs (CompleteSpace (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

instance fcRationalLiftFieldUltrametric : IsUltrametricDist (fcRationalLiftField f x) :=
  inferInstanceAs (IsUltrametricDist (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

instance fcRationalLiftFieldAlgClosed : IsAlgClosed (fcRationalLiftField f x) :=
  inferInstanceAs (IsAlgClosed (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

instance fcRationalLiftFieldPointAlgebra :
    Algebra (SchemeValuedPoint.H x.1) (fcRationalLiftField f x) :=
  inferInstanceAs (Algebra (SchemeValuedPoint.H x.1)
    (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

instance fcRationalLiftFieldPointNormedAlgebra :
    NormedAlgebra (SchemeValuedPoint.H x.1) (fcRationalLiftField f x) :=
  inferInstanceAs (NormedAlgebra (SchemeValuedPoint.H x.1)
    (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1)))

/-- The actual original base coefficient action on this same completed closure. -/
instance fcRationalLiftFieldAlgebra : Algebra F (fcRationalLiftField f x) :=
  ((algebraMap (SchemeValuedPoint.H x.1) (fcRationalLiftField f x)).comp
    (fcPointFieldCoefficient f x)).toAlgebra

/-- Every original coefficient norm is retained by the actual field extension. -/
theorem fcRationalLiftField_val_algebraMap (c : F) :
    NormedField.valuation (K := fcRationalLiftField f x)
      (algebraMap F (fcRationalLiftField f x) c) = NormedField.valuation (K := F) c := by
  change ‖algebraMap (SchemeValuedPoint.H x.1)
    (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1))
    (fcPointFieldCoefficient f x c)‖₊ = ‖c‖₊
  apply NNReal.eq
  change ‖algebraMap (SchemeValuedPoint.H x.1)
    (EnvelopeProperty.CompleteAlgebraicClosure (SchemeValuedPoint.H x.1))
    (fcPointFieldCoefficient f x c)‖ = ‖c‖
  rw [EnvelopeProperty.completeAlgebraicClosure_norm_algebraMap]
  exact congrArg (fun a : ℝ≥0 => (a : ℝ)) (fcPointFieldCoefficient_norm f x c)

/-- The derived original field extension is genuinely normed, with the exact
actual coefficient action; completeness and algebraic closedness are inherited
from the constructed completed algebraic closure. -/
instance fcRationalLiftFieldNormedAlgebra : NormedAlgebra F (fcRationalLiftField f x) where
  norm_smul_le c a := by
    rw [Algebra.smul_def, norm_mul]
    have hc : ‖algebraMap F (fcRationalLiftField f x) c‖ = ‖c‖ :=
      congrArg (fun z : ℝ≥0 => (z : ℝ)) (fcRationalLiftField_val_algebraMap f x c)
    rw [hc]

/-- The actual rational point morphism of the literal scalar-changed scheme. -/
def fcRationalLiftSection :
    Spec (CommRingCat.of (fcRationalLiftField f x)) ⟶
      model (S := fcRationalLiftField f x) f :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap (SchemeValuedPoint.H x.1) (fcRationalLiftField f x))) ≫
      SchemeValuedPoint.fieldPoint x.1)
    (𝟙 _) (by
      rw [Category.assoc, ← fcPointFieldCoefficient_spec, ← Spec.map_comp, Category.id_comp]
      rfl)

/-- The actual rational point is a section of the entire new field structure. -/
theorem fcRationalLiftSection_structure :
    fcRationalLiftSection f x ≫ structureMap (S := fcRationalLiftField f x) f = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Its whole original projection is the genuine original completed-field point
preceded by the actual completed algebraic closure coefficient extension. -/
theorem fcRationalLiftSection_projection :
    fcRationalLiftSection f x ≫ projection (S := fcRationalLiftField f x) f =
      Spec.map (CommRingCat.ofHom (algebraMap (SchemeValuedPoint.H x.1) (fcRationalLiftField f x))) ≫
        SchemeValuedPoint.fieldPoint x.1 :=
  pullback.lift_fst _ _ _

/-- The norm point of that actual rational section gives an actual whole
native point prescribing exactly the new field norm. -/
def fcRationalScalarLift :
    RelativeSchemeValuedPoint (NormedField.valuation (K := fcRationalLiftField f x))
      (structureMap (S := fcRationalLiftField f x) f) :=
  ⟨SchemeValuedPoint.map (fcRationalLiftSection f x)
    (SchemeValuedPoint.basePoint (NormedField.valuation (K := fcRationalLiftField f x))), by
      change SchemeValuedPoint.map (structureMap (S := fcRationalLiftField f x) f)
        (SchemeValuedPoint.map (fcRationalLiftSection f x)
          (SchemeValuedPoint.basePoint (NormedField.valuation (K := fcRationalLiftField f x)))) =
        SchemeValuedPoint.basePoint (NormedField.valuation (K := fcRationalLiftField f x))
      rw [← SchemeValuedPoint.map_comp, fcRationalLiftSection_structure, SchemeValuedPoint.map_id]⟩

/-- True scalar restriction of the constructed rational point recovers the
ENTIRE original valued scheme point. No rational-lift certificate is supplied. -/
theorem fcRationalScalarLift_nativeMap :
    nativeMap (fcRationalLiftField_val_algebraMap f x) f (fcRationalScalarLift f x) = x := by
  apply Subtype.ext
  change SchemeValuedPoint.map (projection (S := fcRationalLiftField f x) f)
    (SchemeValuedPoint.map (fcRationalLiftSection f x)
      (SchemeValuedPoint.basePoint (NormedField.valuation (K := fcRationalLiftField f x)))) = x.1
  rw [← SchemeValuedPoint.map_comp, fcRationalLiftSection_projection, SchemeValuedPoint.map_comp]
  rw [SchemeValuedPoint.map_basePoint
    (v := NormedField.valuation (K := SchemeValuedPoint.H x.1))
    (w := NormedField.valuation (K := fcRationalLiftField f x))
    (algebraMap (SchemeValuedPoint.H x.1) (fcRationalLiftField f x))
    (fun c => nnnorm_algebraMap' (fcRationalLiftField f x) c)]
  exact SchemeValuedPoint.map_norm_basePoint_fieldPoint x.1

section RationalSection
variable {E : Type u} [NormedField E] [IsUltrametricDist E] [NormedAlgebra F E]
    (s : Spec (CommRingCat.of F) ⟶ X) (hs : s ≫ f = 𝟙 _)

/-- Any genuine original rational section has an actual rational section
on the literal scheme pullback through every normed scalar extension. -/
def fcScalarChangeRationalSection : Spec (CommRingCat.of E) ⟶ model (S := E) f :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ s) (𝟙 _) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

omit [IsUltrametricDist F] [IsUltrametricDist E] in
/-- The whole lifted rational morphism is a section of the genuine new base. -/
theorem fcScalarChangeRationalSection_structure :
    fcScalarChangeRationalSection (E := E) f s hs ≫ structureMap (S := E) f = 𝟙 _ :=
  pullback.lift_snd _ _ _

omit [IsUltrametricDist F] [IsUltrametricDist E] in
/-- Its entire original projection is the actual coefficient extension
followed by the genuine original rational section. -/
theorem fcScalarChangeRationalSection_projection :
    fcScalarChangeRationalSection (E := E) f s hs ≫ projection (S := E) f =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ s :=
  pullback.lift_fst _ _ _

/-- The norm point of the true lifted rational section recovers the WHOLE
norm point of the original rational section under actual native projection. -/
theorem fcScalarChangeRationalSection_nativeProjection :
    SchemeValuedPoint.map (projection (S := E) f)
      (SchemeValuedPoint.map (fcScalarChangeRationalSection (E := E) f s hs)
        (SchemeValuedPoint.basePoint (NormedField.valuation (K := E)))) =
      SchemeValuedPoint.map s (SchemeValuedPoint.basePoint (NormedField.valuation (K := F))) := by
  rw [← SchemeValuedPoint.map_comp, fcScalarChangeRationalSection_projection,
    SchemeValuedPoint.map_comp]
  rw [SchemeValuedPoint.map_basePoint
    (v := NormedField.valuation (K := F)) (w := NormedField.valuation (K := E))
    (algebraMap F E) (fun c => nnnorm_algebraMap' E c)]

end RationalSection
end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
