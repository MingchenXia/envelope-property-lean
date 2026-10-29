import EnvelopeProperty.AlgGeom.SchemeGenericFieldGraph
import EnvelopeProperty.AlgGeom.SchemeStalkCoefficients

/-! # Actual generic graph field comparisons retain every original coefficient -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeGenericFieldCoefficients

/-- Every original coefficient is preserved by the ACTUAL native generic
field-point map, for the original whole coefficient triangle. -/
theorem fieldHom_coefficients {R K : Type u} [CommRing R] [Field K]
    {Y : Scheme.{u}} [IsIntegral Y] (g : Spec (.of K) ⟶ Y) [IsDominant g]
    (f : Y ⟶ Spec (.of R)) (α : R →+* K)
    (h : g ≫ f = Spec.map (CommRingCat.ofHom α)) :
    (SchemeGenericFieldGraph.fieldHom g).hom.comp
      (SchemeStalkCoefficients.coefficientMap f (genericPoint Y)) = α := by
  have hc : CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap f (genericPoint Y)) ≫
      SchemeGenericFieldGraph.fieldHom g = CommRingCat.ofHom α := by
    apply Spec.map_injective
    rw [Spec.map_comp,← SchemeStalkCoefficients.fromSpecStalk_structureMap,
      ← Category.assoc,SchemeGenericFieldGraph.fieldHom_fromSpecStalk,h]
  exact congrArg CommRingCat.Hom.hom hc

/-- The SAME genuine generic-graph function-field isomorphism preserves the
actual original coefficient action, including its native source stalk algebra. -/
def functionFieldAlgEquiv {F : Type u} [Field F]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [Algebra F X.functionField]
    (g : Spec X.functionField ⟶ Y) [IsDominant g] (p : Y ⟶ X)
    (hp : g ≫ p = X.fromSpecStalk (genericPoint X))
    (f : Y ⟶ Spec (.of F))
    (hf : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F X.functionField))) :
    letI := f.stalkAlgebra (genericPoint Y)
    Y.functionField ≃ₐ[F] X.functionField := by
  let := f.stalkAlgebra (genericPoint Y)
  refine { SchemeGenericFieldGraph.functionFieldEquiv g p hp with commutes' := ?_ }
  intro c
  exact RingHom.congr_fun (fieldHom_coefficients g f (algebraMap F X.functionField) hf) c

end EnvelopeProperty.SchemeGenericFieldCoefficients
