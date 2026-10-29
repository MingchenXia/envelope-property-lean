import EnvelopeProperty.AlgGeom.SchemeGenericFieldGraph
import EnvelopeProperty.AlgGeom.NormalCurveSmooth

/-! # SAME original generic field point lifts through native normalization and all original base changes -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeDominantPointNormalization
variable {X : Scheme.{u}} [IsIntegral X] {N : Type u} [Field N]
  (g : Spec (.of N) ⟶ X) [IsDominant g]

/-- The SAME actual original field point lifts through actual native normalization,
using only its genuine native generic-stalk coefficient map. -/
def lift : Spec (.of N) ⟶ IntegralSchemeNormalization.normalization X :=
  Spec.map (SchemeGenericFieldGraph.fieldHom g) ≫ IntegralSchemeNormalization.genericLift X

/-- The WHOLE original field-valued morphism is retained EXACTLY. -/
theorem lift_projection : lift g ≫ IntegralSchemeNormalization.projection X = g := by
  rw [lift,Category.assoc,IntegralSchemeNormalization.genericLift_comp_projection]
  exact SchemeGenericFieldGraph.fieldHom_fromSpecStalk g

/-- Actual field spectra and native normalization internally derive dominance
of the SAME original normalization point. -/
theorem lift_isDominant : IsDominant (lift g) := by
  let : IsDominant (Spec.map (SchemeGenericFieldGraph.fieldHom g)) := by
    let : Subsingleton (Spec X.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
    refine ⟨Function.Surjective.denseRange ?_⟩
    intro x
    exact ⟨IsLocalRing.closedPoint N,Subsingleton.elim _ _⟩
  dsimp only [lift,IntegralSchemeNormalization.genericLift]
  infer_instance

omit g in
/-- The SAME actual native normalization projection after original base change. -/
def baseChangeMap {S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) :
    pullback (IntegralSchemeNormalization.projection X ≫ f) b ⟶ pullback f b :=
  pullback.map (IntegralSchemeNormalization.projection X ≫ f) b f b
    (IntegralSchemeNormalization.projection X) (𝟙 _) (𝟙 _) (by simp) (by simp)

omit g in
/-- The SAME original N field point lifts to the actual normalization basechange;
its entire original coefficient point and original generic projection are retained. -/
def baseChangeLift {S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (q : Spec (.of N) ⟶ pullback f b) [IsDominant (q ≫ pullback.fst f b)] :
    Spec (.of N) ⟶ pullback (IntegralSchemeNormalization.projection X ≫ f) b :=
  pullback.lift (lift (q ≫ pullback.fst f b)) (q ≫ pullback.snd f b) (by
    rw [← Category.assoc,lift_projection,Category.assoc,pullback.condition,← Category.assoc])

omit g in
/-- The WHOLE actual original completed/residue field point is unchanged
under the same normalization base-change comparison. -/
theorem baseChangeLift_map {S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (q : Spec (.of N) ⟶ pullback f b) [IsDominant (q ≫ pullback.fst f b)] :
    baseChangeLift f b q ≫ baseChangeMap f b = q := by
  apply pullback.hom_ext
  · dsimp only [baseChangeMap,pullback.map]
    rw [Category.assoc,pullback.lift_fst,← Category.assoc]
    dsimp only [baseChangeLift]
    rw [pullback.lift_fst,lift_projection]
  · dsimp only [baseChangeMap,pullback.map]
    rw [Category.assoc,pullback.lift_snd,Category.comp_id]
    dsimp only [baseChangeLift]
    exact pullback.lift_snd _ _ _

omit g N in
/-- The SAME actual native curve normalization basechanged to the original
new field/base is smooth, internally from actual normal curve geometry. -/
theorem baseChange_smooth {F : Type u} [Field F] [PerfectField F]
    (f : X ⟶ Spec (.of F)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) {T : Scheme.{u}} (b : T ⟶ Spec (.of F)) :
    Smooth (pullback.snd (IntegralSchemeNormalization.projection X ≫ f) b) := by
  let := NormalCurveSmooth.normalization_smooth f hdim
  infer_instance

end EnvelopeProperty.SchemeDominantPointNormalization
