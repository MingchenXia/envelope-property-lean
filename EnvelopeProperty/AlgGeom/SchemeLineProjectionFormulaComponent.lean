import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaUnit
import EnvelopeProperty.AlgGeom.SchemePullbackBraided

/-! # The actual components of the original inverse-tensor line PF

These identities expose the original PF itself through the original
unit, tensor comparison and counit.  They construct no replacement PF.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open EnvelopeProperty.SchemeLineProjectionFormula
universe u v

section Abstract
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]

/-- The original component is its canonical unit/tensor/counit composite,
as forced by original source naturality and the proved strong unit law. -/
theorem projectionFormulaOfTensorInverse_hom_component
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Braided]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) (N : D) :
    (projectionFormulaOfTensorInverse F G adj L Q e).hom.app N =
      adj.unit.app (G.obj N ⊗ L) ≫
        G.map (Functor.OplaxMonoidal.δ F (G.obj N) L) ≫
        G.map (adj.counit.app N ▷ F.obj L) := by
  let P := projectionFormulaOfTensorInverse F G adj L Q e
  have hn := P.hom.naturality (adj.counit.app N)
  change (G.map (adj.counit.app N) ▷ L) ≫ P.hom.app N =
    P.hom.app (F.obj (G.obj N)) ≫ G.map (adj.counit.app N ▷ F.obj L) at hn
  calc
    P.hom.app N =
        ((adj.unit.app (G.obj N) ≫ G.map (adj.counit.app N)) ▷ L) ≫ P.hom.app N := by
      erw [adj.right_triangle_components, MonoidalCategory.id_whiskerRight, Category.id_comp]
    _ = (adj.unit.app (G.obj N) ▷ L) ≫ P.hom.app (F.obj (G.obj N)) ≫
        G.map (adj.counit.app N ▷ F.obj L) := by
      rw [MonoidalCategory.comp_whiskerRight, Category.assoc, hn]
    _ = _ := by
      rw [← Category.assoc, projectionFormulaOfTensorInverse_unit_tensor]
      simp only [Category.assoc]
end Abstract

open AlgebraicGeometry Scheme.Modules
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
private noncomputable local instance originalComponentPullbackMonoidal
    {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

/-- The original native line PF has the same actual native component,
with its original pullback monoidal structure and native adjunction. -/
theorem lineProjectionFormulaObj_hom_component {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L) (N : Y.Modules) :
    (lineProjectionFormulaObj g L hL N).hom =
      (pullbackPushforwardAdjunction g).unit.app ((pushforward g).obj N ⊗ L) ≫
        (pushforward g).map
          (Functor.OplaxMonoidal.δ (pullback g) ((pushforward g).obj N) L) ≫
        (pushforward g).map
          ((pullbackPushforwardAdjunction g).counit.app N ▷ (pullback g).obj L) := by
  let : (pullback g).Braided := SchemePullbackBraided.pullbackBraided g
  exact projectionFormulaOfTensorInverse_hom_component
    (pullback g) (pushforward g) (pullbackPushforwardAdjunction g)
    L (dualObj L) hL.monoidalEvaluationIso N

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
