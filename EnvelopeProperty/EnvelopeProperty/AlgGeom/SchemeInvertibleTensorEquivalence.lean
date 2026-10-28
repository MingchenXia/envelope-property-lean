import EnvelopeProperty.AlgGeom.CartierDualEvaluation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-! # Exact tensoring by the same original invertible module sheaf -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u v
namespace EnvelopeProperty.SchemeInvertibleTensorEquivalence

/-- An actual inverse tensor pair gives a genuine equivalence of the same
original category, using the original right-tensor functor. -/
def rightTensorEquivalence {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] (L D : C) (e : L ⊗ D ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight D)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫
      tensorRightTensor L D)
    ((tensorRightTensor D L).symm ≪≫
      (tensoringRight C).mapIso ((β_ D L) ≪≫ e) ≪≫ rightUnitorNatIso C)

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The actual original line bundle and its genuine sheaf dual derive a
whole module-category equivalence with no supplied inverse or exactness certificate. -/
def invertibleTensorEquivalence {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) : X.Modules ≌ X.Modules := by
  let := Scheme.Modules.symmetricCategory X
  exact rightTensorEquivalence L (Scheme.Modules.dualObj L) hL.monoidalEvaluationIso

/-- The equivalence uses the SAME original tensor functor on every original module and morphism. -/
theorem invertibleTensorEquivalence_functor {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    (invertibleTensorEquivalence L hL).functor = tensorRight L := rfl

/-- Actual local invertibility alone derives equivalence of the original tensor functor. -/
theorem tensorRight_isEquivalence {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) : (tensorRight L).IsEquivalence := by
  change (invertibleTensorEquivalence L hL).functor.IsEquivalence
  infer_instance

/-- Tensoring EVERY actual original short exact sequence by an actual original
invertible sheaf retains exactness and both original endpoint maps. -/
theorem tensorRight_shortExact {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    let : (tensorRight L).IsEquivalence := tensorRight_isEquivalence L hL
    (S.map (tensorRight L)).ShortExact := by
  let : (tensorRight L).IsEquivalence := tensorRight_isEquivalence L hL
  exact hS.map_of_exact (tensorRight L)

end EnvelopeProperty.SchemeInvertibleTensorEquivalence
