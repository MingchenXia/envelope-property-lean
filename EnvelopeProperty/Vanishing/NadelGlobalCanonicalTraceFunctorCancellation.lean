import Mathlib.CategoryTheory.Functor.Category

/-! # Abstract whole-factor cancellation with two pushforward layers

All map composition is normalized on arbitrary categorical objects,
so the original geometric specialization contains no rewriting of its
native pullbacks, projection formula or canonical sheaf records.
-/
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
set_option autoImplicit false

theorem naturality_factor_comp_two
    {C : Type u₁} {D : Type u₂} {B : Type u₄} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₄} B] [Category.{v₃} E]
    (P : C ⥤ E) (R : C ⥤ D) (Q : D ⥤ B) (G : B ⥤ E)
    {M N : C} {Z : D} {W : B} (δ : M ⟶ N)
    (aM : P.obj M ⟶ G.obj (Q.obj (R.obj M)))
    (aN : P.obj N ⟶ G.obj (Q.obj (R.obj N)))
    (hn : P.map δ ≫ aN = aM ≫ G.map (Q.map (R.map δ)))
    (α : R.obj N ⟶ Z) (s : R.obj M ⟶ Z)
    (he : R.map δ ≫ α = s) (t : Q.obj Z ⟶ W) :
    P.map δ ≫ (aN ≫ G.map (Q.map α ≫ t)) = aM ≫ G.map (Q.map s ≫ t) := by
  calc
    _ = (P.map δ ≫ aN) ≫ G.map (Q.map α ≫ t) := by simp only [Category.assoc]
    _ = (aM ≫ G.map (Q.map (R.map δ))) ≫ G.map (Q.map α ≫ t) := by rw [hn]
    _ = aM ≫ G.map (Q.map (R.map δ ≫ α) ≫ t) := by
      simp only [G.map_comp, Q.map_comp, Category.assoc]
    _ = _ := by rw [he]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
