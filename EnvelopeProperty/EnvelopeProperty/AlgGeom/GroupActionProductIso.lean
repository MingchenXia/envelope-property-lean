/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# The actual whole product isomorphism induced by a genuine group action

The actual group inverse and action laws give (g,x)↦(g,gx) and its
inverse on the whole product in every Cartesian monoidal category.
-/

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace EnvelopeProperty
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The actual whole product isomorphism of a genuine group action. -/
def actionProductIso (G X : C) [GrpObj G] [ModObj G X] : G ⊗ X ≅ G ⊗ X where
  hom := lift (fst G X) ((fst G X) • (snd G X))
  inv := lift (fst G X) ((fst G X)⁻¹ • (snd G X))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd, ModObj.comp_smul, Hom.inv_def,
        lift_fst_assoc, Category.id_comp]
      exact inv_smul_smul (fst G X) (snd G X)
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd, ModObj.comp_smul, lift_fst, Category.id_comp]
      exact smul_inv_smul (fst G X) (snd G X)

/-- The true group component of the whole action product isomorphism is unchanged. -/
theorem actionProductIso_fst (G X : C) [GrpObj G] [ModObj G X] :
    (actionProductIso G X).hom ≫ fst G X = fst G X :=
  lift_fst _ _

/-- The second component of the true whole product isomorphism is the actual
original group action morphism. -/
theorem actionProductIso_snd (G X : C) [GrpObj G] [ModObj G X] :
    (actionProductIso G X).hom ≫ snd G X = ModObj.smul (M := G) (X := X) := by
  simp [actionProductIso, Hom.smul_def]

end EnvelopeProperty
