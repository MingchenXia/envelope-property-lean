/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Genuine actions on a specified original Cartesian square

The actual original pullback cone is retained exactly. Both full projection
maps and the original universal lift are equivariant for the derived action.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace EnvelopeProperty.PullbackConeMonoidAction

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [MonObj G] {P X Y S : C} [ModObj G X] [ModObj G Y] [ModObj G S]
  {f : X ⟶ S} {g : Y ⟶ S} [IsModHom G f] [IsModHom G g]
  {p : P ⟶ X} {q : P ⟶ Y} (h : IsPullback p q f g)

/-- The internally constructed whole action on the SAME specified original pullback. -/
def action : G ⊗ P ⟶ P :=
  h.lift ((G ◁ p) ≫ ModObj.smul (M := G) (X := X))
    ((G ◁ q) ≫ ModObj.smul (M := G) (X := Y)) (by
      have hf : ModObj.smul (M := G) (X := X) ≫ f =
          (G ◁ f) ≫ ModObj.smul (M := G) (X := S) :=
        IsModHom.smul_hom (A := G) (f := f)
      have hg : ModObj.smul (M := G) (X := Y) ≫ g =
          (G ◁ g) ≫ ModObj.smul (M := G) (X := S) :=
        IsModHom.smul_hom (A := G) (f := g)
      rw [Category.assoc, hf, ← whiskerLeft_comp_assoc, h.w,
        whiskerLeft_comp_assoc, ← hg, ← Category.assoc])

@[reassoc (attr := simp)]
theorem action_fst : action G h ≫ p = (G ◁ p) ≫ ModObj.smul (M := G) (X := X) :=
  h.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem action_snd : action G h ≫ q = (G ◁ q) ≫ ModObj.smul (M := G) (X := Y) :=
  h.lift_snd _ _ _

private theorem action_unit :
    (η[G] ▷ P) ≫ action G h = (λ_ P).hom := by
  apply h.hom_ext
  · rw [Category.assoc, action_fst, ← whisker_exchange_assoc,
      ModObj.one_smul_self, leftUnitor_naturality]
  · rw [Category.assoc, action_snd, ← whisker_exchange_assoc,
      ModObj.one_smul_self, leftUnitor_naturality]

private theorem action_mul :
    (μ[G] ▷ P) ≫ action G h =
      (α_ G G P).hom ≫ (G ◁ action G h) ≫ action G h := by
  apply h.hom_ext
  · simp only [Category.assoc, action_fst]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self,
      associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← action_fst G h, whiskerLeft_comp_assoc, action_fst]
  · simp only [Category.assoc, action_snd]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self,
      associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← action_snd G h, whiskerLeft_comp_assoc, action_snd]

/-- The genuine derived monoid action on the SAME original Cartesian-cone object. -/
@[instance_reducible]
def modObj : ModObj G P where
  smul := action G h
  one_smul := action_unit G h
  mul_smul := action_mul G h

/-- The entire original first projection is equivariant. -/
theorem fst_isModHom : letI := modObj G h; IsModHom G p := by
  let := modObj G h
  exact ⟨action_fst G h⟩

/-- The entire original second projection is equivariant. -/
theorem snd_isModHom : letI := modObj G h; IsModHom G q := by
  let := modObj G h
  exact ⟨action_snd G h⟩

/-- Equivariance into the SAME original pullback is detected by its two projections. -/
theorem isModHom_of_comp {T : C} [ModObj G T] (a : T ⟶ P)
    [IsModHom G (a ≫ p)] [IsModHom G (a ≫ q)] :
    letI := modObj G h
    IsModHom G a := by
  let := modObj G h
  constructor
  change ModObj.smul (M := G) (X := T) ≫ a = (G ◁ a) ≫ action G h
  apply h.hom_ext
  · simp only [Category.assoc, action_fst]
    rw [← whiskerLeft_comp_assoc]
    exact IsModHom.smul_hom (A := G) (f := a ≫ p)
  · simp only [Category.assoc, action_snd]
    rw [← whiskerLeft_comp_assoc]
    exact IsModHom.smul_hom (A := G) (f := a ≫ q)

/-- The original actual universal lift of equivariant maps is equivariant. -/
theorem lift_isModHom {T : C} [ModObj G T] (a : T ⟶ X) (b : T ⟶ Y)
    [IsModHom G a] [IsModHom G b] (hab : a ≫ f = b ≫ g) :
    letI := modObj G h
    IsModHom G (h.lift a b hab) := by
  let := modObj G h
  constructor
  change ModObj.smul (M := G) (X := T) ≫ h.lift a b hab =
    (G ◁ h.lift a b hab) ≫ action G h
  apply h.hom_ext
  · simp only [Category.assoc, h.lift_fst, action_fst]
    rw [← whiskerLeft_comp_assoc, h.lift_fst]
    exact IsModHom.smul_hom (A := G) (f := a)
  · simp only [Category.assoc, h.lift_snd, action_snd]
    rw [← whiskerLeft_comp_assoc, h.lift_snd]
    exact IsModHom.smul_hom (A := G) (f := b)

end EnvelopeProperty.PullbackConeMonoidAction
