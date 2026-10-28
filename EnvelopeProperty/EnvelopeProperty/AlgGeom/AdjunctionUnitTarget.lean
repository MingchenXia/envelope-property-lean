import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The explicit object target of an unchanged adjunction-unit equation

This is only a definitional typing adapter. The functors, adjunction,
unit and both original morphisms are unchanged.
-/
namespace EnvelopeProperty.AdjunctionUnitTarget
open CategoryTheory
universe u v
set_option autoImplicit false

/-- An equation indexed by `(F ⋙ G).obj M` also holds with its original
unit composite indexed explicitly by `G.obj (F.obj M)`. -/
theorem unit_composite_explicit_target
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) {A M : C}
    (r : A ⟶ M) (s : A ⟶ G.obj (F.obj M))
    (h : r ≫ adj.unit.app M = s) :
    CategoryStruct.comp (Z := G.obj (F.obj M)) r (adj.unit.app M) = s := by
  exact h

end EnvelopeProperty.AdjunctionUnitTarget
