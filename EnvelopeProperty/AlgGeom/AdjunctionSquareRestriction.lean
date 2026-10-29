import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Extracting a restriction square through its original adjunction

This is the ordinary hom-set equivalence for the unchanged functors and
adjunction. Its applications keep the actual native unit and counit.
-/
namespace EnvelopeProperty.AdjunctionSquareRestriction
open CategoryTheory
universe u v
set_option autoImplicit false

/-- Applying the SAME adjunction to a native unit equation gives its
restriction equation with the original counit. -/
theorem square_of_unit_square
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    {S M : C} {A N : D} (r : S ⟶ M) (a : F.obj M ⟶ N)
    (u : S ⟶ G.obj A) (t : A ⟶ N)
    (h : r ≫ (adj.homEquiv M N) a = u ≫ G.map t) :
    F.map r ≫ a = F.map u ≫ adj.counit.app A ≫ t := by
  have hi := congrArg ((adj.homEquiv S N).symm) h
  rw [adj.homEquiv_naturality_left_symm r ((adj.homEquiv M N) a),
    Equiv.symm_apply_apply, adj.homEquiv_naturality_right_symm u t,
    adj.homEquiv_symm_apply] at hi
  exact hi.trans (Category.assoc _ _ _)

end EnvelopeProperty.AdjunctionSquareRestriction
