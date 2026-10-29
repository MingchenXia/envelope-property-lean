import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The actual transported inverse-pair unit

These are categorical coherence producers for the existing projection
formula, not an alternative choice of projection isomorphism.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [MonoidalCategory D]

/-- The actual inverse-pair evaluation transported by the given monoidal
functor.  This is the same construction used by the original projection formula. -/
def mappedInversePair (F : C ⥤ D) [F.Monoidal]
    (Q L : C) (e : Q ⊗ L ≅ 𝟙_ C) : F.obj Q ⊗ F.obj L ≅ 𝟙_ D :=
  Functor.Monoidal.μIso F Q L ≪≫ F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm

/-- The literal raw unit of the inverse right-tensor equivalence. -/
def inversePairUnit (X Q L : C) (e : Q ⊗ L ≅ 𝟙_ C) : X ⟶ (X ⊗ Q) ⊗ L :=
  (ρ_ X).inv ≫ X ◁ e.inv ≫ (α_ X Q L).inv

private theorem mappedInversePair_inv_comp_tensorator
    (F : C ⥤ D) [F.Monoidal] (Q L : C) (e : Q ⊗ L ≅ 𝟙_ C) :
    (mappedInversePair F Q L e).inv ≫ Functor.LaxMonoidal.μ F Q L =
      Functor.LaxMonoidal.ε F ≫ F.map e.inv := by
  simp only [mappedInversePair, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.Monoidal.εIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.δ_μ, Category.comp_id]

/-- The given monoidal functor carries the actual inverse-pair unit
through its actual tensor comparison. -/
theorem map_inversePairUnit
    (F : C ⥤ D) [F.Monoidal] (X Q L : C) (e : Q ⊗ L ≅ 𝟙_ C) :
    F.map (inversePairUnit X Q L e) ≫ Functor.OplaxMonoidal.δ F (X ⊗ Q) L =
      inversePairUnit (F.obj X) (F.obj Q) (F.obj L) (mappedInversePair F Q L e) ≫
        Functor.LaxMonoidal.μ F X Q ▷ F.obj L := by
  apply (cancel_mono (Functor.LaxMonoidal.μ F (X ⊗ Q) L)).mp
  simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  dsimp only [inversePairUnit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.associativity_inv]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    mappedInversePair_inv_comp_tensorator, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
