import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Braiding of an actual monoidal left adjoint from its original right adjoint

The right-adjoint lax structure and the monoidal adjunction compatibility
are ordinary functor data. The proof does not manufacture that structure
from the desired braiding of the left adjoint.
-/
noncomputable section
namespace EnvelopeProperty.MonoidalAdjunctionBraided
open CategoryTheory CategoryTheory.MonoidalCategory
universe u v
set_option autoImplicit false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section Oplax
variable [F.OplaxMonoidal] [G.LaxBraided] [adj.IsMonoidal]

include adj in
/-- Braiding of the SAME actual oplax comparison follows by adjunction
from the original right-adjoint lax braiding and genuine unit compatibility. -/
theorem leftAdjoint_oplax_braiding (X Y : C) :
    F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply (adj.homEquiv _ _).injective
  change adj.unit.app (X ⊗ Y) ≫
      G.map (F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X) =
    adj.unit.app (X ⊗ Y) ≫
      G.map (Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
  calc
    _ = (β_ X Y).hom ≫ adj.unit.app (Y ⊗ X) ≫
        G.map (Functor.OplaxMonoidal.δ F Y X) := by
      simpa only [G.map_comp, Category.assoc] using
        congrArg (fun k => k ≫ G.map (Functor.OplaxMonoidal.δ F Y X))
          (adj.unit_naturality (β_ X Y).hom)
    _ = (β_ X Y).hom ≫
        ((adj.unit.app Y ⊗ₘ adj.unit.app X) ≫
          Functor.LaxMonoidal.μ G (F.obj Y) (F.obj X)) := by
      exact congrArg (fun k => (β_ X Y).hom ≫ k)
        (adj.unit_app_tensor_comp_map_δ Y X)
    _ = (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫
        (β_ (G.obj (F.obj X)) (G.obj (F.obj Y))).hom ≫
          Functor.LaxMonoidal.μ G (F.obj Y) (F.obj X) := by
      simpa only [Category.assoc, Functor.id_obj, Functor.comp_obj] using
        congrArg (fun k => k ≫ Functor.LaxMonoidal.μ G (F.obj Y) (F.obj X))
          (BraidedCategory.braiding_naturality (adj.unit.app X) (adj.unit.app Y)).symm
    _ = (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫
        Functor.LaxMonoidal.μ G (F.obj X) (F.obj Y) ≫
          G.map (β_ (F.obj X) (F.obj Y)).hom := by
      have h : Functor.LaxMonoidal.μ G (F.obj X) (F.obj Y) ≫
          G.map (β_ (F.obj X) (F.obj Y)).hom =
          (β_ (G.obj (F.obj X)) (G.obj (F.obj Y))).hom ≫
            Functor.LaxMonoidal.μ G (F.obj Y) (F.obj X) := by
        apply Functor.LaxBraided.braided
      exact congrArg (fun k => (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ k) h.symm
    _ = adj.unit.app (X ⊗ Y) ≫
        G.map (Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) := by
      simpa only [G.map_comp, Category.assoc] using
        congrArg (fun k => k ≫ G.map (β_ (F.obj X) (F.obj Y)).hom)
          (adj.unit_app_tensor_comp_map_δ X Y).symm

end Oplax

section Strong
variable [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal]

/-- The original strong monoidal left-adjoint structure is braided. -/
@[implicit_reducible]
def leftAdjointBraided : F.Braided where
  toMonoidal := inferInstance
  braided X Y := by
    apply (cancel_mono (Functor.OplaxMonoidal.δ F Y X)).1
    simpa only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id] using
      congrArg (fun k => Functor.LaxMonoidal.μ F X Y ≫ k)
        (leftAdjoint_oplax_braiding adj X Y)

/-- Adding the proof preserves the actual supplied monoidal structure literally. -/
theorem leftAdjointBraided_toMonoidal :
    (leftAdjointBraided adj).toMonoidal = (inferInstance : F.Monoidal) := rfl

end Strong

end EnvelopeProperty.MonoidalAdjunctionBraided
