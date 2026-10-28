import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.EssentialImage

/-! # Descent of braiding through an essentially surjective braided functor

The comparison maps in every conclusion belong to the supplied actual strong
monoidal structures. The composite law is used as a mathematical equality;
no replacement monoidal structure on either functor is chosen.
-/
noncomputable section
namespace EnvelopeProperty.MonoidalBraidedDescent
open CategoryTheory MonoidalCategory
universe u v
set_option autoImplicit false

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    [MonoidalCategory E] [BraidedCategory E]
    (L : C ⥤ D) (F : D ⥤ E) [L.Braided] [L.EssSurj] [F.Monoidal]

/-- Braiding of the actual tensor comparison is invariant under isomorphisms
of the two input objects. -/
theorem braiding_of_iso {M N M' N' : D} (e : M ≅ M') (e' : N ≅ N')
    (h : Functor.LaxMonoidal.μ F M N ≫ F.map (β_ M N).hom =
      (β_ (F.obj M) (F.obj N)).hom ≫ Functor.LaxMonoidal.μ F N M) :
    Functor.LaxMonoidal.μ F M' N' ≫ F.map (β_ M' N').hom =
      (β_ (F.obj M') (F.obj N')).hom ≫ Functor.LaxMonoidal.μ F N' M' := by
  apply (cancel_epi (F.map e.hom ⊗ₘ F.map e'.hom)).1
  calc
    _ = Functor.LaxMonoidal.μ F M N ≫
        F.map (β_ M N).hom ≫ F.map (e'.hom ⊗ₘ e.hom) := by
      rw [← Category.assoc, Functor.LaxMonoidal.μ_natural,
        Category.assoc, ← F.map_comp, BraidedCategory.braiding_naturality,
        F.map_comp]
    _ = (β_ (F.obj M) (F.obj N)).hom ≫
        Functor.LaxMonoidal.μ F N M ≫ F.map (e'.hom ⊗ₘ e.hom) := by
      rw [← Category.assoc, h, Category.assoc]
    _ = _ := by
      rw [← Functor.LaxMonoidal.μ_natural,
        ← BraidedCategory.braiding_naturality_assoc]

/-- Descent of the explicit braided composite law to the original functor. -/
theorem braided_of_essSurj
    (h : ∀ X Y : C,
      Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫
          F.map (Functor.LaxMonoidal.μ L X Y) ≫ F.map (L.map (β_ X Y).hom) =
        (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
          Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X) ≫
            F.map (Functor.LaxMonoidal.μ L Y X)) (M N : D) :
    Functor.LaxMonoidal.μ F M N ≫ F.map (β_ M N).hom =
      (β_ (F.obj M) (F.obj N)).hom ≫ Functor.LaxMonoidal.μ F N M := by
  apply braiding_of_iso F (L.objObjPreimageIso M) (L.objObjPreimageIso N)
  apply (cancel_mono (F.map (Functor.LaxMonoidal.μ L
    (L.objPreimage N) (L.objPreimage M)))).1
  have hL : Functor.LaxMonoidal.μ L (L.objPreimage M) (L.objPreimage N) ≫
      L.map (β_ (L.objPreimage M) (L.objPreimage N)).hom =
      (β_ (L.obj (L.objPreimage M)) (L.obj (L.objPreimage N))).hom ≫
        Functor.LaxMonoidal.μ L (L.objPreimage N) (L.objPreimage M) := by
    apply Functor.LaxBraided.braided
  have hc := h (L.objPreimage M) (L.objPreimage N)
  rw [← F.map_comp, hL, F.map_comp] at hc
  simpa only [Category.assoc] using hc

end EnvelopeProperty.MonoidalBraidedDescent
