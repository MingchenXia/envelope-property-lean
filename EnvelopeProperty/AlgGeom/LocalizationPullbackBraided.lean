import EnvelopeProperty.AlgGeom.MonoidalBraidedDescent
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Braiding for the existing monoidal localization descent -/
noncomputable section
namespace EnvelopeProperty.MonoidalBraidedDescent
open CategoryTheory MonoidalCategory
universe u v
set_option autoImplicit false

/-- Braiding descends to exactly `functorMonoidalOfComp`, using the existing
monoidal lifting isomorphism and essential surjectivity of localization. -/
@[implicit_reducible]
def localizationBraidedOfComp
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    [MonoidalCategory E] [BraidedCategory E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Braided]
    (F : D ⥤ E) (G : C ⥤ E) [G.Braided] [W.ContainsIdentities]
    [Localization.Lifting L W G F] :
    letI := Localization.Monoidal.functorMonoidalOfComp L W F G
    F.Braided := by
  letI := Localization.Monoidal.functorMonoidalOfComp L W F G
  let e := Localization.Lifting.iso L W G F
  haveI : e.hom.IsMonoidal := inferInstance
  haveI : e.symm.hom.IsMonoidal := inferInstanceAs (NatTrans.IsMonoidal e.inv)
  letI : L.EssSurj := Localization.essSurj L W
  letI : (L ⋙ F).LaxBraided := Functor.LaxBraided.ofNatIso e.symm
  exact {
    toMonoidal := Localization.Monoidal.functorMonoidalOfComp L W F G
    braided M N := by
      apply braided_of_essSurj L F ?_ M N
      intro X Y
      have h : Functor.LaxMonoidal.μ (L ⋙ F) X Y ≫
          (L ⋙ F).map (β_ X Y).hom =
          (β_ ((L ⋙ F).obj X) ((L ⋙ F).obj Y)).hom ≫
            Functor.LaxMonoidal.μ (L ⋙ F) Y X := by
        apply Functor.LaxBraided.braided
      simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj,
        Functor.comp_map, Category.assoc] using h }

end EnvelopeProperty.MonoidalBraidedDescent
