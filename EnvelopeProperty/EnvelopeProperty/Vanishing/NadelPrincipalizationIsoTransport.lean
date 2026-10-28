import Mathlib.CategoryTheory.EqToHom

/-! # A genuine isomorphism retaining its proved whole original homomorphism -/

open CategoryTheory
universe u v
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationIsoTransport

variable {C : Type u} [Category.{v} C] {A B : C}

/-- Keep a proved actual forward map literally as the hom field. -/
def withHom (e : A ≅ B) (f : A ⟶ B) (hf : f = e.hom) : A ≅ B where
  hom := f
  inv := e.inv
  hom_inv_id := by rw [hf, e.hom_inv_id]
  inv_hom_id := by rw [hf, e.inv_hom_id]

/-- No reduction of geometric isomorphism inverses is needed to read back
the entire original forward morphism. -/
theorem withHom_hom (e : A ≅ B) (f : A ⟶ B) (hf : f = e.hom) :
    (withHom e f hf).hom = f := rfl

/-- Transport the target of a genuine isomorphism while retaining the
proved original whole forward map literally in the hom field. -/
def targetWithHom (e : A ≅ B) (f : A ⟶ B) (hf : f = e.hom) {B' : C} (t : B = B') : A ≅ B' where
  hom := f ≫ eqToHom t
  inv := eqToHom t.symm ≫ e.inv
  hom_inv_id := by
    subst B'
    simpa only [eqToHom_refl, Category.comp_id, Category.id_comp, hf] using e.hom_inv_id
  inv_hom_id := by
    subst B'
    simpa only [eqToHom_refl, Category.comp_id, Category.id_comp, hf] using e.inv_hom_id

/-- The actual forward map and actual target equality are retained as
an equality of entire morphisms, without reducing geometric inverses. -/
theorem targetWithHom_hom (e : A ≅ B) (f : A ⟶ B) (hf : f = e.hom) {B' : C} (t : B = B') :
    (targetWithHom e f hf t).hom = f ≫ eqToHom t := rfl

end EnvelopeProperty.Vanishing.NadelPrincipalizationIsoTransport
