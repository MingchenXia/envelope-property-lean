import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.EpiMono

/-! # Generic-target cancellation by an actual open pullback

This categorical lemma only uses the original adjunction hom equivalence
and the epimorphism of the actual mapped original arrow.
-/
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open CategoryTheory
universe u₁ u₂ v₁ v₂
set_option autoImplicit false

theorem hom_ext_of_map_epi
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B : C} (a : A ⟶ B) [Epi (F.map a)]
    {N : D} (f g : B ⟶ G.obj N) (h : a ≫ f = a ≫ g) : f = g := by
  apply (adj.homEquiv B N).symm.injective
  apply (cancel_epi (F.map a)).mp
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm, h]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
