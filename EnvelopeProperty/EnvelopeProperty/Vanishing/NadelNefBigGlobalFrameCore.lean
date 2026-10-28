import Mathlib.CategoryTheory.Monoidal.Functor
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe u v w z
namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalFrameCore
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  [MonoidalCategory C] [MonoidalCategory D]

theorem map_right_frame (F : C ⥤ D) [F.Monoidal] (M B : C) (b : B ⟶ 𝟙_ C) :
    (Functor.Monoidal.μIso F M B).inv ≫
        F.obj M ◁ (F.map b ≫ (Functor.Monoidal.εIso F).inv) ≫ (ρ_ (F.obj M)).hom =
      F.map (M ◁ b ≫ (ρ_ M).hom) := by
  apply (cancel_epi (Functor.Monoidal.μIso F M B).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  symm
  simp only [Functor.Monoidal.μIso_hom, Functor.map_comp, whiskerLeft_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality F M]
  simp only [← Category.assoc, ← whiskerLeft_comp]
  simp only [← Functor.Monoidal.εIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem tensor_frame_naturality {M N B : D} (p : M ⟶ N) (b : B ⟶ 𝟙_ D) :
    p ▷ B ≫ N ◁ b ≫ (ρ_ N).hom = M ◁ b ≫ (ρ_ M).hom ≫ p := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc, rightUnitor_naturality]

theorem map_right_frame_comp (F : C ⥤ D) [F.Monoidal] (M B : C) (N : D)
    (p : F.obj M ⟶ N) (b : B ⟶ 𝟙_ C) :
    (Functor.Monoidal.μIso F M B).inv ≫ p ▷ F.obj B ≫
        N ◁ (F.map b ≫ (Functor.Monoidal.εIso F).inv) ≫ (ρ_ N).hom =
      F.map (M ◁ b ≫ (ρ_ M).hom) ≫ p := by
  rw [tensor_frame_naturality]
  simpa only [Category.assoc] using congrArg (fun a => a ≫ p) (map_right_frame F M B b)
end EnvelopeProperty.Vanishing.NadelNefBigGlobalFrameCore
