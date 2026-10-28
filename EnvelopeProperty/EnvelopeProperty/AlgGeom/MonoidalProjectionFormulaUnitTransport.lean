import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaUnit

/-! # Transport of the original projection formula to actual unit objects -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open EnvelopeProperty.SchemeLineProjectionFormula
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]

/-- Left multiplication by an actual chosen representative of the tensor unit. -/
def transportedLeftUnit {U : C} (a : 𝟙_ C ≅ U) (L : C) : U ⊗ L ≅ L :=
  (a.symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L

/-- Transporting both unit representatives preserves the original projection
formula and the original adjunction unit. -/
theorem projectionFormulaOfTensorInverse_actual_unit
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Braided]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C)
    {U : C} {V : D} (a : 𝟙_ C ≅ U) (b : 𝟙_ D ≅ V)
    (t : F.obj U ≅ V)
    (ht : Functor.OplaxMonoidal.η F ≫ b.hom = F.map a.hom ≫ t.hom) :
    (transportedLeftUnit a L).inv ≫
      ((adj.unit.app U ≫ G.map t.hom) ▷ L) ≫
      (projectionFormulaOfTensorInverse F G adj L Q e).hom.app V ≫
      G.map (transportedLeftUnit b (F.obj L)).hom = adj.unit.app L := by
  let P := projectionFormulaOfTensorInverse F G adj L Q e
  have hu : a.hom ≫ (adj.unit.app U ≫ G.map t.hom) =
      (adj.unit.app (𝟙_ C) ≫ G.map (Functor.OplaxMonoidal.η F)) ≫ G.map b.hom := by
    have ha := adj.unit.naturality a.hom
    change a.hom ≫ adj.unit.app U =
      adj.unit.app (𝟙_ C) ≫ G.map (F.map a.hom) at ha
    rw [← Category.assoc, ha]
    simp only [Category.assoc, ← G.map_comp]
    rw [← ht]
  have hn := P.hom.naturality b.hom
  change (G.map b.hom ▷ L) ≫ P.hom.app V =
    P.hom.app (𝟙_ D) ≫ G.map (b.hom ▷ F.obj L) at hn
  simp only [transportedLeftUnit, Iso.trans_inv, Iso.trans_hom,
    MonoidalCategory.tensorIso_inv, MonoidalCategory.tensorIso_hom,
    Iso.symm_inv, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    MonoidalCategory.tensorHom_id]
  change ((λ_ L).inv ≫ a.hom ▷ L) ≫
      ((adj.unit.app U ≫ G.map t.hom) ▷ L) ≫ P.hom.app V ≫
      G.map ((b.inv ▷ F.obj L) ≫ (λ_ (F.obj L)).hom) = _
  simp only [Category.assoc, Functor.map_comp]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hu,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map b.hom ▷ L), hn]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight,
    b.hom_inv_id, MonoidalCategory.id_whiskerRight]
  erw [G.map_id]
  simp only [Category.id_comp]
  exact projectionFormulaOfTensorInverse_unit F G adj L Q e

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
