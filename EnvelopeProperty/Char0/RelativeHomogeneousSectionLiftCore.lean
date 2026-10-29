import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula

/-! # Actual adjunction units under line tensoring and evaluation -/

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u v w z

namespace EnvelopeProperty.Char0.RelativeHomogeneousSectionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Naturality transports the evaluated tensor-unit epimorphism along a genuine iso. -/
theorem unitTensor_epi_of_iso
    {C D A : Type u} [Category.{v} C] [Category.{v} D] [Category.{w} A]
    [MonoidalCategory C] (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (T : C ⥤ A) (L : C) {M N : C} (e : M ≅ N)
    [Epi (T.map ((adj.unit.app N) ▷ L))] :
    Epi (T.map ((adj.unit.app M) ▷ L)) := by
  have hs : (adj.unit.app M) ▷ L ≫ (G.map (F.map e.hom)) ▷ L =
      e.hom ▷ L ≫ (adj.unit.app N) ▷ L := by
    rw [← comp_whiskerRight, ← comp_whiskerRight]
    exact congrArg (fun f => f ▷ L) (adj.unit.naturality e.hom).symm
  have hc : Epi (T.map (((adj.unit.app M) ▷ L) ≫
      (G.map (F.map e.hom)) ▷ L)) := by
    rw [hs, T.map_comp]
    infer_instance
  rw [T.map_comp] at hc
  exact (epi_comp_iff_of_isIso _ _).mp hc

/-- Actual monoidal adjunction and a genuine tensor inverse transfer an evaluated
structure-unit epimorphism to the SAME original unit on the original line. -/
theorem lineUnit_epi_of_unitTensor
    {C D A : Type u} [Category.{v} C] [Category.{v} D] [Category.{w} A]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Monoidal]
    (T : C ⥤ A) (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C)
    [Epi (T.map ((adj.unit.app (𝟙_ C)) ▷ L))] :
    Epi (T.map (adj.unit.app L)) := by
  let E := SchemeInvertibleTensorEquivalence.rightTensorEquivalence L Q e
  let E' := SchemeInvertibleTensorEquivalence.rightTensorEquivalence (F.obj L) (F.obj Q)
    (Functor.Monoidal.μIso F L Q ≪≫ F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm)
  let adj₁ := E.symm.toAdjunction.comp adj
  let adj₂ := adj.comp E'.symm.toAdjunction
  let α := Functor.Monoidal.commTensorRight F Q
  let P := SchemeLineProjectionFormula.projectionFormulaOfTensorInverse F G adj L Q e
  let : Epi (T.map ((adj.unit.app (L ⊗ Q)) ▷ L)) :=
    unitTensor_epi_of_iso F G adj T L e
  have h₁ : Epi (T.map (adj₁.unit.app L)) := by
    dsimp only [adj₁]
    rw [Adjunction.comp_unit_app, T.map_comp]
    change Epi (T.map (E.symm.toAdjunction.unit.app L) ≫
      T.map ((adj.unit.app (L ⊗ Q)) ▷ L))
    infer_instance
  have hs : adj₁.unit.app L ≫ P.hom.app ((E.symm.functor ⋙ F).obj L) =
      adj₂.unit.app L ≫ (tensorRight (F.obj L) ⋙ G).map (α.hom.app L) :=
    unit_conjugateEquiv adj₁ adj₂ α.hom L
  have hc : Epi (T.map (adj₂.unit.app L ≫
      (tensorRight (F.obj L) ⋙ G).map (α.hom.app L))) := by
    rw [← hs, T.map_comp]
    let : Epi (T.map (adj₁.unit.app L)) := h₁
    infer_instance
  rw [T.map_comp] at hc
  have h₂ : Epi (T.map (adj₂.unit.app L)) :=
    (epi_comp_iff_of_isIso _ _).mp hc
  have h₂' : Epi (T.map (adj.unit.app L ≫
      G.map (E'.symm.toAdjunction.unit.app (F.obj L)))) := by
    simpa only [adj₂, Adjunction.comp_unit_app] using h₂
  rw [T.map_comp] at h₂'
  exact (epi_comp_iff_of_isIso _ _).mp h₂'

end EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
