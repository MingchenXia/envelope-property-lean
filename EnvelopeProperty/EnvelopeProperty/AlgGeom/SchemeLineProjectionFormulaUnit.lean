import EnvelopeProperty.AlgGeom.MonoidalTensorDualMate

/-! # Unit normalization of the original inverse-tensor projection formula -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open EnvelopeProperty.SchemeInvertibleTensorEquivalence
open EnvelopeProperty.SchemeLineProjectionFormula
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]

private theorem projectionFormulaOfTensorInverse_mate
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Braided]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) :
    (projectionFormulaOfTensorInverse F G adj L Q e).hom =
      (mateEquiv adj adj
        (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F L).inv)).natTrans := by
  let E := rightTensorEquivalence L Q e
  let E' := rightTensorEquivalence (F.obj L) (F.obj Q) (mappedInversePair F L Q e)
  have hi := iterated_mateEquiv_conjugateEquiv
    E.symm.toAdjunction E'.symm.toAdjunction adj adj
    (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F Q).hom)
  change conjugateEquiv (E.symm.toAdjunction.comp adj)
    (adj.comp E'.symm.toAdjunction) (Functor.Monoidal.commTensorRight F Q).hom = _
  rw [← hi]
  exact congrArg (fun α : tensorRight L ⋙ F ⟶ F ⋙ tensorRight (F.obj L) =>
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ α)).natTrans) (tensorDual_mate F L Q e)

/-- The strong unit formula for the same original conjugate projection
formula, before specializing its original module to the tensor unit. -/
theorem projectionFormulaOfTensorInverse_unit_tensor
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Braided]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) (A : C) :
    (adj.unit.app A ▷ L) ≫ (projectionFormulaOfTensorInverse F G adj L Q e).hom.app
        (F.obj A) =
      adj.unit.app (A ⊗ L) ≫ G.map (Functor.OplaxMonoidal.δ F A L) := by
  rw [projectionFormulaOfTensorInverse_mate]
  exact unit_mateEquiv adj adj
    (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F L).inv) A

/-- The original inverse-tensor projection formula carries its actual
categorical structure unit to the actual adjunction unit of the line. -/
theorem projectionFormulaOfTensorInverse_unit
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Braided]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) :
    (λ_ L).inv ≫
      ((adj.unit.app (𝟙_ C) ≫ G.map (Functor.OplaxMonoidal.η F)) ▷ L) ≫
      (projectionFormulaOfTensorInverse F G adj L Q e).hom.app (𝟙_ D) ≫
      G.map (λ_ (F.obj L)).hom = adj.unit.app L := by
  let P := projectionFormulaOfTensorInverse F G adj L Q e
  have hn := P.hom.naturality (Functor.OplaxMonoidal.η F)
  change (G.map (Functor.OplaxMonoidal.η F) ▷ L) ≫ P.hom.app (𝟙_ D) =
    P.hom.app (F.obj (𝟙_ C)) ≫
      G.map (Functor.OplaxMonoidal.η F ▷ F.obj L) at hn
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← Category.assoc (G.map (Functor.OplaxMonoidal.η F) ▷ L), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (adj.unit.app (𝟙_ C) ▷ L),
    projectionFormulaOfTensorInverse_unit_tensor]
  simp only [Category.assoc, ← G.map_comp]
  rw [Functor.OplaxMonoidal.left_unitality_hom]
  have hu := adj.unit.naturality (λ_ L).hom
  change (λ_ L).hom ≫ adj.unit.app L =
    adj.unit.app (𝟙_ C ⊗ L) ≫ G.map (F.map (λ_ L).hom) at hu
  rw [← hu]
  simp

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
