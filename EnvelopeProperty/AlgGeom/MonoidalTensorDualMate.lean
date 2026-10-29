import EnvelopeProperty.AlgGeom.MonoidalInversePairUnitCoherence

/-! # The tensor-dual mate of the original tensor comparison

The braided hypothesis is essential here: the original inverse-tensor
equivalence uses the reversed evaluation containing the source braiding.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open EnvelopeProperty.SchemeInvertibleTensorEquivalence
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]

private theorem rightTensorInverse_unit (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) (X : C) :
    (rightTensorEquivalence L Q e).symm.toAdjunction.unit.app X =
      inversePairUnit X Q L ((β_ Q L) ≪≫ e) := by
  change ((ρ_ X).inv ≫ X ◁ ((β_ Q L) ≪≫ e).inv) ≫
    (α_ X Q L).inv = _
  exact Category.assoc _ _ _

private theorem mappedInversePair_braiding
    (F : C ⥤ D) [F.Braided] (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) :
    (β_ (F.obj Q) (F.obj L)) ≪≫ mappedInversePair F L Q e =
      mappedInversePair F Q L ((β_ Q L) ≪≫ e) := by
  apply Iso.ext
  simp only [mappedInversePair, Iso.trans_hom, Functor.mapIso_hom,
    Functor.Monoidal.μIso_hom, Iso.symm_hom]
  rw [← Functor.LaxBraided.braided_assoc]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- The inner mate in the existing inverse-tensor construction is the
inverse of the actual tensor comparison of the same functor. -/
theorem tensorDual_mate
    (F : C ⥤ D) [F.Braided] (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) :
    (mateEquiv
      (rightTensorEquivalence L Q e).symm.toAdjunction
      (rightTensorEquivalence (F.obj L) (F.obj Q)
        (mappedInversePair F L Q e)).symm.toAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F Q).hom)).natTrans =
        (Functor.Monoidal.commTensorRight F L).inv := by
  let E := rightTensorEquivalence L Q e
  let E' := rightTensorEquivalence (F.obj L) (F.obj Q) (mappedInversePair F L Q e)
  let m : tensorRight L ⋙ F ⟶ F ⋙ tensorRight (F.obj L) :=
    (mateEquiv E.symm.toAdjunction E'.symm.toAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F Q).hom)).natTrans
  have h (X : C) : m.app (X ⊗ Q) =
      (Functor.Monoidal.commTensorRight F L).inv.app (X ⊗ Q) := by
    apply (cancel_epi (F.map (E.symm.toAdjunction.unit.app X))).mp
    have hm : F.map (E.symm.toAdjunction.unit.app X) ≫ m.app (X ⊗ Q) =
        E'.symm.toAdjunction.unit.app (F.obj X) ≫
          Functor.LaxMonoidal.μ F X Q ▷ F.obj L :=
      unit_mateEquiv E.symm.toAdjunction E'.symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (Functor.Monoidal.commTensorRight F Q).hom) X
    rw [hm]
    change E'.symm.toAdjunction.unit.app (F.obj X) ≫
        Functor.LaxMonoidal.μ F X Q ▷ F.obj L =
      F.map (E.symm.toAdjunction.unit.app X) ≫
        Functor.OplaxMonoidal.δ F (X ⊗ Q) L
    dsimp only [E, E']
    rw [rightTensorInverse_unit, rightTensorInverse_unit,
      mappedInversePair_braiding]
    exact (map_inversePairUnit F X Q L ((β_ Q L) ≪≫ e)).symm
  change m = _
  ext A
  let i : (A ⊗ L) ⊗ Q ≅ A := E.symm.counitIso.app A
  apply (cancel_epi ((tensorRight L ⋙ F).map i.hom)).mp
  have hm := m.naturality i.hom
  change (tensorRight L ⋙ F).map i.hom ≫ m.app A =
    m.app ((A ⊗ L) ⊗ Q) ≫ (F ⋙ tensorRight (F.obj L)).map i.hom at hm
  rw [h] at hm
  exact hm.trans ((Functor.Monoidal.commTensorRight F L).inv.naturality i.hom).symm

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
