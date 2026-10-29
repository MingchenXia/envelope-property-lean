import EnvelopeProperty.AlgGeom.SchemeTensorObjUnits
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # Genuine original tensor-ideal interchange -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeTensorObjMorphisms

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalIdealShuffleNaturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (B I D : C) (i : I ⟶ 𝟙_ C) :
    ((B ◁ i) ≫ (ρ_ B).hom) ▷ D =
      (α_ B I D).hom ≫ B ◁ (β_ I D).hom ≫ (α_ B D I).inv ≫
        (B ⊗ D) ◁ i ≫ (ρ_ (B ⊗ D)).hom := by
  rw [← associator_inv_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    ← BraidedCategory.braiding_naturality_left]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_middle_assoc]
  have hc : (α_ B (𝟙_ C) D).hom ≫ B ◁ (β_ (𝟙_ C) D).hom ≫
      (α_ B D (𝟙_ C)).inv ≫ (ρ_ (B ⊗ D)).hom = (ρ_ B).hom ▷ D := by
    rw [braiding_tensorUnit_left]
    monoidal_coherence
  simpa only [Category.assoc, comp_whiskerRight] using
    congrArg (fun t ↦ (B ◁ i) ▷ D ≫ t) hc.symm

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
noncomputable local instance : SymmetricCategory X.Modules := Scheme.Modules.symmetricCategory X

/-- Tensor the SAME original module-to-structure morphism and use the
ORIGINAL explicit right unitor, retaining the ENTIRE original map. -/
def tensorObjIdealMap (B I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) :
    Scheme.Modules.tensorObj B I ⟶ B :=
  tensorObjMap (𝟙 B) i ≫ (Scheme.Modules.tensorObjUnitIso B).hom

/-- The ORIGINAL explicit map retains the SAME native monoidal inclusion,
with the genuine original tensor and structure-unit comparisons. -/
theorem tensorObjIdealMap_monoidal (B I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) :
    (ModularCurves.monoidalTensorObjIso B I).hom ≫ tensorObjIdealMap B I i =
      B ◁ (i ≫ (ModularCurves.monoidalUnitObjIso X).inv) ≫ (ρ_ B).hom := by
  have hn := tensorObjMap_monoidal (𝟙 B) i
  have ht : (ModularCurves.monoidalTensorObjIso B I).hom ≫ tensorObjMap (𝟙 B) i =
      (B ◁ i) ≫ (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.unitObj X)).hom := by
    apply (cancel_mono (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.unitObj X)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hn, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      MonoidalCategory.id_tensorHom]
  unfold tensorObjIdealMap
  rw [← Category.assoc, ht, Category.assoc, tensorObjUnitIso_monoidal,
    ← whiskerLeft_comp_assoc]

/-- The actual explicit sheafified tensor shuffle, using SAME original
tensor comparisons, genuine associators and original braiding. -/
def tensorObjIdealShuffleIso (B I D : X.Modules) :
    Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B I) D ≅
      Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B D) I :=
  (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B I) D).symm ≪≫
    ((ModularCurves.monoidalTensorObjIso B I).symm ⊗ᵢ Iso.refl D) ≪≫
    (α_ B I D) ≪≫ whiskerLeftIso B (β_ I D) ≪≫ (α_ B D I).symm ≪≫
    ((ModularCurves.monoidalTensorObjIso B D) ⊗ᵢ Iso.refl I) ≪≫
    (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B D) I)

/-- The SAME actual explicit tensor-ideal shuffle retains the ENTIRE
original inclusion after tensoring by the original module, with no
invertibility, ideal matching or compatibility premise. -/
theorem tensorObjIdealShuffleIso_inclusion (B I D : X.Modules)
    (i : I ⟶ Scheme.Modules.unitObj X) :
    tensorObjMap (tensorObjIdealMap B I i) (𝟙 D) =
      (tensorObjIdealShuffleIso B I D).hom ≫ tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i := by
  let eS : (B ⊗ I) ⊗ D ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B I) D :=
    ((ModularCurves.monoidalTensorObjIso B I) ⊗ᵢ Iso.refl D) ≪≫
      ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B I) D
  let eT : (B ⊗ D) ⊗ I ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B D) I :=
    ((ModularCurves.monoidalTensorObjIso B D) ⊗ᵢ Iso.refl I) ≪≫
      ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B D) I
  let s : (B ⊗ I) ⊗ D ≅ (B ⊗ D) ⊗ I :=
    (α_ B I D) ≪≫ whiskerLeftIso B (β_ I D) ≪≫ (α_ B D I).symm
  let j := i ≫ (ModularCurves.monoidalUnitObjIso X).inv
  have hshuffle : eS.hom ≫ (tensorObjIdealShuffleIso B I D).hom = s.hom ≫ eT.hom := by
    dsimp only [eS, eT, s, tensorObjIdealShuffleIso]
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
      Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
      Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  have hl : eS.hom ≫ tensorObjMap (tensorObjIdealMap B I i) (𝟙 D) ≫
      (ModularCurves.monoidalTensorObjIso B D).inv = (B ◁ j ≫ (ρ_ B).hom) ▷ D := by
    dsimp only [eS]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc]
    change (ModularCurves.monoidalTensorObjIso B I).hom ▷ D ≫
      (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B I) D).hom ≫
      tensorObjMap (tensorObjIdealMap B I i) (𝟙 D) ≫
      (ModularCurves.monoidalTensorObjIso B D).inv = _
    rw [tensorObjMap_monoidal, Iso.hom_inv_id_assoc, tensorHom_id,
      ← comp_whiskerRight, tensorObjIdealMap_monoidal]
  have hr : eT.hom ≫ tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i ≫
      (ModularCurves.monoidalTensorObjIso B D).inv =
        (B ⊗ D) ◁ j ≫ (ρ_ (B ⊗ D)).hom := by
    dsimp only [eT]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc]
    change (ModularCurves.monoidalTensorObjIso B D).hom ▷ I ≫
      (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B D) I).hom ≫
      tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i ≫
      (ModularCurves.monoidalTensorObjIso B D).inv = _
    rw [← Category.assoc (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B D) I).hom
      (tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i)
      (ModularCurves.monoidalTensorObjIso B D).inv, tensorObjIdealMap_monoidal]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
    simp only [Iso.hom_inv_id, Category.comp_id]
    rfl
  apply (cancel_epi eS.hom).mp
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso B D).inv).mp
  calc
    _ = (B ◁ j ≫ (ρ_ B).hom) ▷ D := hl
    _ = s.hom ≫ ((B ⊗ D) ◁ j ≫ (ρ_ (B ⊗ D)).hom) :=
      originalIdealShuffleNaturality B I D j
    _ = (s.hom ≫ eT.hom) ≫ tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i ≫
        (ModularCurves.monoidalTensorObjIso B D).inv := by rw [Category.assoc, hr]
    _ = _ := by rw [← hshuffle]; simp only [Category.assoc]

end
end EnvelopeProperty.SchemeTensorObjMorphisms
