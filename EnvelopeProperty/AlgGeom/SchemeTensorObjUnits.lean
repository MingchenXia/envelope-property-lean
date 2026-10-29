import EnvelopeProperty.AlgGeom.SchemeTensorObjMorphisms

/-! # The SAME original explicit tensor right unit and native monoidal unit -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeTensorObjMorphisms

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The ORIGINAL explicit tensor right unit equals the SAME native
monoidal right unit through the genuine original tensor/structure-unit
comparisons, on the ENTIRE original module. -/
theorem tensorObjUnitIso_monoidal (M : X.Modules) :
    (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.unitObj X)).hom ≫
        (Scheme.Modules.tensorObjUnitIso M).hom =
      M ◁ (ModularCurves.monoidalUnitObjIso X).inv ≫ (ρ_ M).hom := by
  let : (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _)
  let : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _)).Monoidal
    infer_instance
  let eM : F.obj M.val ≅ M := Scheme.Modules.sheafifyValIso M
  let eU : F.obj (Scheme.Modules.unitObj X).val ≅ Scheme.Modules.unitObj X :=
    Scheme.Modules.sheafifyValIso (Scheme.Modules.unitObj X)
  have hk : (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.unitObj X)).inv =
      Functor.OplaxMonoidal.δ F M.val (Scheme.Modules.unitObj X).val ≫
        (eM.hom ⊗ₘ eU.hom) := by
    rfl
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.unitObj X)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  rw [hk]
  have hr := Functor.LaxMonoidal.right_unitality F M.val
  have hn : eM.hom ▷ (𝟙_ X.Modules) ≫ (ρ_ M).hom =
      (ρ_ (F.obj M.val)).hom ≫ eM.hom := rightUnitor_naturality eM.hom
  change (Scheme.Modules.tensorObjUnitIso M).hom =
    (Functor.OplaxMonoidal.δ F M.val (Scheme.Modules.unitObj X).val ≫
      (eM.hom ⊗ₘ eU.hom)) ≫ M ◁ eU.inv ≫ (ρ_ M).hom
  simp only [tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  change (Scheme.Modules.tensorObjUnitIso M).hom =
    Functor.OplaxMonoidal.δ F M.val (Scheme.Modules.unitObj X).val ≫
      eM.hom ▷ (𝟙_ X.Modules) ≫ (ρ_ M).hom
  rw [hn]
  change (Scheme.Modules.tensorObjUnitIso M).hom =
    Functor.OplaxMonoidal.δ F M.val (Scheme.Modules.unitObj X).val ≫
      (ρ_ (F.obj M.val)).hom ≫ eM.hom
  rw [hr]
  have heps : Functor.LaxMonoidal.ε F = 𝟙 (𝟙_ X.Modules) := rfl
  simp only [heps, whiskerLeft_id, Category.id_comp, Category.assoc]
  change (Scheme.Modules.tensorObjUnitIso M).hom =
    Functor.OplaxMonoidal.δ F M.val (𝟙_ X.PresheafOfModules) ≫
      Functor.LaxMonoidal.μ F M.val (𝟙_ X.PresheafOfModules) ≫ F.map (ρ_ M.val).hom ≫ eM.hom
  rw [Functor.Monoidal.δ_μ_assoc]
  rfl

end
end EnvelopeProperty.SchemeTensorObjMorphisms
