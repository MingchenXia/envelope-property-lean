import EnvelopeProperty.AlgGeom.InvertibleSheafBaseIdeal

/-! # The actual localized tensor unit acts on the whole original section module -/

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.SchemeTensorUnitSections
attribute [local instance] Scheme.Modules.monoidalCategory
open Scheme.Modules ModularCurves

def leftUnitIso {X : Scheme.{u}} (M : X.Modules) : unitObj X ⊗ M ≅ M :=
  whiskerRightIso (monoidalUnitObjIso X).symm M ≪≫ λ_ M

private theorem unit_pair_coherence {C : Type*} [Category C] [MonoidalCategory C]
    {A M N : C} (e : 𝟙_ C ≅ A) (f : M ⟶ N) :
    (e.hom ⊗ₘ f) ≫ (e.inv ▷ N) ≫ (λ_ N).hom = (λ_ M).hom ≫ f := by
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id, Category.comp_id, id_tensorHom, leftUnitor_naturality]

private theorem tensor_comparison_leftUnit {X : Scheme.{u}} (M : X.Modules) :
    (monoidalTensorObjIso (unitObj X) M).inv ≫ (leftUnitIso M).hom =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (λ_ M.val).hom ≫ (Scheme.Modules.sheafifyValIso M).hom := by
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
  let c := monoidalUnitObjIso X
  let d := Scheme.Modules.sheafifyValIso M
  have hcancel :
      (monoidalTensorObjIso (unitObj X) M).inv ≫ (leftUnitIso M).hom =
        Functor.OplaxMonoidal.δ F (unitObj X).val M.val ≫
          (λ_ (F.obj M.val)).hom ≫ d.hom := by
    change (Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) (unitObj X).val M.val).inv ≫
        (c.hom ⊗ₘ d.hom) ≫ (c.inv ▷ M) ≫ (λ_ M).hom = _
    rw [unit_pair_coherence]
    rfl
  rw [hcancel]
  change Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
    (λ_ (F.obj M.val)).hom ≫ d.hom = F.map (λ_ M.val).hom ≫ d.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := rfl
  simpa only [heta, id_whiskerRight, Category.id_comp] using
    Functor.OplaxMonoidal.left_unitality_hom_assoc F M.val d.hom

/-- The genuine native left-unit comparison evaluates EVERY original pure
tensor on EVERY original open, with no chosen frame or matching premise. -/
theorem leftUnitIso_hom_tensorSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (a : Γ(X, U)) (m : Γ(M, U)) :
    (leftUnitIso M).hom.val.app (.op U)
      (tensorSection (unitObj X) M U a m) = a • m := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let q : ((unitObj X).val ⊗ M.val).obj (.op U) := a ⊗ₜ m
  let uq := (adj.unit.app ((unitObj X).val ⊗ M.val)).app (.op U) q
  have hmor := tensor_comparison_leftUnit M
  have hmorU := congrArg (fun k => k.val.app (.op U)) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorU uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hmorApply
  change (leftUnitIso M).hom.val.app (.op U)
    ((monoidalTensorObjIso (unitObj X) M).inv.val.app (.op U) uq) = _
  rw [hmorApply]
  let f := (λ_ M.val).hom
  let c := Scheme.Modules.sheafifyValIso M
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components M
  change adj.unit.app ((unitObj X).val ⊗ M.val) ≫ (L.map f).val =
    f ≫ adj.unit.app M.val at hnat
  change adj.unit.app M.val ≫ c.hom.val = 𝟙 M.val at htri
  have hpre : adj.unit.app ((unitObj X).val ⊗ M.val) ≫
      (L.map f).val ≫ c.hom.val = f := by
    rw [← Category.assoc, hnat, Category.assoc, htri, Category.comp_id]
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (.op U)) hpre) q
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hp
  dsimp only [uq]
  change c.hom.val.app (.op U) ((L.map f).val.app (.op U)
    ((adj.unit.app ((unitObj X).val ⊗ M.val)).app (.op U) q)) = a • m
  have h := ConcreteCategory.congr_hom (PresheafOfModules.leftUnitor_hom_app M.val (.op U)) q
  exact hp.trans (h.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply
    (R := X.sheaf.obj.obj (.op U)) (M := ModuleCat.of (X.sheaf.obj.obj (.op U))
      (M.val.obj (.op U))) a m))

/-- The SAME morphism used in the original base ideal evaluates the SAME
original global section against EVERY original local dual section. -/
theorem sectionEvaluation_apply {X : Scheme.{u}} (L : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (d : Γ(dualObj L, U)) :
    (InvertibleSheafBaseIdeal.sectionEvaluation L s).val.app (.op U) d =
      SheafOfModules.evalSection X.ringCatSheaf L U d
        (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  let D : X.Modules := dualObj L
  let e := leftUnitIso D
  let σ := SchemeModuleGlobalSections.sectionHom L s
  let t := tensorSection (unitObj X) D U (1 : Γ(X, U)) d
  have hunit : e.hom.val.app (.op U) t = d := by
    exact (leftUnitIso_hom_tensorSection D U 1 d).trans (one_smul _ _)
  have hinv : e.inv.val.app (.op U) d = t := by
    exact (congrArg (fun z => e.inv.val.app (.op U) z) hunit.symm).trans
      (Scheme.Modules.iso_hom_inv_app_applyT e (.op U) t)
  have hmap : (σ ▷ D).val.app (.op U) t =
      tensorSection L D U (σ.val.app (.op U) (show Γ(X, U) from 1)) d := by
    have h := tensorSection_map σ (𝟙 D) U (show Γ(X, U) from 1) d
    rw [tensorHom_id] at h
    have hid : (𝟙 D : D ⟶ D).val.app (.op U) d = d := rfl
    exact h.trans (congrArg
      (tensorSection L D U (σ.val.app (.op U) (show Γ(X, U) from 1))) hid)
  have hsection : σ.val.app (.op U) (show Γ(X, U) from 1) =
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
    change (1 : Γ(X, U)) •
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = _
    exact one_smul _ _
  change (dualPairing L).val.app (.op U)
    ((σ ▷ D).val.app (.op U) (e.inv.val.app (.op U) d)) = _
  exact (congrArg (fun z => (dualPairing L).val.app (.op U)
      ((σ ▷ D).val.app (.op U) z)) hinv).trans
    ((congrArg (fun z => (dualPairing L).val.app (.op U) z) hmap).trans
      ((dualPairing_tensorSection L U
          (σ.val.app (.op U) (show Γ(X, U) from 1)) d).trans
        (congrArg (SheafOfModules.evalSection X.ringCatSheaf L U d) hsection)))

end EnvelopeProperty.SchemeTensorUnitSections
