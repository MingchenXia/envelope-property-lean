import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativePowerUnitCompatibility

/-! # Actual original structure multiplication and true native scheme pullback -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u v w z
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Native genuine monoidal left-unit law derives the whole actual unit-multiplication diagram. -/
theorem originalMonoidalUnitMultiplication {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] :
    Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom ≫
        (Functor.Monoidal.εIso F).inv =
      ((Functor.Monoidal.εIso F).inv ⊗ₘ (Functor.Monoidal.εIso F).inv) ≫ (λ_ (𝟙_ D)).hom := by
  have hu : Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom =
      (Functor.Monoidal.εIso F).inv ▷ F.obj (𝟙_ C) ≫ (λ_ (F.obj (𝟙_ C))).hom := by
    rw [Functor.LaxMonoidal.left_unitality]
    simp only [← Functor.Monoidal.εIso_hom, ← Category.assoc, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  calc
    _ = (Functor.Monoidal.εIso F).inv ▷ F.obj (𝟙_ C) ≫
        (λ_ (F.obj (𝟙_ C))).hom ≫ (Functor.Monoidal.εIso F).inv := by
      simpa only [Category.assoc] using congrArg (fun a => a ≫ (Functor.Monoidal.εIso F).inv) hu
    _ = (Functor.Monoidal.εIso F).inv ▷ F.obj (𝟙_ C) ≫
        (𝟙_ D) ◁ (Functor.Monoidal.εIso F).inv ≫ (λ_ (𝟙_ D)).hom := by
      rw [← leftUnitor_naturality]
    _ = _ := by rw [MonoidalCategory.tensorHom_def, Category.assoc]

/-- TRUE original native scheme pullback preserves SAME coherent structure multiplication. -/
theorem originalPullbackUnitTensorIso_hom {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    letI : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
    letI : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
    letI : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
    (Functor.Monoidal.μIso (pullback f) (unitObj Z) (unitObj Z)).hom ≫
        (pullback f).map (ModularCurves.unitObjTensorIso Z).hom ≫ (pullbackUnitIso f).hom =
      ((pullbackUnitIso f).hom ⊗ₘ (pullbackUnitIso f).hom) ≫ (ModularCurves.unitObjTensorIso Y).hom := by
  let : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  let : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
  let : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  let F := pullback f
  let uZ := ModularCurves.monoidalUnitObjIso Z
  let uY := ModularCurves.monoidalUnitObjIso Y
  have hx : (uZ.hom ⊗ₘ uZ.hom) ≫ (ModularCurves.unitObjTensorIso Z).hom =
      (λ_ (𝟙_ Z.Modules)).hom ≫ uZ.hom := by
    simp only [uZ, ModularCurves.unitObjTensorIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
      ← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]
  have hy : (uY.hom ⊗ₘ uY.hom) ≫ (ModularCurves.unitObjTensorIso Y).hom =
      (λ_ (𝟙_ Y.Modules)).hom ≫ uY.hom := by
    simp only [uY, ModularCurves.unitObjTensorIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
      ← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]
  have hu : F.map uZ.hom ≫ (pullbackUnitIso f).hom =
      (Functor.Monoidal.εIso F).inv ≫ uY.hom := by
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, F, uZ, uY] using
      congrArg Iso.hom (originalPullbackUnitIso_monoidal f)
  have hfm : F.map (uZ.hom ⊗ₘ uZ.hom) ≫ F.map (ModularCurves.unitObjTensorIso Z).hom =
      F.map (λ_ (𝟙_ Z.Modules)).hom ≫ F.map uZ.hom := by
    rw [← F.map_comp, hx, F.map_comp]
  have hl : (F.map uZ.hom ⊗ₘ F.map uZ.hom) ≫
        Functor.LaxMonoidal.μ F (unitObj Z) (unitObj Z) ≫
          F.map (ModularCurves.unitObjTensorIso Z).hom ≫ (pullbackUnitIso f).hom =
      ((Functor.Monoidal.εIso F).inv ⊗ₘ (Functor.Monoidal.εIso F).inv) ≫
        (λ_ (𝟙_ Y.Modules)).hom ≫ uY.hom := by
    calc
      _ = Functor.LaxMonoidal.μ F (𝟙_ Z.Modules) (𝟙_ Z.Modules) ≫
          F.map (λ_ (𝟙_ Z.Modules)).hom ≫ (F.map uZ.hom ≫ (pullbackUnitIso f).hom) := by
        rw [← Category.assoc (F.map uZ.hom ⊗ₘ F.map uZ.hom)
          (Functor.LaxMonoidal.μ F (unitObj Z) (unitObj Z)), Functor.LaxMonoidal.μ_natural]
        simp only [Category.assoc]
        rw [← Category.assoc (F.map (uZ.hom ⊗ₘ uZ.hom))
          (F.map (ModularCurves.unitObjTensorIso Z).hom) (pullbackUnitIso f).hom, hfm]
        simp only [Category.assoc]
      _ = _ := by
        rw [hu]
        simpa only [Category.assoc] using congrArg (fun a => a ≫ uY.hom)
          (originalMonoidalUnitMultiplication F)
  have hr : (F.map uZ.hom ⊗ₘ F.map uZ.hom) ≫
        ((pullbackUnitIso f).hom ⊗ₘ (pullbackUnitIso f).hom) ≫ (ModularCurves.unitObjTensorIso Y).hom =
      ((Functor.Monoidal.εIso F).inv ⊗ₘ (Functor.Monoidal.εIso F).inv) ≫
        (λ_ (𝟙_ Y.Modules)).hom ≫ uY.hom := by
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [hu]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hy]
  apply (cancel_epi (F.map uZ.hom ⊗ₘ F.map uZ.hom)).mp
  simpa only [Category.assoc, Functor.Monoidal.μIso_hom, F] using hl.trans hr.symm

/-- The SAME original explicit structure multiplication commutes with actual original scheme pullback. -/
theorem originalBundleTensorUnitIso_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (pullback f).mapIso (bundleTensorLeftUnitIso (unitObj Z)) ≪≫ pullbackUnitIso f =
      canonicalTensorPullbackIso f (unitObj Z) (unitObj Z) ≪≫
        tensorObjCongr (pullbackUnitIso f) (pullbackUnitIso f) ≪≫ bundleTensorLeftUnitIso (unitObj Y) := by
  let : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  let : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
  let : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  let F := pullback f
  let kZ := ModularCurves.monoidalTensorObjIso (unitObj Z) (unitObj Z)
  let kF := ModularCurves.monoidalTensorObjIso (F.obj (unitObj Z)) (F.obj (unitObj Z))
  let e := Functor.Monoidal.μIso F (unitObj Z) (unitObj Z) ≪≫ F.mapIso kZ
  have hc : canonicalTensorPullbackIso f (unitObj Z) (unitObj Z) = e.symm ≪≫ kF := rfl
  have hl : e.hom ≫ F.map (bundleTensorLeftUnitIso (unitObj Z)).hom ≫ (pullbackUnitIso f).hom =
      (Functor.Monoidal.μIso F (unitObj Z) (unitObj Z)).hom ≫
        F.map (ModularCurves.unitObjTensorIso Z).hom ≫ (pullbackUnitIso f).hom := by
    change (Functor.Monoidal.μIso F (unitObj Z) (unitObj Z)).hom ≫ F.map kZ.hom ≫
      F.map (bundleTensorLeftUnitIso (unitObj Z)).hom ≫ (pullbackUnitIso f).hom = _
    rw [← Category.assoc (F.map kZ.hom) (F.map (bundleTensorLeftUnitIso (unitObj Z)).hom)
      (pullbackUnitIso f).hom, ← F.map_comp, originalBundleTensorUnitIso_monoidal]
  have hr : e.hom ≫ (canonicalTensorPullbackIso f (unitObj Z) (unitObj Z) ≪≫
        tensorObjCongr (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
          bundleTensorLeftUnitIso (unitObj Y)).hom =
      ((pullbackUnitIso f).hom ⊗ₘ (pullbackUnitIso f).hom) ≫ (ModularCurves.unitObjTensorIso Y).hom := by
    rw [hc]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc kF.hom (tensorObjCongr (pullbackUnitIso f) (pullbackUnitIso f)).hom
      (bundleTensorLeftUnitIso (unitObj Y)).hom,
      ModularCurves.cartierMonoidalTensorObjIso_hom_natural]
    simp only [Category.assoc]
    rw [originalBundleTensorUnitIso_monoidal]
  apply Iso.ext
  apply (cancel_epi e.hom).mp
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    hl.trans ((originalPullbackUnitTensorIso_hom f).trans hr.symm)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
