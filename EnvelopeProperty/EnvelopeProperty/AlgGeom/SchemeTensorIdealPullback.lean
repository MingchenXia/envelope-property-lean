import EnvelopeProperty.AlgGeom.SchemeTensorIdealShuffle
import EnvelopeProperty.AlgGeom.IdealModuleOpenRestriction
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # SAME whole tensor-ideal inclusions under actual native pullback -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace EnvelopeProperty.SchemeTensorIdealPullback
universe u v w z
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalRightIdealFunctor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (B I : C) (i : I ⟶ 𝟙_ C) :
    Functor.LaxMonoidal.μ F B I ≫ F.map (B ◁ i ≫ (ρ_ B).hom) =
      F.obj B ◁ (F.map i ≫ (Functor.Monoidal.εIso F).inv) ≫ (ρ_ (F.obj B)).hom := by
  simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality F B]
  simp only [← Category.assoc, ← whiskerLeft_comp]
  simp only [← Functor.Monoidal.εIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private noncomputable instance tensorIdealPullbackMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
private noncomputable instance tensorIdealPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual native monoidal pullback and SAME original explicit tensor
comparisons construct the WHOLE original explicit tensor pullback isomorphism. -/
def tensorObjPullbackIso (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj M N) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N ≪≫
    (Scheme.Modules.pullback f).mapIso (ModularCurves.monoidalTensorObjIso M N)).symm ≪≫
      ModularCurves.monoidalTensorObjIso ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)

private theorem originalPullbackUnitSquare :
    (Scheme.Modules.pullbackUnitIso f).hom ≫ (ModularCurves.monoidalUnitObjIso Y).inv =
      (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).inv ≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv := by
  let F := Scheme.Modules.pullback f
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  have h := congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso f)
  change (Functor.Monoidal.εIso F).inv ≫ uY.hom = F.map uX.hom ≫
    (Scheme.Modules.pullbackUnitIso f).hom at h
  apply (cancel_epi (F.map uX.hom)).mp
  change F.map uX.hom ≫ (Scheme.Modules.pullbackUnitIso f).hom ≫ uY.inv =
    F.map uX.hom ≫ F.map uX.inv ≫ (Functor.Monoidal.εIso F).inv
  rw [← Category.assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- The SAME entire explicit tensor-to-structure inclusion pulls back
with the TRUE original native unit comparison, for EVERY original morphism. -/
theorem tensorObjIdealMap_pullback (B I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) :
    (Scheme.Modules.pullback f).map (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) =
      (tensorObjPullbackIso f B I).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback f).obj B)
          ((Scheme.Modules.pullback f).obj I)
          ((Scheme.Modules.pullback f).map i ≫ (Scheme.Modules.pullbackUnitIso f).hom) := by
  let F := Scheme.Modules.pullback f
  let eX := ModularCurves.monoidalTensorObjIso B I
  let eY := ModularCurves.monoidalTensorObjIso (F.obj B) (F.obj I)
  let e := Functor.Monoidal.μIso F B I ≪≫ F.mapIso eX
  have hX := SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I i
  have hY := SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal (F.obj B) (F.obj I)
    (F.map i ≫ (Scheme.Modules.pullbackUnitIso f).hom)
  have hF := originalRightIdealFunctor F B I (i ≫ (ModularCurves.monoidalUnitObjIso X).inv)
  have hs : e.hom ≫ F.map (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) =
      eY.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (F.obj B) (F.obj I)
        (F.map i ≫ (Scheme.Modules.pullbackUnitIso f).hom) := by
    change Functor.LaxMonoidal.μ F B I ≫ F.map eX.hom ≫ F.map _ = _
    rw [← F.map_comp, hX, hY]
    rw [hF]
    simp only [F.map_comp, Category.assoc]
    rw [originalPullbackUnitSquare f]
  apply (cancel_epi e.hom).mp
  change e.hom ≫ F.map _ = e.hom ≫ (e.inv ≫ eY.hom) ≫ _
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hs

private theorem originalTensorIdealMapComp {W : Scheme.{u}}
    (B : W.Modules) {I J : W.Modules} (a : I ⟶ J) (j : J ⟶ Scheme.Modules.unitObj W) :
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B J j =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I (a ≫ j) := by
  let eI := ModularCurves.monoidalTensorObjIso B I
  let eJ := ModularCurves.monoidalTensorObjIso B J
  have hMap := SchemeTensorObjMorphisms.tensorObjMap_monoidal (𝟙 B) a
  have ht : eI.hom ≫ SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a =
      B ◁ a ≫ eJ.hom := by
    apply (cancel_mono eJ.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      MonoidalCategory.id_tensorHom]
  apply (cancel_epi eI.hom).mp
  rw [← Category.assoc, ht, Category.assoc,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B J j,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I (a ≫ j)]
  simp only [← whiskerLeft_comp_assoc, Category.assoc]

/-- The SAME actual original ideal comap and its genuine native module
comparison give the actual whole tensor-ideal pullback isomorphism on an open immersion. -/
def idealTensorOpenPullbackIso [IsOpenImmersion f] (B : X.Modules) (J : X.IdealSheafData) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj B J.toModules) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj B) (J.comap f).toModules :=
  tensorObjPullbackIso f B J.toModules ≪≫
    Scheme.Modules.tensorObjCongr (Iso.refl _) (J.openPullbackModuleIso f)

/-- The ENTIRE SAME original ideal-tensor inclusion commutes with actual
original open pullback and the SAME genuine geometric ideal comap. -/
theorem idealTensorOpenPullbackIso_inclusion [IsOpenImmersion f]
    (B : X.Modules) (J : X.IdealSheafData) :
    (idealTensorOpenPullbackIso f B J).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback f).obj B)
          (J.comap f).toModules (J.comap f).toModulesInclusion =
      (Scheme.Modules.pullback f).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap B J.toModules J.toModulesInclusion) := by
  let F := Scheme.Modules.pullback f
  let i : J.toModules ⟶ Scheme.Modules.unitObj X := J.toModulesInclusion
  let i' : (J.comap f).toModules ⟶ Scheme.Modules.unitObj Y := (J.comap f).toModulesInclusion
  let e := J.openPullbackModuleIso f
  have hJ : e.hom ≫ i' = F.map i ≫ (Scheme.Modules.pullbackUnitIso f).hom :=
    J.toModulesComapPullbackMap_inclusion f
  have hc := originalTensorIdealMapComp (F.obj B) e.hom i'
  have hF := tensorObjIdealMap_pullback f B J.toModules i
  change (tensorObjPullbackIso f B J.toModules).hom ≫
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 (F.obj B)) e.hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap (F.obj B) (J.comap f).toModules i' = _
  rw [hc, hJ]
  exact hF.symm

end
end EnvelopeProperty.SchemeTensorIdealPullback
