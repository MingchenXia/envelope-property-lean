import EnvelopeProperty.AlgGeom.SchemeUnitScalarAction
import EnvelopeProperty.AlgGeom.PushforwardUnitSections
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # SAME entire original scalar action under actual native pullback -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace EnvelopeProperty.SchemeUnitScalarActionBaseChange
universe u v w z
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual pulled ORIGINAL structure-unit endomorphism is the SAME
original section morphism of the true original pulled global function. -/
theorem sectionHom_pullback_unit (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map
          (SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj X) a) ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj Y) (f.appTop a) := by
  let F := Scheme.Modules.pullback f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let u := Scheme.Modules.pullbackUnitIso f
  let r := SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj X) a
  let s := SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj Y) (f.appTop a)
  have hs : F.map r ≫ u.hom = u.hom ≫ s := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left,
      Scheme.Modules.pullbackUnitIso_hom_homEquiv,
      Scheme.Modules.pushforwardUnitSection_homEquiv]
    apply SheafOfModules.hom_ext
    ext U
    change f.app U.unop ((1 : Γ(X, U.unop)) * X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) =
      f.app U.unop (1 : Γ(X, U.unop)) * Y.presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ U.unop ≤ ⊤)).op (f.appTop a)
    rw [map_mul]
    congr 1
    have hn := f.naturality (homOfLE (le_top : U.unop ≤ ⊤)).op
    exact ConcreteCategory.congr_hom hn a
  change u.inv ≫ F.map r ≫ u.hom = s
  rw [hs]
  simp only [Iso.inv_hom_id_assoc]

private theorem originalUnitActionFunctor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (M : C) (r : 𝟙_ C ⟶ 𝟙_ C) :
    F.map ((λ_ M).inv ≫ r ▷ M ≫ (λ_ M).hom) =
      (λ_ (F.obj M)).inv ≫
        ((Functor.Monoidal.εIso F).hom ≫ F.map r ≫
          (Functor.Monoidal.εIso F).inv) ▷ F.obj M ≫ (λ_ (F.obj M)).hom := by
  simp only [Functor.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_leftUnitor, Functor.Monoidal.map_whiskerRight,
    comp_whiskerRight, Category.assoc]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rfl

private noncomputable instance scalarBaseChangeMonoidalCategory (W : Scheme.{u}) :
    MonoidalCategory W.Modules := Scheme.Modules.monoidalCategory W
private noncomputable instance scalarBaseChangeMonoidal {W Z : Scheme.{u}} (g : Z ⟶ W) :
    (Scheme.Modules.pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

private theorem originalUnitActionNative {W : Scheme.{u}} (M : W.Modules)
    (r : Scheme.Modules.unitObj W ⟶ Scheme.Modules.unitObj W) :
    SchemeUnitScalarAction.unitAction M r = (λ_ M).inv ≫
      ((ModularCurves.monoidalUnitObjIso W).hom ≫ r ≫
        (ModularCurves.monoidalUnitObjIso W).inv) ▷ M ≫ (λ_ M).hom := by
  dsimp only [SchemeUnitScalarAction.unitAction, SchemeTensorUnitSections.leftUnitIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc, comp_whiskerRight]

private theorem originalUnitSquare :
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv ≫
        (ModularCurves.monoidalUnitObjIso Y).hom =
      (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by
  exact congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso f)

/-- Pullback of the ENTIRE original unit action is conjugation by the
TRUE original native structure-unit pullback comparison, for ANY original map. -/
theorem unitAction_pullback (M : X.Modules)
    (r : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X) :
    (Scheme.Modules.pullback f).map (SchemeUnitScalarAction.unitAction M r) =
      SchemeUnitScalarAction.unitAction ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map r ≫
          (Scheme.Modules.pullbackUnitIso f).hom) := by
  let F := Scheme.Modules.pullback f
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  let u := Scheme.Modules.pullbackUnitIso f
  have hs := originalUnitSquare f
  change (Functor.Monoidal.εIso F).inv ≫ uY.hom = F.map uX.hom ≫ u.hom at hs
  have hleft : (Functor.Monoidal.εIso F).hom ≫ F.map uX.hom = uY.hom ≫ u.inv := by
    apply (cancel_mono u.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hs]
    simp only [Iso.hom_inv_id_assoc]
  have hright : F.map uX.inv ≫ (Functor.Monoidal.εIso F).inv = u.hom ≫ uY.inv := by
    apply (cancel_epi (F.map uX.hom)).mp
    simp only [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]
    rw [← hs]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : (Functor.Monoidal.εIso F).hom ≫ F.map (uX.hom ≫ r ≫ uX.inv) ≫
      (Functor.Monoidal.εIso F).inv =
      uY.hom ≫ (u.inv ≫ F.map r ≫ u.hom) ≫ uY.inv := by
    simp only [F.map_comp, Category.assoc]
    rw [← Category.assoc (Functor.Monoidal.εIso F).hom (F.map uX.hom), hleft]
    rw [hright]
    simp only [Category.assoc]
  rw [originalUnitActionNative, originalUnitActionNative, originalUnitActionFunctor]
  exact congrArg (fun t => (λ_ (F.obj M)).inv ≫ t ▷ F.obj M ≫ (λ_ (F.obj M)).hom) he

/-- The SAME original whole scalar action by an original global function
pulls back to the SAME true original pulled function's entire action. -/
theorem globalScalarAction_pullback (M : X.Modules) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (SchemeUnitScalarAction.globalScalarAction M a) =
      SchemeUnitScalarAction.globalScalarAction ((Scheme.Modules.pullback f).obj M)
        (f.appTop a) := by
  rw [SchemeUnitScalarAction.globalScalarAction, unitAction_pullback,
    sectionHom_pullback_unit]
  rfl

end
end EnvelopeProperty.SchemeUnitScalarActionBaseChange
