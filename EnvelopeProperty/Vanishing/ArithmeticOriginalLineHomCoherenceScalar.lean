import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerMorphisms
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Actual addition and structure-scalar action on original whole Hom sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
open ArithmeticOriginalLinePowerSections SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
attribute [local instance] Scheme.Modules.pullbackMonoidal

private theorem homEquiv_additive {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A)
    (B : X.Modules) (a b : A ⟶ B) :
    SchemeInvertibleHomSection.equiv A hA B (a + b) =
      SchemeInvertibleHomSection.equiv A hA B a + SchemeInvertibleHomSection.equiv A hA B b := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let : (tensorRight A).Additive := inferInstanceAs E.functor.Additive
  let adj : tensorRight A ⊣ tensorRight (dualObj A) := E.toAdjunction
  change (ModularCurves.monoidalUnitObjIso X).inv ≫
      adj.homEquiv _ _ ((λ_ A).hom ≫ (a + b)) ≫
        (ModularCurves.monoidalTensorObjIso B (dualObj A)).hom = _
  simp only [Preadditive.comp_add, Adjunction.homAddEquiv_add, Preadditive.add_comp]
  rfl

/-- The actual original whole Hom-section correspondence preserves addition. -/
theorem homSectionEquiv_add {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A)
    (B : X.Modules) (a b : A ⟶ B) :
    homSectionEquiv A hA B (a + b) = homSectionEquiv A hA B a + homSectionEquiv A hA B b := by
  change sectionAtOne (SchemeInvertibleHomSection.equiv A hA B (a + b)) = _
  rw [homEquiv_additive]
  rfl

/-- Its genuine original inverse preserves addition as well. -/
theorem homSectionEquiv_symm_add {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A)
    (B : X.Modules) (s t : Γ(homLine A B, ⊤)) :
    (homSectionEquiv A hA B).symm (s + t) =
      (homSectionEquiv A hA B).symm s + (homSectionEquiv A hA B).symm t := by
  apply (homSectionEquiv A hA B).injective
  rw [Equiv.apply_symm_apply, homSectionEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private def scalarAction {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) (r : 𝟙_ C ⟶ 𝟙_ C) : A ⟶ A :=
  (λ_ A).inv ≫ r ▷ A ≫ (λ_ A).hom

private theorem scalarAction_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {A B : C} (a : A ⟶ B) (r : 𝟙_ C ⟶ 𝟙_ C) :
    scalarAction A r ≫ a = a ≫ scalarAction B r := by
  dsimp only [scalarAction]
  rw [Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← Category.assoc (r ▷ A), ← MonoidalCategory.whisker_exchange,
    Category.assoc, ← Category.assoc (λ_ A).inv, ← leftUnitor_inv_naturality]
  simp only [Category.assoc]

private theorem scalarAction_map {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (A : C) (r : 𝟙_ C ⟶ 𝟙_ C) :
    F.map (scalarAction A r) = scalarAction (F.obj A)
      ((Functor.Monoidal.εIso F).hom ≫ F.map r ≫ (Functor.Monoidal.εIso F).inv) := by
  simp only [scalarAction, Functor.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.εIso_hom,
    Functor.Monoidal.εIso_inv, MonoidalCategory.comp_whiskerRight]

private theorem conjugate_pair {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {V M : C} {U W : D} (e : V ≅ M) (e0 : U ≅ F.obj V)
    (u : F.obj M ≅ W) (r : M ⟶ M) :
    e0.hom ≫ F.map (e.hom ≫ r ≫ e.inv) ≫ e0.inv =
      (e0 ≪≫ F.mapIso e ≪≫ u).hom ≫ (u.inv ≫ F.map r ≫ u.hom) ≫
        (e0 ≪≫ F.mapIso e ≪≫ u).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
private theorem iso_cancel {C : Type*} [Category C] {A B D : C} (e : A ≅ B) (j : A ≅ D) :
    e ≪≫ (e.symm ≪≫ j) = j := by simp
private theorem unitScalar_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫
      (Scheme.Modules.pullback f).map ((ModularCurves.monoidalUnitObjIso X).hom ≫
        ModularCurves.unitEndomorphismOfTopSection r ≫ (ModularCurves.monoidalUnitObjIso X).inv) ≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv =
      (ModularCurves.monoidalUnitObjIso Y).hom ≫
        ModularCurves.unitEndomorphismOfTopSection (f.appTop.hom r) ≫
        (ModularCurves.monoidalUnitObjIso Y).inv := by
  let F := Scheme.Modules.pullback f
  have hj : Functor.Monoidal.εIso F ≪≫ F.mapIso (ModularCurves.monoidalUnitObjIso X) ≪≫
      pullbackUnitIso f = ModularCurves.monoidalUnitObjIso Y := by
    have h := pullback_monoidalUnitObjIso f
    exact (congrArg (fun t => Functor.Monoidal.εIso F ≪≫ t) h.symm).trans (iso_cancel (Functor.Monoidal.εIso F) (ModularCurves.monoidalUnitObjIso Y))
  have hc := congrArg (fun j => j.hom ≫ ((pullbackUnitIso f).inv ≫
      F.map (ModularCurves.unitEndomorphismOfTopSection r) ≫ (pullbackUnitIso f).hom) ≫ j.inv) hj
  have hr := congrArg (fun z => (ModularCurves.monoidalUnitObjIso Y).hom ≫ z ≫
      (ModularCurves.monoidalUnitObjIso Y).inv)
    (ModularCurves.pullback_unitEndomorphismOfTopSection f r)
  exact (conjugate_pair F (ModularCurves.monoidalUnitObjIso X) (Functor.Monoidal.εIso F)
    (pullbackUnitIso f) (ModularCurves.unitEndomorphismOfTopSection r)).trans (hc.trans hr)

/-- The actual structure-line endomorphism acting on an entire original module. -/
def structureScalar {X : Scheme.{u}} (A : X.Modules) (r : Γ(X, ⊤)) : A ⟶ A :=
  scalarAction A ((ModularCurves.monoidalUnitObjIso X).hom ≫
    ModularCurves.unitEndomorphismOfTopSection r ≫ (ModularCurves.monoidalUnitObjIso X).inv)

/-- Multiplication of the actual whole Hom section is the actual source scalar action. -/
theorem homSectionEquiv_scalar {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A)
    (B : X.Modules) (r : Γ(X, ⊤)) (a : A ⟶ B) :
    homSectionEquiv A hA B (structureScalar A r ≫ a) = r • homSectionEquiv A hA B a := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let adj : tensorRight A ⊣ tensorRight (dualObj A) := E.toAdjunction
  let t := (ModularCurves.monoidalUnitObjIso X).hom ≫
    ModularCurves.unitEndomorphismOfTopSection r ≫ (ModularCurves.monoidalUnitObjIso X).inv
  have hn := adj.homEquiv_naturality_left t ((λ_ A).hom ≫ a)
  have he : SchemeInvertibleHomSection.equiv A hA B (structureScalar A r ≫ a) =
      ModularCurves.unitEndomorphismOfTopSection r ≫ SchemeInvertibleHomSection.equiv A hA B a := by
    change (ModularCurves.monoidalUnitObjIso X).inv ≫
        adj.homEquiv _ _ ((λ_ A).hom ≫
          ((λ_ A).inv ≫ t ▷ A ≫ (λ_ A).hom) ≫ a) ≫
          (ModularCurves.monoidalTensorObjIso B (dualObj A)).hom = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change (ModularCurves.monoidalUnitObjIso X).inv ≫
        adj.homEquiv _ _ ((tensorRight A).map t ≫ (λ_ A).hom ≫ a) ≫ _ = _
    rw [hn]
    dsimp only [t]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  change sectionAtOne (SchemeInvertibleHomSection.equiv A hA B (structureScalar A r ≫ a)) = _
  rw [he]
  change (SchemeInvertibleHomSection.equiv A hA B a).app ⊤
      ((ModularCurves.unitEndomorphismOfTopSection r).app ⊤ (1 : Γ(X, ⊤))) = _
  have hu : (ModularCurves.unitEndomorphismOfTopSection r).app ⊤ (1 : Γ(X, ⊤)) = r := by
    change 1 * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
    simp
  rw [hu]
  have hv := Scheme.Modules.Hom.app_smul (SchemeInvertibleHomSection.equiv A hA B a) r
    (1 : Γ(X, ⊤))
  have hr : r • (show Γ(unitObj X, ⊤) from (1 : Γ(X, ⊤))) = (r : Γ(unitObj X, ⊤)) := by
    change r * 1 = r
    exact mul_one r
  exact (congrArg (fun z : Γ(unitObj X, ⊤) =>
    (SchemeInvertibleHomSection.equiv A hA B a).app ⊤ z) hr.symm).trans hv

/-- The actual original source scalar action is natural for whole module maps. -/
theorem structureScalar_naturality {X : Scheme.{u}} {A B : X.Modules}
    (a : A ⟶ B) (r : Γ(X, ⊤)) : structureScalar A r ≫ a = a ≫ structureScalar B r :=
  scalarAction_naturality a _

/-- Whole native pullback retains the actual original structure-scalar action. -/
theorem structureScalar_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : X.Modules) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (structureScalar A r) =
      structureScalar ((Scheme.Modules.pullback f).obj A) (f.appTop.hom r) := by
  exact (scalarAction_map (Scheme.Modules.pullback f) A
    ((ModularCurves.monoidalUnitObjIso X).hom ≫
      ModularCurves.unitEndomorphismOfTopSection r ≫ (ModularCurves.monoidalUnitObjIso X).inv)).trans
    (congrArg (scalarAction ((Scheme.Modules.pullback f).obj A)) (unitScalar_pullback f r))

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
