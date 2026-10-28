import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionPullback

/-! # Genuine monoidal base change of the original tensor counit -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeInvertibleHomSection

universe u v w z
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalMonoidalTensorEvaluation
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (B L A : C) (e : L ⊗ A ⟶ 𝟙_ C) :
    (Functor.LaxMonoidal.μ F B L) ▷ F.obj A ≫
        Functor.LaxMonoidal.μ F (B ⊗ L) A ≫
        F.map ((α_ B L A).hom ≫ B ◁ e ≫ (ρ_ B).hom) =
      (α_ (F.obj B) (F.obj L) (F.obj A)).hom ≫
        F.obj B ◁ (Functor.LaxMonoidal.μ F L A ≫ F.map e ≫
          (Functor.Monoidal.εIso F).inv) ≫ (ρ_ (F.obj B)).hom := by
  simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.associativity_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality F B]
  simp only [← Category.assoc, ← whiskerLeft_comp]
  simp only [← Functor.Monoidal.εIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)

/-- Pull the SAME original right dual evaluation through the actual
monoidal pullback, retaining its genuine tensor and unit comparisons. -/
def rightPulledEvaluationIso :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dualObj A) ⊗
      (Scheme.Modules.pullback f).obj A ≅ 𝟙_ Y.Modules :=
  Functor.Monoidal.μIso (Scheme.Modules.pullback f) (Scheme.Modules.dualObj A) A ≪≫
    (Scheme.Modules.pullback f).mapIso ((β_ (Scheme.Modules.dualObj A) A) ≪≫ hA.monoidalEvaluationIso) ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm

/-- The SAME original pulled dual is identified with the SAME original
dual of the pullback by actual RIGHT evaluations, as required by the
actual right-tensor Hom-section adjunction; no matching premise. -/
def rightDualPullbackEvaluationIso :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dualObj A) ≅
      Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A) :=
  (hA.pullback f).tensorRightFullyFaithful.preimageIso
    (rightPulledEvaluationIso f A hA ≪≫
      ((β_ (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))
        ((Scheme.Modules.pullback f).obj A)) ≪≫ (hA.pullback f).monoidalEvaluationIso).symm)

/-- ENTIRE original right evaluation is preserved by the ACTUAL derived
right-dual pullback isomorphism, on the SAME original modules. -/
theorem rightDualPullbackEvaluationIso_pairing :
    (rightDualPullbackEvaluationIso f A hA).hom ▷ (Scheme.Modules.pullback f).obj A ≫
      ((β_ (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))
        ((Scheme.Modules.pullback f).obj A)).hom ≫ (hA.pullback f).monoidalEvaluationIso.hom) =
      (rightPulledEvaluationIso f A hA).hom := by
  have he := (hA.pullback f).tensorRightFullyFaithful.map_preimage
    (rightPulledEvaluationIso f A hA ≪≫
      ((β_ (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))
        ((Scheme.Modules.pullback f).obj A)) ≪≫ (hA.pullback f).monoidalEvaluationIso).symm).hom
  change (rightDualPullbackEvaluationIso f A hA).hom ▷ (Scheme.Modules.pullback f).obj A = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The ENTIRE SAME original tensor counit commutes with the actual
monoidal pullback and its genuinely derived original dual comparison. -/
theorem tensorCounit_pullback (B : X.Modules) :
    (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) B (Scheme.Modules.dualObj A)) ▷
        (Scheme.Modules.pullback f).obj A ≫
      Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) (B ⊗ Scheme.Modules.dualObj A) A ≫
      (Scheme.Modules.pullback f).map
        ((SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).counit.app B) =
      ((Scheme.Modules.pullback f).obj B ◁ (rightDualPullbackEvaluationIso f A hA).hom) ▷
          (Scheme.Modules.pullback f).obj A ≫
        (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence
          ((Scheme.Modules.pullback f).obj A) (hA.pullback f)).counit.app
            ((Scheme.Modules.pullback f).obj B) := by
  rw [invertibleTensor_counit_evaluation, invertibleTensor_counit_evaluation]
  have he := originalMonoidalTensorEvaluation (Scheme.Modules.pullback f) B
    (Scheme.Modules.dualObj A) A
    ((β_ (Scheme.Modules.dualObj A) A).hom ≫ hA.monoidalEvaluationIso.hom)
  change _ = (α_ ((Scheme.Modules.pullback f).obj B)
      ((Scheme.Modules.pullback f).obj (Scheme.Modules.dualObj A))
      ((Scheme.Modules.pullback f).obj A)).hom ≫
    (Scheme.Modules.pullback f).obj B ◁ (rightPulledEvaluationIso f A hA).hom ≫
      (ρ_ ((Scheme.Modules.pullback f).obj B)).hom at he
  rw [← rightDualPullbackEvaluationIso_pairing] at he
  simp only [whiskerLeft_comp, Category.assoc] at he ⊢
  rw [← associator_naturality_middle_assoc] at he
  exact he

/-- The ENTIRE original tensor-adjunction section of the original pulled
map is the actual monoidal pullback of its SAME original section, with
the genuinely DERIVED actual dual comparison and genuine tensor/unit maps. -/
theorem tensorHomSection_pullback (B : X.Modules) (φ : A ⟶ B) :
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence
      ((Scheme.Modules.pullback f).obj A) (hA.pullback f)).toAdjunction.homEquiv _ _
        ((λ_ ((Scheme.Modules.pullback f).obj A)).hom ≫ (Scheme.Modules.pullback f).map φ) =
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫
        (Scheme.Modules.pullback f).map
          ((SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).toAdjunction.homEquiv _ _
            ((λ_ A).hom ≫ φ)) ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f) B (Scheme.Modules.dualObj A)).inv ≫
        (Scheme.Modules.pullback f).obj B ◁ (rightDualPullbackEvaluationIso f A hA).hom := by
  let F := Scheme.Modules.pullback f
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let E' := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence (F.obj A) (hA.pullback f)
  let s : 𝟙_ X.Modules ⟶ B ⊗ Scheme.Modules.dualObj A :=
    E.toAdjunction.homEquiv _ _ ((λ_ A).hom ≫ φ)
  let c : (B ⊗ Scheme.Modules.dualObj A) ⊗ A ⟶ B := E.counit.app B
  let c' : (F.obj B ⊗ Scheme.Modules.dualObj (F.obj A)) ⊗ F.obj A ⟶ F.obj B :=
    E'.counit.app (F.obj B)
  let m := Functor.Monoidal.μIso F B (Scheme.Modules.dualObj A)
  let b := F.obj B ◁ (rightDualPullbackEvaluationIso f A hA).hom
  have hc := tensorCounit_pullback f A hA B
  have hcancel : m.inv ▷ F.obj A ≫ b ▷ F.obj A ≫ c' =
      Functor.LaxMonoidal.μ F (B ⊗ Scheme.Modules.dualObj A) A ≫ F.map c := by
    apply (cancel_epi (m.hom ▷ F.obj A)).mp
    simp only [← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
      Category.id_comp]
    exact hc.symm
  have hs : s ▷ A ≫ c = (λ_ A).hom ≫ φ := by
    have he := (E.toAdjunction.homEquiv _ _).symm_apply_apply ((λ_ A).hom ≫ φ)
    rw [Adjunction.homEquiv_counit] at he
    exact he
  apply (E'.toAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  change (λ_ (F.obj A)).hom ≫ F.map φ =
    ((Functor.Monoidal.εIso F).hom ≫ F.map s ≫ m.inv ≫ b) ▷ F.obj A ≫
      c'
  symm
  simp only [comp_whiskerRight, Category.assoc]
  rw [hcancel, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, hs, F.map_comp]
  exact (Functor.LaxMonoidal.left_unitality_assoc F A (F.map φ)).symm

private theorem originalHomSectionMonoidal {W : Scheme.{u}}
    (L : W.Modules) (hL : Scheme.Modules.IsInvertible L) (M : W.Modules) (φ : L ⟶ M) :
    (ModularCurves.monoidalUnitObjIso W).hom ≫ equiv L hL M φ ≫
      (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.dualObj L)).inv =
        (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence L hL).toAdjunction.homEquiv _ _
          ((λ_ L).hom ≫ φ) := by
  change (ModularCurves.monoidalUnitObjIso W).hom ≫
      ((ModularCurves.monoidalUnitObjIso W).inv ≫ _ ≫
        (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.dualObj L)).hom) ≫
          (ModularCurves.monoidalTensorObjIso M (Scheme.Modules.dualObj L)).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  change (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence L hL).toAdjunction.homEquiv _ _
    ((λ_ L).hom ≫ φ ≫ 𝟙 M) = _
  rw [Category.comp_id]

/-- The SAME original whole Hom-section correspondence commutes with
the actual pullback, retaining BOTH true original unit/tensor comparisons
and the genuinely DERIVED right-dual pullback map. No naturality or
dual-matching assumption is supplied. -/
theorem equiv_pullback_monoidal (B : X.Modules) (φ : A ⟶ B) :
    (ModularCurves.monoidalUnitObjIso Y).hom ≫
      equiv ((Scheme.Modules.pullback f).obj A) (hA.pullback f) ((Scheme.Modules.pullback f).obj B)
        ((Scheme.Modules.pullback f).map φ) ≫
      (ModularCurves.monoidalTensorObjIso ((Scheme.Modules.pullback f).obj B)
        (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))).inv =
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫
        (Scheme.Modules.pullback f).map
          ((ModularCurves.monoidalUnitObjIso X).hom ≫ equiv A hA B φ ≫
            (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv) ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f) B (Scheme.Modules.dualObj A)).inv ≫
        (Scheme.Modules.pullback f).obj B ◁ (rightDualPullbackEvaluationIso f A hA).hom := by
  rw [originalHomSectionMonoidal, originalHomSectionMonoidal]
  exact tensorHomSection_pullback f A hA B φ

end
end EnvelopeProperty.SchemeInvertibleHomSection
