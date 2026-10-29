import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionBaseChange

/-! # The SAME original Hom-section and true pullback retain actual map isomorphisms -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace EnvelopeProperty.SchemeInvertibleHomSection
universe u
set_option backward.isDefEq.respectTransparency false
private noncomputable instance homSectionIsoMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
private noncomputable instance homSectionIsoSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
private noncomputable instance homSectionIsoPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- A genuine isomorphism of the SAME original modules gives a genuine isomorphism
of its SAME entire original Hom-section; no frame or scalar comparison premise. -/
theorem isIso_equiv_of_isIso {X : Scheme.{u}}
    (A : X.Modules) (hA : Scheme.Modules.IsInvertible A) (B : X.Modules)
    (φ : A ⟶ B) [IsIso φ] : IsIso (equiv A hA B φ) := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  change IsIso ((ModularCurves.monoidalUnitObjIso X).inv ≫
    E.toAdjunction.homEquiv _ _ ((λ_ A).hom ≫ φ ≫ 𝟙 B) ≫
      (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).hom)
  rw [Category.comp_id, Adjunction.homEquiv_unit]
  infer_instance

/-- If the SAME entire original map becomes an isomorphism after actual geometric
pullback, the SAME ENTIRE original Hom-section becomes an isomorphism after that
pullback. Actual native unit/tensor/dual comparisons are derived, not input. -/
theorem isIso_pullback_equiv_of_isIso_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B : X.Modules) (φ : A ⟶ B) [IsIso ((Scheme.Modules.pullback f).map φ)] :
    IsIso ((Scheme.Modules.pullback f).map (equiv A hA B φ)) := by
  let F := Scheme.Modules.pullback f
  let : IsIso (equiv (F.obj A) (hA.pullback f) (F.obj B) (F.map φ)) :=
    isIso_equiv_of_isIso (F.obj A) (hA.pullback f) (F.obj B) (F.map φ)
  let t := (ModularCurves.monoidalUnitObjIso X).hom ≫ equiv A hA B φ ≫
    (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv
  let c := (Functor.Monoidal.μIso F B (Scheme.Modules.dualObj A)).inv ≫
    F.obj B ◁ (rightDualPullbackEvaluationIso f A hA).hom
  have he : (ModularCurves.monoidalUnitObjIso Y).hom ≫
      equiv (F.obj A) (hA.pullback f) (F.obj B) (F.map φ) ≫
        (ModularCurves.monoidalTensorObjIso (F.obj B) (Scheme.Modules.dualObj (F.obj A))).inv =
      (Functor.Monoidal.εIso F).hom ≫ F.map t ≫ c := by
    simpa only [F, t, c, Category.assoc] using equiv_pullback_monoidal f A hA B φ
  let : IsIso ((Functor.Monoidal.εIso F).hom ≫ F.map t ≫ c) := he ▸ inferInstance
  let : IsIso ((Functor.Monoidal.εIso F).hom ≫ F.map t) :=
    IsIso.of_isIso_comp_right _ c
  let : IsIso (F.map t) := IsIso.of_isIso_comp_left
    (Functor.Monoidal.εIso F).hom (F.map t)
  have ht : F.map t = F.map (ModularCurves.monoidalUnitObjIso X).hom ≫
      F.map (equiv A hA B φ) ≫
        F.map (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv := by
    simp only [t, Functor.map_comp]
  let : IsIso (F.map (ModularCurves.monoidalUnitObjIso X).hom ≫
      F.map (equiv A hA B φ) ≫
        F.map (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv) :=
    ht ▸ inferInstance
  let : IsIso (F.map (ModularCurves.monoidalUnitObjIso X).hom ≫ F.map (equiv A hA B φ)) :=
    IsIso.of_isIso_comp_right
      (F.map (ModularCurves.monoidalUnitObjIso X).hom ≫ F.map (equiv A hA B φ))
      (F.map (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv)
  exact IsIso.of_isIso_comp_left (F.map (ModularCurves.monoidalUnitObjIso X).hom)
    (F.map (equiv A hA B φ))

end EnvelopeProperty.SchemeInvertibleHomSection
