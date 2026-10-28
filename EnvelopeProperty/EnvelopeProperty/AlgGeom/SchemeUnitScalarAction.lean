import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionNaturality

/-! # Actual original structure-unit actions and the entire Hom-section map -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite

namespace EnvelopeProperty.SchemeUnitScalarAction

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
open Scheme.Modules ModularCurves

/-- The action of an actual ORIGINAL structure-module endomorphism on the
ENTIRE original module, using its actual localized tensor and left unitor. -/
def unitAction (M : X.Modules) (r : unitObj X ⟶ unitObj X) : M ⟶ M :=
  (SchemeTensorUnitSections.leftUnitIso M).inv ≫ (r ▷ M) ≫
    (SchemeTensorUnitSections.leftUnitIso M).hom

/-- On EVERY original open and EVERY original section, the SAME original
unit action is multiplication by that actual unit endomorphism's value on one. -/
theorem unitAction_apply (M : X.Modules) (r : unitObj X ⟶ unitObj X)
    (U : X.Opens) (m : Γ(M, U)) :
    (unitAction M r).val.app (.op U) m =
      (show Γ(X, U) from r.val.app (.op U) (show Γ(X, U) from 1)) • m := by
  let e := SchemeTensorUnitSections.leftUnitIso M
  let t := tensorSection (unitObj X) M U (1 : Γ(X, U)) m
  have hunit : e.hom.val.app (.op U) t = m := by
    exact (SchemeTensorUnitSections.leftUnitIso_hom_tensorSection M U 1 m).trans (one_smul _ _)
  have hinv : e.inv.val.app (.op U) m = t := by
    exact (congrArg (fun z => e.inv.val.app (.op U) z) hunit.symm).trans
      (Scheme.Modules.iso_hom_inv_app_applyT e (.op U) t)
  have hmap : (r ▷ M).val.app (.op U) t =
      tensorSection (unitObj X) M U (r.val.app (.op U) (show Γ(X, U) from 1)) m := by
    have h := tensorSection_map r (𝟙 M) U (show Γ(X, U) from 1) m
    rw [tensorHom_id] at h
    exact h
  change e.hom.val.app (.op U) ((r ▷ M).val.app (.op U) (e.inv.val.app (.op U) m)) = _
  rw [hinv, hmap]
  exact SchemeTensorUnitSections.leftUnitIso_hom_tensorSection M U _ m

private theorem unitAction_native (M : X.Modules) (r : unitObj X ⟶ unitObj X) :
    unitAction M r = (λ_ M).inv ≫
      ((monoidalUnitObjIso X).hom ≫ r ≫ (monoidalUnitObjIso X).inv) ▷ M ≫ (λ_ M).hom := by
  dsimp only [unitAction, SchemeTensorUnitSections.leftUnitIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc, comp_whiskerRight]

/-- The ACTUAL entire Hom-section bijection turns the SAME original
unit action on the source into precomposition by SAME original unit map. -/
theorem unitAction_equiv (A : X.Modules) (hA : IsInvertible A)
    (B : X.Modules) (r : unitObj X ⟶ unitObj X) (φ : A ⟶ B) :
    SchemeInvertibleHomSection.equiv A hA B (unitAction A r ≫ φ) =
      r ≫ SchemeInvertibleHomSection.equiv A hA B φ := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let adj := E.toAdjunction
  let m := (monoidalUnitObjIso X).hom ≫ r ≫ (monoidalUnitObjIso X).inv
  have hinput : (λ_ A).hom ≫ (unitAction A r ≫ φ) =
      E.functor.map m ≫ ((λ_ A).hom ≫ φ) := by
    rw [unitAction_native]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hn := adj.homEquiv_naturality_left m ((λ_ A).hom ≫ φ)
  change (monoidalUnitObjIso X).inv ≫
      adj.homEquiv _ _ ((λ_ A).hom ≫ (unitAction A r ≫ φ)) ≫
        (monoidalTensorObjIso B (dualObj A)).hom =
    r ≫ (monoidalUnitObjIso X).inv ≫ adj.homEquiv _ _ ((λ_ A).hom ≫ φ) ≫
      (monoidalTensorObjIso B (dualObj A)).hom
  rw [hinput, hn]
  dsimp only [m]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The ACTUAL original global regular function acts on the ENTIRE module
through its genuine original structure-section morphism. -/
def globalScalarAction (M : X.Modules) (a : Γ(X, ⊤)) : M ⟶ M :=
  unitAction M (SchemeModuleGlobalSections.sectionHom (unitObj X) a)

/-- The whole global scalar action multiplies EVERY section on EVERY
original open by the SAME original function's actual restriction. -/
theorem globalScalarAction_apply (M : X.Modules) (a : Γ(X, ⊤))
    (U : X.Opens) (m : Γ(M, U)) :
    (globalScalarAction M a).val.app (.op U) m =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) • m := by
  rw [globalScalarAction, unitAction_apply]
  change ((1 : Γ(X, U)) • X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) • m = _
  rw [one_smul]

end
end EnvelopeProperty.SchemeUnitScalarAction
