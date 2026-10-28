/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealFamilyLift
import EnvelopeProperty.Projective.NativeClosedLaurentEvaluation

/-!
# Actual action-law transport through the genuine blowup

Unit, naturality and multiplication laws are equalities of whole constructed
scheme morphisms, proved by the actual pullback and blowup universal properties.
The native closed Laurent sections supply their concrete base diagrams.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {Y Y₁ Y₂ : Scheme.{u}} (K : Y.IdealSheafData)

/-- The actual unit section of the whole blowup family product. -/
def parameterFamilyUnitSection (p : Y₁ ⟶ Y) (b : Y ⟶ Y₁) (hb : b ≫ p = 𝟙 Y) :
    K.blowUp ⟶ pullback K.blowUpπ p :=
  pullback.lift (𝟙 _) (K.blowUpπ ≫ b) (by
    rw [Category.id_comp, Category.assoc, hb, Category.comp_id])

/-- The actual unit law on the whole constructed blowup family. -/
theorem parameterFamilyLift_unit (p a : Y₁ ⟶ Y) [Flat p]
    (hK : K.comap a = K.comap p) (b : Y ⟶ Y₁)
    (hbp : b ≫ p = 𝟙 Y) (hba : b ≫ a = 𝟙 Y) :
    K.parameterFamilyUnitSection p b hbp ≫ K.parameterFamilyLift p a hK = 𝟙 _ := by
  apply blowUp.hom_ext K K.blowUpπ (blowUp.isInvertible_comap_π K)
  · rw [Category.assoc, K.parameterFamilyLift_π, ← Category.assoc]
    change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ a = _
    rw [pullback.lift_snd, Category.assoc, hba, Category.comp_id]
  · exact Category.id_comp _

/-- The actual map of whole blowup products under a commuting base-family map. -/
def parameterFamilyBaseChangeMap (p : Y₁ ⟶ Y) (p₂ : Y₂ ⟶ Y) (e : Y₂ ⟶ Y₁)
    (he : e ≫ p = p₂) : pullback K.blowUpπ p₂ ⟶ pullback K.blowUpπ p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e) (by
    rw [Category.assoc, he, pullback.condition])

/-- The whole product map preserves its entire changed-family component. -/
@[reassoc]
theorem parameterFamilyBaseChangeMap_snd
    (p : Y₁ ⟶ Y) (p₂ : Y₂ ⟶ Y) (e : Y₂ ⟶ Y₁) (he : e ≫ p = p₂) :
    K.parameterFamilyBaseChangeMap p p₂ e he ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e :=
  pullback.lift_snd _ _ _

/-- The actual entire family lift is natural under its true whole base diagrams. -/
theorem parameterFamilyLift_naturality (p a : Y₁ ⟶ Y) [Flat p]
    (p₂ a₂ : Y₂ ⟶ Y) [Flat p₂] (hK : K.comap a = K.comap p)
    (hK₂ : K.comap a₂ = K.comap p₂) (e : Y₂ ⟶ Y₁)
    (hp : e ≫ p = p₂) (ha : e ≫ a = a₂) :
    K.parameterFamilyBaseChangeMap p p₂ e hp ≫ K.parameterFamilyLift p a hK =
      K.parameterFamilyLift p₂ a₂ hK₂ := by
  apply blowUp.hom_ext K (pullback.snd K.blowUpπ p₂ ≫ a₂)
    (K.parameterFamily_admissible p₂ a₂ hK₂)
  · rw [Category.assoc, K.parameterFamilyLift_π, ← Category.assoc,
      K.parameterFamilyBaseChangeMap_snd, Category.assoc, ha]
  · exact K.parameterFamilyLift_π p₂ a₂ hK₂

/-- The actual product map implementing the second action after the first
constructed blowup family lift. -/
def parameterFamilyThenMap (p : Y₁ ⟶ Y) (p₂ a₁ : Y₂ ⟶ Y) [Flat p₂]
    (hK₁ : K.comap a₁ = K.comap p₂) (e : Y₂ ⟶ Y₁) (he : e ≫ p = a₁) :
    pullback K.blowUpπ p₂ ⟶ pullback K.blowUpπ p :=
  pullback.lift (K.parameterFamilyLift p₂ a₁ hK₁) (pullback.snd _ _ ≫ e) (by
    rw [K.parameterFamilyLift_π, Category.assoc, he])

/-- The whole sequential-action product map retains the true family component. -/
@[reassoc]
theorem parameterFamilyThenMap_snd (p : Y₁ ⟶ Y) (p₂ a₁ : Y₂ ⟶ Y) [Flat p₂]
    (hK₁ : K.comap a₁ = K.comap p₂) (e : Y₂ ⟶ Y₁) (he : e ≫ p = a₁) :
    K.parameterFamilyThenMap p p₂ a₁ hK₁ e he ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e :=
  pullback.lift_snd _ _ _

/-- The whole sequential lifted action equals the single product lift, by
actual blowup uniqueness over the proved entire base multiplication diagram. -/
theorem parameterFamilyLift_composition (p a : Y₁ ⟶ Y) [Flat p]
    (p₂ a₁ a₂ : Y₂ ⟶ Y) [Flat p₂] (hK : K.comap a = K.comap p)
    (hK₁ : K.comap a₁ = K.comap p₂) (hK₂ : K.comap a₂ = K.comap p₂)
    (e : Y₂ ⟶ Y₁) (hp : e ≫ p = a₁) (ha : e ≫ a = a₂) :
    K.parameterFamilyThenMap p p₂ a₁ hK₁ e hp ≫ K.parameterFamilyLift p a hK =
      K.parameterFamilyLift p₂ a₂ hK₂ := by
  apply blowUp.hom_ext K (pullback.snd K.blowUpπ p₂ ≫ a₂)
    (K.parameterFamily_admissible p₂ a₂ hK₂)
  · rw [Category.assoc, K.parameterFamilyLift_π, ← Category.assoc,
      K.parameterFamilyThenMap_snd, Category.assoc, ha]
  · exact K.parameterFamilyLift_π p₂ a₂ hK₂

end AlgebraicGeometry.Scheme.IdealSheafData
