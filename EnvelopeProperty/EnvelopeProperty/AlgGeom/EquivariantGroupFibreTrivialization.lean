/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.GroupActionProductIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Genuine whole trivialization of an equivariant map to its regular group

The SAME specified unit fibre and original action give the actual mutually
inverse morphisms (g,z) ↦ g z and x ↦ (p(x),p(x)⁻¹ x). No trivialization,
normality, reducedness or irreducibility certificate is supplied.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace EnvelopeProperty.EquivariantGroupFibreTrivialization

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G] {X F : C} [ModObj G X]
local instance regularAction : ModObj G G := ModObj.regular G
variable (p : X ⟶ G) [IsModHom G p]
  {i : F ⟶ X} (h : IsPullback i (toUnit F) p η[G])

private theorem regular_smul_eq_mul {A : C} (a b : A ⟶ G) : a • b = a * b := rfl

/-- The entire original inverse-parameter action, on the SAME original object. -/
def normalize : X ⟶ X := p⁻¹ • 𝟙 X

private theorem normalize_projection : normalize G p ≫ p = toUnit X ≫ η[G] := by
  rw [normalize, IsModHom.map_smul, Category.id_comp, regular_smul_eq_mul]
  exact inv_mul_cancel p

omit [IsModHom G p] in
private theorem comp_normalize {A : C} (a : A ⟶ X) :
    a ≫ normalize G p = (a ≫ p)⁻¹ • a := by
  simp only [normalize, ModObj.comp_smul, Category.comp_id, Hom.inv_def, Category.assoc]

/-- The whole original normalization map factors through the SAME specified unit fibre. -/
def toFibre : X ⟶ F := h.lift (normalize G p) (toUnit X) (normalize_projection G p)

@[reassoc (attr := simp)]
theorem toFibre_inclusion : toFibre G p h ≫ i = normalize G p := h.lift_fst _ _ _

/-- The actual original action map from the regular group times the SAME unit fibre. -/
def fromProduct : G ⊗ F ⟶ X := (fst G F) • (snd G F ≫ i)

/-- The original whole point-to-product morphism uses the original parameter and fibre. -/
def toProduct : X ⟶ G ⊗ F := lift p (toFibre G p h)

include h in
private theorem fromProduct_projection : fromProduct G (i := i) ≫ p = fst G F := by
  rw [fromProduct, IsModHom.map_smul]
  have hi : (snd G F ≫ i) ≫ p = (1 : G ⊗ F ⟶ G) := by
    rw [Category.assoc, h.w]
    change snd G F ≫ toUnit F ≫ η[G] = toUnit (G ⊗ F) ≫ η[G]
    rw [← Category.assoc]
    exact congrArg (fun a => a ≫ η[G]) (toUnit_unique _ _)
  rw [hi, regular_smul_eq_mul, mul_one]

private theorem toProduct_fromProduct :
    toProduct G p h ≫ fromProduct G (i := i) = 𝟙 X := by
  rw [fromProduct, ModObj.comp_smul]
  simp only [toProduct, lift_fst, lift_snd_assoc, toFibre_inclusion, normalize]
  exact smul_inv_smul p (𝟙 X)

private theorem fromProduct_toFibre :
    fromProduct G (i := i) ≫ toFibre G p h = snd G F := by
  apply h.hom_ext
  · rw [Category.assoc, toFibre_inclusion, comp_normalize, fromProduct_projection G p h,
      fromProduct]
    exact inv_smul_smul (fst G F) (snd G F ≫ i)
  · exact toUnit_unique _ _

private theorem fromProduct_toProduct :
    fromProduct G (i := i) ≫ toProduct G p h = 𝟙 (G ⊗ F) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, toProduct, lift_fst, Category.id_comp]
    exact fromProduct_projection G p h
  · simp only [Category.assoc, toProduct, lift_snd, Category.id_comp]
    exact fromProduct_toFibre G p h

/-- The genuine entire original product trivialization, retaining the SAME specified
unit fibre and SAME original group parameter, without any supplied trivialization. -/
def iso : X ≅ G ⊗ F where
  hom := toProduct G p h
  inv := fromProduct G (i := i)
  hom_inv_id := toProduct_fromProduct G p h
  inv_hom_id := fromProduct_toProduct G p h

/-- The entire original parameter is exactly the first whole product projection. -/
@[reassoc (attr := simp)]
theorem iso_hom_fst : (iso G p h).hom ≫ fst G F = p := lift_fst _ _

/-- The entire inverse projection is the original parameter map of the actual action. -/
@[reassoc (attr := simp)]
theorem iso_inv_projection : (iso G p h).inv ≫ p = fst G F := fromProduct_projection G p h

/-- The whole same original unit-fibre component is inverse-parameter normalization. -/
@[reassoc (attr := simp)]
theorem iso_hom_snd_inclusion : (iso G p h).hom ≫ snd G F ≫ i = normalize G p := by
  change lift p (toFibre G p h) ≫ snd G F ≫ i = normalize G p
  rw [lift_snd_assoc, toFibre_inclusion]

end EnvelopeProperty.EquivariantGroupFibreTrivialization
