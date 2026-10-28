/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.EquivariantGroupFibreTrivialization

/-!
# Entire original unit-fibre compatibility of the genuine group trivialization

The SAME original fibre inclusion becomes exactly the unit-times-original
fibre inclusion, with no supplied pointwise or fibre-restriction certificate.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace EnvelopeProperty.EquivariantGroupFibreInclusion
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G] {X F : C} [ModObj G X]
private local instance regularAction : ModObj G G := ModObj.regular G
variable (p : X ⟶ G) [IsModHom G p]
  {i : F ⟶ X} (h : IsPullback i (toUnit F) p η[G])

omit [IsModHom G p] in
include h in
private theorem inclusion_normalize : i ≫ EquivariantGroupFibreTrivialization.normalize G p = i := by
  rw [EquivariantGroupFibreTrivialization.normalize, ModObj.comp_smul, Category.comp_id]
  have hi : i ≫ p⁻¹ = (i ≫ p)⁻¹ := by simp only [Hom.inv_def, Category.assoc]
  rw [hi, h.w]
  change (1 : F ⟶ G)⁻¹ • i = i
  simp

/-- The SAME original fibre inclusion followed by the actual derived fibre component is the WHOLE identity. -/
theorem inclusion_toFibre : i ≫ EquivariantGroupFibreTrivialization.toFibre G p h = 𝟙 F := by
  let : Mono i := h.mono_fst_of_mono
  apply (cancel_mono i).mp
  rw [Category.assoc, EquivariantGroupFibreTrivialization.toFibre_inclusion,
    inclusion_normalize G p h, Category.id_comp]

/-- The entire ORIGINAL unit-fibre inclusion is exactly the original group unit
and SAME original fibre identity under the internally derived whole trivialization. -/
theorem inclusion_iso : i ≫ (EquivariantGroupFibreTrivialization.iso G p h).hom =
    lift (toUnit F ≫ η[G]) (𝟙 F) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, EquivariantGroupFibreTrivialization.iso_hom_fst, lift_fst, h.w]
  · change (i ≫ lift p (EquivariantGroupFibreTrivialization.toFibre G p h)) ≫ snd G F = _
    rw [Category.assoc, lift_snd, lift_snd]
    exact inclusion_toFibre G p h

/-- The actual WHOLE inverse product isomorphism restricts to precisely the ORIGINAL unit-fibre inclusion. -/
theorem unit_iso_inv : lift (toUnit F ≫ η[G]) (𝟙 F) ≫
    (EquivariantGroupFibreTrivialization.iso G p h).inv = i := by
  rw [← inclusion_iso G p h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end EnvelopeProperty.EquivariantGroupFibreInclusion
