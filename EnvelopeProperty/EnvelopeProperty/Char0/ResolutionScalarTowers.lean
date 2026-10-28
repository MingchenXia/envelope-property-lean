/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AffineTransformIdeals
import EnvelopeProperty.Char0.EtaleStalkDifferentials

/-!
# Actual original-base scalar structures on resolution charts and stalks

All scalar triangles are proved from the actual section and germ maps. The
base-change compatibility generalizes the field-valued intermediate-base
calculation in Hironaka's derivative base-change module to any affine base ring.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

section Ring

variable {k R : Type u} [CommRing k] [CommRing R] {Y : Scheme.{u}}

/-- Actual section maps commute with composition through an arbitrary affine base ring. -/
theorem sectionsHom_comp_specMap (π : Y ⟶ Spec (.of R)) (σ : k →+* R) (U : Y.Opens) :
    sectionsHom (π ≫ Spec.map (CommRingCat.ofHom σ)) U = (sectionsHom π U).comp σ := by
  have hnat : (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom σ)).appTop =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of R)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have h : (π ≫ Spec.map (CommRingCat.ofHom σ)).appLE ⊤ U le_top =
      (Spec.map (CommRingCat.ofHom σ)).appTop ≫ π.appLE ⊤ U le_top :=
    Scheme.Hom.comp_appLE π (Spec.map (CommRingCat.ofHom σ)) ⊤ U le_top
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (π ≫ Spec.map (CommRingCat.ofHom σ)).appLE ⊤ U le_top).hom =
    (CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ U le_top).hom
  rw [h, ← Category.assoc, hnat, Category.assoc]

/-- The original affine base acts on the actual stalk through its actual section/germ maps. -/
@[instance_reducible]
def resolutionStalkAlgebra (π : Y ⟶ Spec (.of R)) (U : Y.Opens) (x : Y) (hx : x ∈ U) :
    Algebra R (Y.presheaf.stalk x) :=
  ((Y.presheaf.germ U x hx).hom.comp (sectionsHom π U)).toAlgebra

/-- The actual original section and germ maps form the original-base scalar tower. -/
theorem isScalarTower_resolutionStalkAlgebra (π : Y ⟶ Spec (.of R)) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) :
    letI : Algebra R Γ(Y, U) := (sectionsHom π U).toAlgebra
    letI := resolutionStalkAlgebra π U x hx
    letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower R Γ(Y, U) (Y.presheaf.stalk x) := by
  let _ : Algebra R Γ(Y, U) := (sectionsHom π U).toAlgebra
  let _ := resolutionStalkAlgebra π U x hx
  let _ := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The actual original-base section map commutes with restriction to a smaller open. -/
theorem sectionsHom_restrict (π : Y ⟶ Spec (.of R)) {U V : Y.Opens} (h : V ≤ U) :
    sectionsHom π V = (Y.presheaf.map (homOfLE h).op).hom.comp (sectionsHom π U) := by
  have e := Scheme.Hom.appLE_map π (U := ⊤) (V := U) (V' := V) le_top (homOfLE h).op
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ V le_top).hom =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ U le_top ≫
      Y.presheaf.map (homOfLE h).op).hom
  rw [e]

end Ring

section Field

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {Y : Scheme.{u}}

/-- The actual original section map respects the given field-base structure. -/
theorem isScalarTower_base_resolutionSections (π : Y ⟶ Spec (.of R)) (U : Y.Opens) :
    letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U
    letI : Algebra R Γ(Y, U) := (sectionsHom π U).toAlgebra
    IsScalarTower k R Γ(Y, U) := by
  let _ := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U
  let _ : Algebra R Γ(Y, U) := (sectionsHom π U).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact sectionsHom_comp_specMap π (algebraMap k R) U

/-- The actual original stalk algebra respects the actual original field-base structure. -/
theorem isScalarTower_base_resolutionStalk (π : Y ⟶ Spec (.of R)) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) :
    letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).stalkAlgebra x
    letI := resolutionStalkAlgebra π U x hx
    IsScalarTower k R (Y.presheaf.stalk x) := by
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := resolutionStalkAlgebra π U x hx
  apply IsScalarTower.of_algebraMap_eq'
  rw [← f.germ_comp_algebraMap_sectionsAlgebra U hx]
  change (Y.presheaf.germ U x hx).hom.comp (sectionsHom f U) =
    ((Y.presheaf.germ U x hx).hom.comp (sectionsHom π U)).comp (algebraMap k R)
  rw [sectionsHom_comp_specMap, RingHom.comp_assoc]

end Field

end EnvelopeProperty.Char0
