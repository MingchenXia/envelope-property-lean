import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsOriginal
import EnvelopeProperty.SchemeImageFlat

/-! # The SAME actual section scalar actions under original scheme isomorphisms -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsSectionAlgebra
open Berkovich
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two native names use the SAME original local section coefficient map. -/
theorem sectionBaseMap_eq_sectionsAlgebra {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (U : X.Opens) :
    SchemeValuedPoint.sectionBaseMap f U =
      @algebraMap R Γ(X, U) _ _ (f.sectionsAlgebra U) := by
  rfl

/-- The actual coefficient change composes the SAME original whole section maps. -/
theorem sectionBaseMap_comp {R S : Type u} [CommRing R] [CommRing S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of S)) (φ : R →+* S) (U : X.Opens) :
    SchemeValuedPoint.sectionBaseMap (f ≫ Spec.map (CommRingCat.ofHom φ)) U =
      (SchemeValuedPoint.sectionBaseMap f U).comp φ := by
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  apply RingHom.ext
  intro r
  change (((Scheme.ΓSpecIso (.of R)).inv ≫
      (f ≫ Spec.map (CommRingCat.ofHom φ)).appTop ≫
        X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom r) =
    ((CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of S)).inv ≫ f.appTop ≫
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom r)
  rw [Scheme.Hom.comp_appTop]
  simp only [← Category.assoc]
  rw [hnat]

private theorem ringIsoEquiv_apply {A B : CommRingCat.{u}} (f : A ⟶ B) [IsIso f] (a : A) :
    (asIso f).commRingCatIsoToRingEquiv a = f.hom a := rfl

/-- The actual whole local section isomorphism retains precisely the actual
original regular-smooth section algebras and original scalar triangle. -/
def sectionAlgEquivOfIso {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (e : X ≅ Y) (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (w : e.hom ≫ pY = pX) (U : Y.Opens) :
    letI := pY.sectionsAlgebra U
    letI := pX.sectionsAlgebra (e.hom ⁻¹ᵁ U)
    Γ(Y, U) ≃ₐ[R] Γ(X, e.hom ⁻¹ᵁ U) := by
  letI := pY.sectionsAlgebra U
  letI := pX.sectionsAlgebra (e.hom ⁻¹ᵁ U)
  refine { (asIso (e.hom.app U)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  have h := RingHom.congr_fun (SchemeImage.sectionBaseMap_comp_app (RingHom.id R) pX pY e.hom
    (by simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using w) U) r
  have hh := (ringIsoEquiv_apply (e.hom.app U) (algebraMap R Γ(Y, U) r))
  exact hh.trans (by
    simpa only [sectionBaseMap_eq_sectionsAlgebra, RingHom.comp_apply, RingHom.id_apply] using h)

end EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsSectionAlgebra
