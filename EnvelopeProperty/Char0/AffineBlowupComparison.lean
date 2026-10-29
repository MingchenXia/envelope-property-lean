/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Scheme.BlowUp.UniversalProperty
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Existence
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible

/-!
# Actual affine and global blowup comparison

Both the affine Rees-Proj blowup and the global scheme blowup satisfy the actual universal
property. Uniqueness identifies them over the affine base. The ideal-sheaf normalization on
an actual spectrum removes any separate affine-presentation assumption on a sequence centre.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory

universe u

/-- The actual universal properties produce an isomorphism over the common base. -/
theorem exists_iso_of_isBlowUp {X Y Z : Scheme.{u}} {I : X.IdealSheafData}
    {πY : Y ⟶ X} {πZ : Z ⟶ X} (hY : IsBlowUp I πY) (hZ : IsBlowUp I πZ) :
    ∃ e : Y ≅ Z, e.hom ≫ πZ = πY := by
  obtain ⟨f, hf⟩ := hZ.exists_lift πY hY.admissible
  obtain ⟨g, hg⟩ := hY.exists_lift πZ hZ.admissible
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply hY.hom_ext πY hY.admissible
    · rw [Category.assoc, hg, hf]
    · exact Category.id_comp πY
  · apply hZ.hom_ext πZ hZ.admissible
    · rw [Category.assoc, hf, hg]
    · exact Category.id_comp πZ

/-- The checked affine lift and exceptional-ideal theorems satisfy the actual blowup predicate. -/
theorem affineBlowUp_isBlowUp {R : Type u} [CommRing R] (I : Ideal R) :
    IsBlowUp (specIdealSheaf I) (affineBlowUp.π I) :=
  ⟨affineBlowUp.isInvertible_exceptionalIdeal I,
    fun f hf => affineBlowUp.existsUnique_lift I f hf⟩

/-- The actual affine Rees-Proj blowup and the global scheme blowup are isomorphic over `Spec R`. -/
theorem exists_affineBlowUp_global_iso {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : affineBlowUp I ≅ (specIdealSheaf I).blowUp,
      e.hom ≫ (specIdealSheaf I).blowUpπ = affineBlowUp.π I :=
  exists_iso_of_isBlowUp (affineBlowUp_isBlowUp I)
    (Scheme.IdealSheafData.blowUp.isBlowUp (specIdealSheaf I))

/-- The actual ideal of a centre on `Spec R`, transported from its global sections to `R`. -/
def idealOfSpecSheaf {R : Type u} [CommRing R] (J : (Spec (.of R)).IdealSheafData) : Ideal R :=
  (J.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (.of R)).hom.hom

/-- Normalizing an arbitrary affine centre and reconstructing its ideal sheaf gives it back. -/
theorem specIdealSheaf_idealOfSpecSheaf {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) : specIdealSheaf (idealOfSpecSheaf J) = J := by
  unfold specIdealSheaf idealOfSpecSheaf
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  exact (Scheme.IdealSheafData.equivOfIsAffine (X := Spec (.of R))).symm_apply_apply J

/-- No affine-centre presentation is assumed: every actual centre has the canonical affine
Rees-Proj blowup, compatibly with its actual structure morphism. -/
theorem exists_affineBlowUp_center_iso {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) :
    ∃ e : affineBlowUp (idealOfSpecSheaf J) ≅ J.blowUp,
      e.hom ≫ J.blowUpπ = affineBlowUp.π (idealOfSpecSheaf J) := by
  generalize hI : idealOfSpecSheaf J = I
  have hIJ : specIdealSheaf I = J := by
    rw [← hI]
    exact specIdealSheaf_idealOfSpecSheaf J
  subst J
  exact exists_affineBlowUp_global_iso I

/-- An actual point of the blowup rules out the zero centre ideal on its affine base. -/
theorem idealOfSpecSheaf_ne_bot_of_blowUp_point {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) (p : J.blowUp) : idealOfSpecSheaf J ≠ ⊥ := by
  intro hzero
  obtain ⟨e, _⟩ := exists_affineBlowUp_center_iso J
  have q : affineBlowUp (⊥ : Ideal R) := by
    rw [← hzero]
    exact e.inv p
  have : IsEmpty (affineBlowUp (⊥ : Ideal R)) := affineBlowUp.isEmpty_bot
  exact isEmptyElim q

end EnvelopeProperty.Char0
