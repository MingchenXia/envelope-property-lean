import EnvelopeProperty.Char0.AffineBlowupComparison
import Hironaka.Scheme.BlowUpSequence.Remark33Iso

/-! # The original affine ideal and colon in SAME native spectrum coefficients -/

open CategoryTheory AlgebraicGeometry

namespace EnvelopeProperty.Char0
universe u
noncomputable section
variable {R : Type u} [CommRing R]

/-- Recovering the original affine ideal and applying the SAME original
native coefficient map recovers its ENTIRE original whole-open ideal. -/
theorem idealOfSpecSheaf_map_inv (J : (Spec (.of R)).IdealSheafData) :
    (idealOfSpecSheaf J).map (Scheme.ΓSpecIso (.of R)).inv.hom =
      J.ideal ⟨⊤, isAffineOpen_top _⟩ := by
  unfold idealOfSpecSheaf
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id,
    CommRingCat.hom_id, Ideal.map_id]

/-- EVERY original affine coefficient satisfies the SAME whole section
colon exactly when it satisfies the literal original affine colon. -/
theorem mem_specSheaf_colon_iff (J : (Spec (.of R)).IdealSheafData)
    (I : Ideal R) (a : R) :
    (Scheme.ΓSpecIso (.of R)).inv.hom a ∈
        (J.ideal ⟨⊤, isAffineOpen_top _⟩).colon
          (I.map (Scheme.ΓSpecIso (.of R)).inv.hom : Set Γ(Spec (.of R), ⊤)) ↔
      a ∈ (idealOfSpecSheaf J).colon (I : Set R) := by
  let e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have hinv : Function.Bijective (Scheme.ΓSpecIso (.of R)).inv.hom := e.bijective
  rw [← idealOfSpecSheaf_map_inv J, ← Ideal.map_colon_of_bijective _ hinv]
  rw [Ideal.mem_map_iff_of_surjective _ hinv.2]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hinv.1 hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

end
end EnvelopeProperty.Char0
