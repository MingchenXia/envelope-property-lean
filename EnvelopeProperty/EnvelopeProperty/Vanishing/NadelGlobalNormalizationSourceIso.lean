import Mathlib.AlgebraicGeometry.Normalization

/-! # Native whole relative normalization respects an actual source isomorphism

The universal native normalization morphisms construct both maps. No
normalization comparison is supplied as data.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization
variable {X X' Y : Scheme.{u}} (e : X ≅ X') (f : X ⟶ Y) (g : X' ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  (h : e.hom ≫ g = f)

/-- Actual universal normalization transport through the SAME source iso. -/
def sourceComparison : f.normalization ⟶ g.normalization :=
  f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization (by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h])

/-- The actual transported whole normalization projection triangle. -/
theorem sourceComparison_projection : sourceComparison e f g h ≫ g.fromNormalization = f.fromNormalization :=
  f.normalizationDesc_comp _ _ _

/-- The actual transported whole generic lift triangle. -/
theorem toNormalization_sourceComparison : f.toNormalization ≫ sourceComparison e f g h =
    e.hom ≫ g.toNormalization := f.toNormalization_normalizationDesc _ _ _

/-- The native WHOLE relative normalizations are genuinely isomorphic under
an actual original-source isomorphism, from their universal uniqueness. -/
def sourceIso : f.normalization ≅ g.normalization := by
  have h' : e.inv ≫ f = g := by rw [← h, Iso.inv_hom_id_assoc]
  refine ⟨sourceComparison e f g h, sourceComparison e.symm g f h', ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simp only [toNormalization_sourceComparison, reassoc_of% toNormalization_sourceComparison,
        Iso.symm_hom, Iso.hom_inv_id_assoc, Category.comp_id]
    · rw [Category.assoc, sourceComparison_projection, sourceComparison_projection]
    · simp
  · apply Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
    · simp only [toNormalization_sourceComparison, reassoc_of% toNormalization_sourceComparison,
        Iso.symm_hom, Iso.inv_hom_id_assoc, Category.comp_id]
    · rw [Category.assoc, sourceComparison_projection, sourceComparison_projection]
    · simp

/-- The constructed whole source normalization iso retains its actual projection. -/
theorem sourceIso_projection : (sourceIso e f g h).hom ≫ g.fromNormalization = f.fromNormalization :=
  sourceComparison_projection e f g h

/-- The constructed whole source normalization iso retains its actual generic lift. -/
theorem sourceIso_generic : f.toNormalization ≫ (sourceIso e f g h).hom = e.hom ≫ g.toNormalization :=
  toNormalization_sourceComparison e f g h

end EnvelopeProperty.Vanishing.NadelGlobalNormalization
