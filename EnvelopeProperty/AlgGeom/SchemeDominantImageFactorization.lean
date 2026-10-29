import EnvelopeProperty.SchemeImageFlat

/-! # Actual whole maps factor through the scheme image of a dense restriction -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.SchemeDominantImageFactorization
variable {W T X : Scheme.{u}}

/-- The true entire original morphism factors through the ACTUAL scheme image
of its schematically dense restriction, by actual kernel equality. -/
def factorThroughImage (a : W ⟶ T) [IsSchemeTheoreticallyDominant a] (q : T ⟶ X) :
    T ⟶ (a ≫ q).image :=
  q.toImage ≫ Scheme.IdealSheafData.inclusion (by
    rw [Scheme.Hom.ker_comp,a.ker_eq_bot,Scheme.IdealSheafData.map_bot])

/-- The whole original q is retained, including all original sections. -/
theorem factorThroughImage_inclusion (a : W ⟶ T) [IsSchemeTheoreticallyDominant a]
    (q : T ⟶ X) :
    factorThroughImage a q ≫ (a ≫ q).imageι = q := by
  simp [factorThroughImage]

/-- The true original dense restriction is the ACTUAL canonical image map. -/
theorem dominant_factorThroughImage (a : W ⟶ T) [IsSchemeTheoreticallyDominant a]
    (q : T ⟶ X) : a ≫ factorThroughImage a q = (a ≫ q).toImage := by
  apply (cancel_mono (a ≫ q).imageι).mp
  simp [Category.assoc,factorThroughImage_inclusion]

/-- The whole actual native scheme image of an integral source is integral. -/
theorem image_isIntegral (f : T ⟶ X) [QuasiCompact f] [IsIntegral T] :
    IsIntegral f.image := by
  let : IsSchemeTheoreticallyDominant f.toImage := f.isSchemeTheoreticallyDominant_toImage
  let : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  let : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def f.image).mpr
    have h := (IrreducibleSpace.isIrreducible_univ T).image
      f.toImage f.toImage.continuous.continuousOn
    simpa only [Set.image_univ,f.toImage.denseRange.closure_eq,Set.top_eq_univ] using h.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

end EnvelopeProperty.SchemeDominantImageFactorization
