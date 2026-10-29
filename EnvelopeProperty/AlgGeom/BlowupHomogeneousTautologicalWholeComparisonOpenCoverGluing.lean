import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonOpenImagesCore
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing

/-! # Whole section-preserving comparison from a cover by open immersions -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.SchemeModuleOpenImages
open SchemeLineSectionEvaluation
variable {B : Scheme.{u}} {ι κ : Type*} {W : ι → Scheme.{u}}
variable {M N : B.Modules}

/-- Whole comparisons on a genuine open immersion cover glue, with overlap
matching internally derived from preservation of the same sections and bases. -/
def glueOfOpenImmersionSections (c : ∀ a, W a ⟶ B) [∀ a, IsOpenImmersion (c a)]
    (hc : ∀ x : B, ∃ a, x ∈ (c a).opensRange)
    (e : ∀ a, (Scheme.Modules.pullback (c a)).obj M ≅ (Scheme.Modules.pullback (c a)).obj N)
    (α : κ → (Scheme.Modules.unitObj B ⟶ M)) (β : κ → (Scheme.Modules.unitObj B ⟶ N))
    (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (c a) (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (c a) (α j) ≫ (e a).hom =
      pullbackSectionHom (c a) (β j)) : M ≅ N :=
  SchemeSectionPreservingGluing.glueOfSections (fun a => (c a).opensRange) hc
    (fun a => comparison (c a) (e a)) α β pivot
    (fun a => SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
      (M := N) (c a).isoOpensRange.inv (c a) (c a).opensRange.ι
      (Scheme.Hom.isoOpensRange_inv_comp (c a)) (β (pivot a)) (hβ a))
    (fun a j => comparison_section (c a) (e := e a) (α := α j) (β := β j) (hpres a j))

/-- Every prescribed section is preserved on the entire covered scheme. -/
theorem glueOfOpenImmersionSections_section (c : ∀ a, W a ⟶ B) [∀ a, IsOpenImmersion (c a)]
    (hc : ∀ x : B, ∃ a, x ∈ (c a).opensRange)
    (e : ∀ a, (Scheme.Modules.pullback (c a)).obj M ≅ (Scheme.Modules.pullback (c a)).obj N)
    (α : κ → (Scheme.Modules.unitObj B ⟶ M)) (β : κ → (Scheme.Modules.unitObj B ⟶ N))
    (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (c a) (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (c a) (α j) ≫ (e a).hom =
      pullbackSectionHom (c a) (β j)) (j : κ) :
    α j ≫ (glueOfOpenImmersionSections c hc e α β pivot hβ hpres).hom = β j := by
  exact SchemeSectionPreservingGluing.glueOfSections_section _ _ _ _ _ _ _ _ j

end EnvelopeProperty.SchemeModuleOpenImages
