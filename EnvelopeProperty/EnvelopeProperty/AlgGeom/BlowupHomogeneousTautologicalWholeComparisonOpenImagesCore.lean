import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Transport of module comparisons to the open image of an open immersion -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.SchemeModuleOpenImages

/-- Transport a whole module comparison to the canonical open image. -/
def comparison {B W : Scheme.{u}} (c : W ⟶ B) [IsOpenImmersion c]
    {M N : B.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj N) :
    (Scheme.Modules.pullback c.opensRange.ι).obj M ≅
      (Scheme.Modules.pullback c.opensRange.ι).obj N :=
  (Scheme.Modules.frameFactorIso c.isoOpensRange.inv c c.opensRange.ι
    (Scheme.Hom.isoOpensRange_inv_comp c) M).symm ≪≫
    (Scheme.Modules.pullback c.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.frameFactorIso c.isoOpensRange.inv c c.opensRange.ι
      (Scheme.Hom.isoOpensRange_inv_comp c) N

private theorem sectionPullback_moduleComp {B W : Scheme.{u}} (c : W ⟶ B)
    {M N : B.Modules} (α : Scheme.Modules.unitObj B ⟶ M) (t : M ⟶ N) :
    SchemeLineSectionEvaluation.pullbackSectionHom c α ≫ (Scheme.Modules.pullback c).map t =
      SchemeLineSectionEvaluation.pullbackSectionHom c (α ≫ t) := by
  simp only [SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_comp, Category.assoc]

theorem comparison_section {B W : Scheme.{u}} (c : W ⟶ B)
    [IsOpenImmersion c] {M N : B.Modules}
    {e : (Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj N}
    {α : Scheme.Modules.unitObj B ⟶ M} {β : Scheme.Modules.unitObj B ⟶ N}
    (h : SchemeLineSectionEvaluation.pullbackSectionHom c α ≫ e.hom =
      SchemeLineSectionEvaluation.pullbackSectionHom c β) :
    SchemeLineSectionEvaluation.pullbackSectionHom c.opensRange.ι α ≫
        (comparison c e).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom c.opensRange.ι β := by
  let d := c.isoOpensRange.inv
  let C := Scheme.Modules.frameFactorIso d c c.opensRange.ι (Scheme.Hom.isoOpensRange_inv_comp c) M
  let D := Scheme.Modules.frameFactorIso d c c.opensRange.ι (Scheme.Hom.isoOpensRange_inv_comp c) N
  let E := (Scheme.Modules.pullback d).mapIso e
  have hα := SchemeLineSectionFactorization.pullbackSectionHom_factor d c c.opensRange.ι
    (Scheme.Hom.isoOpensRange_inv_comp c) α
  have hβ := SchemeLineSectionFactorization.pullbackSectionHom_factor d c c.opensRange.ι
    (Scheme.Hom.isoOpensRange_inv_comp c) β
  have hp := (sectionPullback_moduleComp d
    (SchemeLineSectionEvaluation.pullbackSectionHom c α) e.hom).trans
    (congrArg (SchemeLineSectionEvaluation.pullbackSectionHom d) h)
  change SchemeLineSectionEvaluation.pullbackSectionHom c.opensRange.ι α ≫
    (C.inv ≫ E.hom ≫ D.hom) = _
  rw [← hα]
  change (SchemeLineSectionEvaluation.pullbackSectionHom d
      (SchemeLineSectionEvaluation.pullbackSectionHom c α) ≫ C.hom) ≫
    (C.inv ≫ E.hom ≫ D.hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ D.hom) hp).trans hβ)


end EnvelopeProperty.SchemeModuleOpenImages
