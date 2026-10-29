import EnvelopeProperty.Berkovich.SchemeLinePullbackSections

/-! # Genuine factor pullback of SAME original whole sections and scalar relations -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeLineSectionFactorization
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equal ORIGINAL scheme maps preserve the SAME original whole pulled section. -/
theorem pullbackSectionHom_congr {B D : Scheme.{u}} {f g : B ⟶ D} (h : f = g)
    {M : D.Modules} (α : unitObj D ⟶ M) :
    pullbackSectionHom f α ≫ (pullbackCongr h).hom.app M = pullbackSectionHom g α := by
  subst g
  change pullbackSectionHom f α ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- An actual literal factor retains the WHOLE same original section under native comparison. -/
theorem pullbackSectionHom_factor {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α : unitObj D ⟶ M) :
    pullbackSectionHom g (pullbackSectionHom b α) ≫ (frameFactorIso g b f hg M).hom =
      pullbackSectionHom f α := by
  rw [frameFactorIso, Iso.trans_hom, Iso.app_hom, ← Category.assoc,
    pullbackSectionHom_comp]
  exact pullbackSectionHom_congr hg α

/-- Actual original scalar multiplication and original whole sections commute with native pullback. -/
theorem pullbackSectionHom_precomp_scalar {B C : Scheme.{u}} (g : B ⟶ C)
    {M : C.Modules} (r : Γ(C, ⊤)) (α : unitObj C ⟶ M) :
    pullbackSectionHom g (ModularCurves.unitEndomorphismOfTopSection r ≫ α) =
      ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom r) ≫ pullbackSectionHom g α := by
  rw [← ModularCurves.pullback_unitEndomorphismOfTopSection g r]
  simp only [pullbackSectionHom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- EVERY original whole scalar relation survives the SAME actual scheme factorization. -/
theorem factor_scalar_relation {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α β : unitObj D ⟶ M)
    (r : Γ(C, ⊤))
    (h : pullbackSectionHom b α =
      ModularCurves.unitEndomorphismOfTopSection r ≫ pullbackSectionHom b β) :
    pullbackSectionHom f α = ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom r) ≫
      pullbackSectionHom f β := by
  rw [← pullbackSectionHom_factor g b f hg α, ← pullbackSectionHom_factor g b f hg β,
    h, pullbackSectionHom_precomp_scalar, Category.assoc]

/-- An ACTUAL original section isomorphism remains an isomorphism through the genuine factor. -/
theorem isIso_pullbackSectionHom_factor {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α : unitObj D ⟶ M)
    (hα : IsIso (pullbackSectionHom b α)) : IsIso (pullbackSectionHom f α) := by
  let := hα
  have hi : IsIso (pullbackSectionHom g (pullbackSectionHom b α)) := by
    change IsIso ((pullbackUnitIso g).inv ≫ (pullback g).map (pullbackSectionHom b α))
    have hmap : IsIso ((pullback g).map (pullbackSectionHom b α)) := inferInstance
    exact IsIso.comp_isIso' (pullbackUnitIso g).isIso_inv hmap
  have h : IsIso (pullbackSectionHom g (pullbackSectionHom b α) ≫
      (frameFactorIso g b f hg M).hom) := by
    let := hi
    infer_instance
  rwa [pullbackSectionHom_factor g b f hg α] at h

end EnvelopeProperty.SchemeLineSectionFactorization
