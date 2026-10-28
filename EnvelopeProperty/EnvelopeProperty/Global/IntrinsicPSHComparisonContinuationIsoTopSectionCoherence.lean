import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGlobalSections
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationOpenSectionPullbackCoherence

/-!
# The SAME original top-section iso agrees with actual whole section pullback

Actual restriction-unit evaluation at1 and whole naturality give the
forward identity; the genuine iso inverse gives the inverse identity.
Route: owned `iso-top-section-coherence-route.tex`.
-/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The frozen original top-section iso evaluates the actual whole section pullback at the same unit1. -/
theorem isoPullbackTopSections_hom_pullbackSectionHom {Z Y : Scheme.{u}}
    (e : Z ≅ Y) (L : Y.Modules) (α : unitObj Y ⟶ L) :
    (isoPullbackTopSections e L).hom (sectionAtOne (pullbackSectionHom e.hom α)) =
      sectionAtOne α := by
  let f := e.hom
  have ht : f ''ᵁ (⊤ : Z.Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let c := restrictFunctorIsoPullback f
  have he := congrArg (fun q => q.val.app (op ⊤) (show Γ(Z, ⊤) from 1))
    (pullbackSectionHom_comp_restrictComparison f α)
  change ((c.inv.app L).val.app (op ⊤)) (sectionAtOne (pullbackSectionHom f α)) =
    ((restrictFunctor f).map α).val.app (op ⊤)
      ((restrictUnitIso f).inv.val.app (op ⊤) (show Γ(Z, ⊤) from 1)) at he
  have hr : (restrictUnitIso f).inv.val.app (op ⊤) (show Γ(Z, ⊤) from 1) =
      (show Γ(Y, f ''ᵁ (⊤ : Z.Opens)) from 1) :=
    (restrictUnitIso_inv_app_applyP f ⊤ 1).trans (map_one (f.appIso ⊤).inv.hom)
  rw [hr] at he
  change ((c.inv.app L).val.app (op ⊤)) (sectionAtOne (pullbackSectionHom f α)) =
    α.val.app (op (f ''ᵁ (⊤ : Z.Opens))) (show Γ(Y, f ''ᵁ (⊤ : Z.Opens)) from 1) at he
  have hn := PresheafOfModules.naturality_apply α.val (eqToHom ht.symm).op
    (show Γ(Y, f ''ᵁ (⊤ : Z.Opens)) from 1)
  have hu : (unitObj Y).val.map (eqToHom ht.symm).op
      (show Γ(Y, f ''ᵁ (⊤ : Z.Opens)) from 1) = (show Γ(Y, ⊤) from 1) := by
    change Y.presheaf.map (eqToHom ht.symm).op 1 = 1
    exact map_one _
  rw [hu] at hn
  change L.presheaf.map (eqToHom ht.symm).op
      (((c.inv.app L).val.app (op ⊤)) (sectionAtOne (pullbackSectionHom f α))) = sectionAtOne α
  exact (congrArg (fun s => L.presheaf.map (eqToHom ht.symm).op s) he).trans hn.symm

/-- The SAME inverse original top-section iso is the actual unit-normalized whole pullback on values at1. -/
theorem isoPullbackTopSections_inv_sectionAtOne {Z Y : Scheme.{u}}
    (e : Z ≅ Y) (L : Y.Modules) (α : unitObj Y ⟶ L) :
    (isoPullbackTopSections e L).inv (sectionAtOne α) =
      sectionAtOne (pullbackSectionHom e.hom α) := by
  let H := isoPullbackTopSections e L
  apply (ConcreteCategory.bijective_of_isIso H.hom).injective
  exact (ConcreteCategory.congr_hom H.inv_hom_id (sectionAtOne α)).trans
    (isoPullbackTopSections_hom_pullbackSectionHom e L α).symm

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections_hom_pullbackSectionHom
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections_hom_pullbackSectionHom
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections_inv_sectionAtOne
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections_inv_sectionAtOne
