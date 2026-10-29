import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationIsoTopSectionCoherence
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationDualCanonicalSectionEvaluation

/-!
# The whole original top-section and line comparison before specialization

The genuine top-section and line maps are composed while all schemes
and modules remain variables. No section-matching premise is used.
Route: owned `iso-line-top-section-coherence-route.tex`.
-/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual top-section and whole line comparison has its literal whole section formula. -/
theorem isoLineTopSections_sectionAtOne {Z Y : Scheme.{u}} (e : Z ≅ Y)
    (L : Y.Modules) (P : Z.Modules) (a : (pullback e.hom).obj L ≅ P)
    (α : unitObj Y ⟶ L) :
    ((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom (sectionAtOne α) =
      sectionAtOne (pullbackSectionHom e.hom α ≫ a.hom) := by
  change (a.hom.app ⊤) ((isoPullbackTopSections e L).inv (sectionAtOne α)) = _
  rw [isoPullbackTopSections_inv_sectionAtOne]
  rfl

/-- Every actual top-section Hom obeys the SAME original H0 and whole line comparison. -/
theorem isoLineTopSections_topSectionHom {Z Y : Scheme.{u}} (e : Z ≅ Y)
    (L : Y.Modules) (P : Z.Modules) (a : (pullback e.hom).obj L ≅ P)
    (s : Γ(L, ⊤)) :
    topSectionHom P
        (((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom s) =
      pullbackSectionHom e.hom (topSectionHom L s) ≫ a.hom := by
  apply OriginalDualPullbackCoherence.unitHom_ext_top
  have hn : sectionAtOne (topSectionHom L s) = s := topSectionHom_app_top_apply_one _ _
  have hp : sectionAtOne (topSectionHom P
      (((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom s)) =
        ((isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)).hom s :=
    topSectionHom_app_top_apply_one _ _
  have h := isoLineTopSections_sectionAtOne e L P a (topSectionHom L s)
  rw [hn] at h
  exact hp.trans h

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_sectionAtOne
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_sectionAtOne
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_topSectionHom
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineTopSections_topSectionHom
