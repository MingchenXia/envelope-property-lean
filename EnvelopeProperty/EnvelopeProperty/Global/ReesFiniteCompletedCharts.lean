/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ReesChartNativePoint
import EnvelopeProperty.Berkovich.SchemeAffineBaseCompletedFibre

/-!
# Actual completed-field cover by the original Rees affine scheme fibres

Base change the genuine original paper-chart cover, then transport each
component through the actual coefficient triangle pullback isomorphism.
The resulting true scheme cover uses exactly the affine scheme pullbacks
of the intrinsic chart psh producers, with both whole projection identities.
-/

open scoped Classical NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.ReesPresentation
variable {A : Type u} [CommRing A] [IsDomain A] {n : ℕ} (g : Fin (n + 1) → A)
    (a : Spectrum A)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact original coefficient triangle supplies the actual component
pullback isomorphism, with no affine comparison hypothesis. -/
def fcFiniteCompletedChartIso (l : Fin (n + 1)) (hl : g l ≠ 0) :
    SchemeCompletedFibre.affineModel (B := blowupChart (Finset.univ.image g) (g l)) a ≅
      SchemeCompletedFibre.affineBaseModel
        (fcFinitePaperChartImmersion g l hl ≫ fcFiniteProjection g) a :=
  pullback.congrHom (fcFinitePaperChartImmersion_comp_projection g l hl).symm rfl

/-- The literal affine completed scheme chart maps into the literal whole
completed Rees fibre using the genuine base-changed original chart map. -/
def fcFiniteCompletedChartMap (l : Fin (n + 1)) (hl : g l ≠ 0) :
    SchemeCompletedFibre.affineModel (B := blowupChart (Finset.univ.image g) (g l)) a ⟶
      SchemeCompletedFibre.affineBaseModel (fcFiniteProjection g) a :=
  (fcFiniteCompletedChartIso g a l hl).hom ≫
    (Scheme.Pullback.openCoverOfLeft (fcFinitePaperAffineOpenCover g).openCover
      (fcFiniteProjection g) (Spec.map (CommRingCat.ofHom a.toH))).f ⟨l, hl⟩

/-- The actual base-changed original paper cover is transported to the literal
affine completed scheme fibres, giving a genuine whole scheme open cover. -/
def fcFiniteCompletedOpenCover :
    (SchemeCompletedFibre.affineBaseModel (fcFiniteProjection g) a).OpenCover :=
  (Scheme.Pullback.openCoverOfLeft (fcFinitePaperAffineOpenCover g).openCover
    (fcFiniteProjection g) (Spec.map (CommRingCat.ofHom a.toH))).copy
      {l : Fin (n + 1) // g l ≠ 0}
      (fun l => SchemeCompletedFibre.affineModel
        (B := blowupChart (Finset.univ.image g) (g l.1)) a)
      (fun l => fcFiniteCompletedChartMap g a l.1 l.2) (Equiv.refl _)
      (fun l => fcFiniteCompletedChartIso g a l.1 l.2) (fun _ => rfl)

/-- Each actual completed original fraction-chart map is a genuine open immersion. -/
instance fcFiniteCompletedChartMap_isOpenImmersion (l : Fin (n + 1)) (hl : g l ≠ 0) :
    IsOpenImmersion (fcFiniteCompletedChartMap g a l hl) :=
  (fcFiniteCompletedOpenCover g a).map_prop ⟨l, hl⟩

/-- The actual completed chart inclusion retains the entire original
completed-field structure map. -/
theorem fcFiniteCompletedChartMap_structure (l : Fin (n + 1)) (hl : g l ≠ 0) :
    fcFiniteCompletedChartMap g a l hl ≫
      SchemeCompletedFibre.affineBaseStructureMap (fcFiniteProjection g) a =
        SchemeCompletedFibre.affineStructureMap
          (B := blowupChart (Finset.univ.image g) (g l)) a := by
  change ((fcFiniteCompletedChartIso g a l hl).hom ≫
    pullback.map (fcFinitePaperChartImmersion g l hl ≫ fcFiniteProjection g)
      (Spec.map (CommRingCat.ofHom a.toH)) (fcFiniteProjection g)
      (Spec.map (CommRingCat.ofHom a.toH)) (fcFinitePaperChartImmersion g l hl)
      (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ pullback.snd _ _ = pullback.snd _ _
  simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id,
    fcFiniteCompletedChartIso, pullback.congrHom_hom]

/-- The entire original scheme projection from every completed chart
commutes with the actual same original paper-chart immersion. -/
theorem fcFiniteCompletedChartMap_projection (l : Fin (n + 1)) (hl : g l ≠ 0) :
    fcFiniteCompletedChartMap g a l hl ≫
      SchemeCompletedFibre.affineBaseProjection (fcFiniteProjection g) a =
        SchemeCompletedFibre.affineProjection
          (B := blowupChart (Finset.univ.image g) (g l)) a ≫ fcFinitePaperChartImmersion g l hl := by
  change ((fcFiniteCompletedChartIso g a l hl).hom ≫
    pullback.map (fcFinitePaperChartImmersion g l hl ≫ fcFiniteProjection g)
      (Spec.map (CommRingCat.ofHom a.toH)) (fcFiniteProjection g)
      (Spec.map (CommRingCat.ofHom a.toH)) (fcFinitePaperChartImmersion g l hl)
      (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ fcFinitePaperChartImmersion g l hl
  simp only [Category.assoc, pullback.map, pullback.lift_fst]
  rw [← Category.assoc]
  simp only [fcFiniteCompletedChartIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

/-- The actual completed-fibre comparisons commute on entire native points
with the original genuine fraction-chart map, not just on supports. -/
theorem fcFiniteCompletedChartMap_native_commutes (l : Fin (n + 1)) (hl : g l ≠ 0)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (SchemeCompletedFibre.affineStructureMap
        (B := blowupChart (Finset.univ.image g) (g l)) a)) :
    SchemeCompletedFibre.affineBaseFibreHomeomorph (fcFiniteProjection g) a
      (RelativeSchemeValuedPoint.map (fcFiniteCompletedChartMap g a l hl)
        (fcFiniteCompletedChartMap_structure g a l hl) y) =
      RelativeSchemeValuedPoint.map (v := a.val) (fcFinitePaperChartImmersion g l hl)
        (fcFinitePaperChartImmersion_comp_projection g l hl)
        (SchemeCompletedFibre.affineFibreHomeomorph
          (B := blowupChart (Finset.univ.image g) (g l)) a y) := by
  apply Subtype.ext
  rw [SchemeCompletedFibre.affineBaseFibreHomeomorph_apply]
  change SchemeValuedPoint.map (SchemeCompletedFibre.affineBaseProjection (fcFiniteProjection g) a)
    (SchemeValuedPoint.map (fcFiniteCompletedChartMap g a l hl) y.1) =
      SchemeValuedPoint.map (fcFinitePaperChartImmersion g l hl)
        ((SchemeCompletedFibre.affineFibreHomeomorph
          (B := blowupChart (Finset.univ.image g) (g l)) a y).1)
  rw [SchemeCompletedFibre.affineFibreHomeomorph_apply,
    ← SchemeValuedPoint.map_comp, fcFiniteCompletedChartMap_projection, SchemeValuedPoint.map_comp]

end EnvelopeProperty.ReesPresentation
