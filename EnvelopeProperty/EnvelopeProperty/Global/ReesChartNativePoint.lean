/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ReesFiniteCoordinateNativeCharts

/-!
# The actual whole native image of each original normalized Rees chart point

The genuine projective coordinate inverse and the true scheme-chart
triangle identify constructed normalized chart seminorms with the same
whole native Rees chart images. This is the compatibility needed to glue
intrinsic local psh presentations on the actual completed scheme fibre.
-/

open scoped Classical NNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.ReesPresentation
variable {A : Type u} [CommRing A] [IsDomain A] {n : ℕ} (g : Fin (n + 1) → A)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The normalized chart construction has exactly the original whole native
point of the actual fraction chart followed by the true Rees immersion. -/
theorem fcFinitePaperNormalizedPoint_nativePoint (l : Fin (n + 1)) (hl : g l ≠ 0)
    (w : Spectrum (blowupChart (Finset.univ.image g) (g l))) :
    NormalizedProjectiveSpectrum.nativePoint
      (fcPaperNormalizedPoint (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l w) =
      SchemeValuedPoint.map (fcFinitePaperChartImmersion g l hl ≫ fcFiniteImmersion g)
        (SchemeValuedPoint.spectrumHomeomorph.symm w) := by
  let P := blowupChart (Finset.univ.image g) (g l)
  let f := fcPaperCoordinateDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l
  let z := Spectrum.comap f.toRingHom w
  let v := (Spectrum.comap (algebraMap A P) w).val
  let zr : RelativeSpectrum v (ProjBerk.CoordinateRing A l) := ⟨z, by
    intro a
    change w.val (f (algebraMap A (ProjBerk.CoordinateRing A l) a)) = w.val (algebraMap A P a)
    rw [f.commutes]⟩
  let q := (RelativeNormalizedProjectiveSpectrum.coordinateChartHomeomorph v l).symm zr
  have hq : q.1.1 = fcPaperNormalizedPoint (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l w := by
    apply Subtype.ext
    exact RelativeNormalizedProjectiveSpectrum.coordinateChartHomeomorph_symm_coe v l zr
  have hn := RelativeNormalizedProjectiveSpectrum.nativePoint_eq_chart_inverse v l q
  have hc : RelativeNormalizedProjectiveSpectrum.coordinateChartHomeomorph v l q = zr :=
    Homeomorph.apply_symm_apply _ _
  rw [hc, ProjBerk.nativeCoordinateSpectrumHomeomorph_symm_coe, hq] at hn
  have ha : SchemeValuedPoint.spectrumHomeomorph.symm zr.1 =
      SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom f.toRingHom))
        (SchemeValuedPoint.spectrumHomeomorph.symm w) := by
    apply SchemeValuedPoint.spectrumHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, SchemeValuedPoint.spectrumHomeomorph_map,
      Homeomorph.apply_symm_apply]
  rw [fcFinitePaperChartImmersion_comp_immersion, SchemeValuedPoint.map_comp]
  exact hn.trans (congrArg (SchemeValuedPoint.map (ProjBerk.nativeCoordinateInclusion l)) ha)

/-- The actual native kernel-locus comparison of the whole original native
Rees chart image is exactly the constructed original normalized chart point. -/
theorem fcNativeNormalizedHomeomorph_map_paperChart (v : Valuation A ℝ≥0)
    (l : Fin (n + 1)) (hl : g l ≠ 0)
    (x : RelativeSchemeValuedPoint v
      (Spec.map (CommRingCat.ofHom (algebraMap A (blowupChart (Finset.univ.image g) (g l)))))) :
    (fcNativeNormalizedHomeomorph g v
      (RelativeSchemeValuedPoint.map (fcFinitePaperChartImmersion g l hl)
        (fcFinitePaperChartImmersion_comp_projection g l hl) x)).1.1 =
      fcPaperNormalizedPoint (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l
        (SchemeValuedPoint.spectrumHomeomorph x.1) := by
  apply NormalizedProjectiveSpectrum.nativePoint_injective
  have hn := congrArg Subtype.val (fcNativeNormalizedHomeomorph_apply g v
    (RelativeSchemeValuedPoint.map (fcFinitePaperChartImmersion g l hl)
      (fcFinitePaperChartImmersion_comp_projection g l hl) x))
  change NormalizedProjectiveSpectrum.nativePoint _ =
    SchemeValuedPoint.map (fcFiniteImmersion g)
      (SchemeValuedPoint.map (fcFinitePaperChartImmersion g l hl) x.1) at hn
  rw [fcFinitePaperNormalizedPoint_nativePoint g l hl, Homeomorph.symm_apply_apply,
    SchemeValuedPoint.map_comp]
  exact hn

end EnvelopeProperty.ReesPresentation
