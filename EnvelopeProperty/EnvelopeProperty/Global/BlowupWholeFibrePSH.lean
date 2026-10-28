/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupCompletedFibreNative
import EnvelopeProperty.Global.ReesFiniteCompletedCharts
import EnvelopeProperty.Global.FibreLocalPSH
import EnvelopeProperty.Berkovich.SchemeOpenLocalPSH

/-!
# Intrinsic local psh on the whole actual completed-field blowup fibre

The actual completed original Rees chart cover is compatible with the
constructed whole old-fibre homeomorphism. The previously proved intrinsic
raw chart psh presentations therefore glue on that genuine scheme cover.
No fibrewise descent, local-psh atlas certificate or constancy is assumed.
-/

open scoped Classical NNReal Topology
open Topology MvPolynomial CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1)

section DomainChart
variable [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole completed-fibre homeomorphism agrees on every actual
completed original Rees chart with the entire original chart point map. -/
theorem fcAffineCompletedFibreHomeomorph_chartMap
    (l : Fin (M' + 1)) (hl : B.centerGen i l ≠ 0)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H
      (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum))
      (SchemeCompletedFibre.affineStructureMap
        (B := blowupChart (B.centerSet i) (B.centerGen i l))
          (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum)) :
    (B.fcAffineCompletedFibreHomeomorph t i hi
      (RelativeSchemeValuedPoint.map
        (ReesPresentation.fcFiniteCompletedChartMap (B.centerGen i)
          (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum l hl)
        (ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i)
          (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum l hl) y)).1 =
      B.chartPoint i (B.centerGen_mem_centerSet i l) hl
        (Berk.fcNativeCompletedFibreHomeomorph
          (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)) y).1 := by
  let a := V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)
  let w := Berk.fcNativeCompletedFibreHomeomorph a y
  have hn := ReesPresentation.fcNativeNormalizedHomeomorph_map_paperChart
    (B.centerGen i) a.val l hl
    (SchemeCompletedFibre.affineFibreHomeomorph
      (B := blowupChart (B.centerSet i) (B.centerGen i l)) a.toSpectrum y)
  have hp := Berk.fcNativeCompletedFibreHomeomorph_projection a y
  have hs := congrArg SchemeValuedPoint.spectrumHomeomorph
    (SchemeCompletedFibre.affineFibreHomeomorph_apply
      (B := blowupChart (B.centerSet i) (B.centerGen i l)) a.toSpectrum y)
  have hnorm := hn.trans (congrArg
    (ReesPresentation.fcPaperNormalizedPoint (B.centerSet i) (B.centerGen i)
      (B.centerGen_mem_centerSet i) l) (hs.trans hp.symm))
  have hq :
      (ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i) a.val
        (RelativeSchemeValuedPoint.map
          (ReesPresentation.fcFinitePaperChartImmersion (B.centerGen i) l hl)
          (ReesPresentation.fcFinitePaperChartImmersion_comp_projection (B.centerGen i) l hl)
          (SchemeCompletedFibre.affineFibreHomeomorph
            (B := blowupChart (B.centerSet i) (B.centerGen i l)) a.toSpectrum y))).1 =
        (B.fcChartNormalizedReesPoint i t hi l hl w.1 w.2).1 :=
    Subtype.ext hnorm
  have hcompat :
      (B.fcNativeFibreHomeomorph i t hi
        (RelativeSchemeValuedPoint.map
          (ReesPresentation.fcFinitePaperChartImmersion (B.centerGen i) l hl)
          (ReesPresentation.fcFinitePaperChartImmersion_comp_projection (B.centerGen i) l hl)
          (SchemeCompletedFibre.affineFibreHomeomorph
            (B := blowupChart (B.centerSet i) (B.centerGen i l)) a.toSpectrum y))).1 =
        B.chartPoint i (B.centerGen_mem_centerSet i l) hl w.1 := by
    apply Subtype.ext
    exact (congrArg (fcAffineProjectivePoint t i hi) hq).trans
      (B.fcAffineProjectivePoint_fcChartNormalizedReesPoint i t hi l hl w.1 w.2)
  exact (congrArg (fun z => (B.fcNativeFibreHomeomorph i t hi z).1)
    (ReesPresentation.fcFiniteCompletedChartMap_native_commutes
      (B.centerGen i) a.toSpectrum l hl y)).trans hcompat

end DomainChart

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual original blowup psh potential is intrinsically locally psh
on the whole actual proper completed-field scheme fibre. The actual cover,
comparison and local presentations are constructed, not assumed. -/
theorem fc_isLocallyPSHOn_wholeCompletedFibre [Countable k] {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ) :
    RelativeSchemeValuedPoint.IsLocallyPSHOn Set.univ
      (fun y => φ (B.fcAffineCompletedFibreHomeomorph t i hi y).1) := by
  let := fc_isDomain_baseChart t i hi
  let b := V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)
  let 𝒰 := ReesPresentation.fcFiniteCompletedOpenCover (B.centerGen i) b.toSpectrum
  apply RelativeSchemeValuedPoint.IsLocallyPSHOn.of_openCover 𝒰
    (fun l => SchemeCompletedFibre.affineStructureMap
      (B := blowupChart (B.centerSet i) (B.centerGen i l.1)) b.toSpectrum)
    (fun l => ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i) b.toSpectrum l.1 l.2)
  intro l
  simp only [Set.preimage_univ]
  have hchart := B.fc_isLocallyPSHOn_nativeChartFibre i h
    (B.centerGen_mem_centerSet i l.1) l.2 b
  have hfun :
      (fun y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H b.toSpectrum))
        (SchemeCompletedFibre.affineStructureMap
          (B := blowupChart (B.centerSet i) (B.centerGen i l.1)) b.toSpectrum) =>
        φ (B.fcAffineCompletedFibreHomeomorph t i hi
          (RelativeSchemeValuedPoint.map
            (ReesPresentation.fcFiniteCompletedChartMap (B.centerGen i) b.toSpectrum l.1 l.2)
            (ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i) b.toSpectrum l.1 l.2) y)).1) =
      (fun y => φ (B.chartPoint i (B.centerGen_mem_centerSet i l.1) l.2
        (Berk.fcNativeCompletedFibreHomeomorph b y).1)) :=
    funext fun y => congrArg φ (B.fcAffineCompletedFibreHomeomorph_chartMap t i hi l.1 l.2 y)
  change RelativeSchemeValuedPoint.IsLocallyPSHOn Set.univ
    (fun y => φ (B.fcAffineCompletedFibreHomeomorph t i hi
      (RelativeSchemeValuedPoint.map
        (ReesPresentation.fcFiniteCompletedChartMap (B.centerGen i) b.toSpectrum l.1 l.2)
        (ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i) b.toSpectrum l.1 l.2) y)).1)
  exact hfun.symm ▸ hchart

end EnvelopeProperty.ProjSubvariety.BlowupCenter
