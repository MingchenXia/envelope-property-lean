import EnvelopeProperty.Global.FibreLocalNetPSH
import EnvelopeProperty.Global.BlowupWholeFibrePSH
import EnvelopeProperty.Berkovich.SchemeNetPSH
import EnvelopeProperty.Berkovich.SchemeNetPSHAlgebra
import EnvelopeProperty.Berkovich.SchemeOpenNetPSH

/-! # Actual whole completed blowup fibres retain directed local PL without countability -/

open scoped Classical NNReal Topology TensorProduct
open Topology MvPolynomial CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty

section NativeCompletedAffineFibre
variable {k A C : Type u} [Field k] [CommRing A] [CommRing C]
  [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
  (x : Berk k A)

omit [Algebra k C] [IsScalarTower k A C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual local presentations on the tensor algebra give intrinsic
regular-unit local psh presentations on the same scheme-theoretic fibre. -/
theorem fc_isLocallyNetPSHOn_affineNativeFibre
    {U : Set (RelativeSpectrum (NormedField.valuation (K := Spectrum.H x.toSpectrum)) (Spectrum.H x.toSpectrum ⊗[A] C))}
    {u : RelativeSpectrum (NormedField.valuation (K := Spectrum.H x.toSpectrum)) (Spectrum.H x.toSpectrum ⊗[A] C) → EReal}
    (hu : RelativeSpectrum.IsLocallyNetPSHOn U u) :
    RelativeSchemeValuedPoint.IsLocallyNetPSHOn
      (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum ⁻¹' U)
      (fun y => u (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum y)) := by
  have ht := RelativeSchemeValuedPoint.IsLocallyNetPSHOn.of_affineSpectrum hu
  have hdiag : (SchemeCompletedFibre.affineTensorIso (B := C) x.toSpectrum).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Spectrum.H x.toSpectrum) (Spectrum.H x.toSpectrum ⊗[A] C))) =
      SchemeCompletedFibre.affineStructureMap (B := C) x.toSpectrum ≫
        Spec.map (CommRingCat.ofHom (RingHom.id (Spectrum.H x.toSpectrum))) := by
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id (Spectrum.H x.toSpectrum))) =
      𝟙 (Spec (CommRingCat.of (Spectrum.H x.toSpectrum))) from Spec.map_id _, Category.comp_id]
    exact SchemeCompletedFibre.affineTensorIso_hom_structureMap (B := C) x.toSpectrum
  let p := RelativeSchemeValuedPoint.mapOverBase
    (v := NormedField.valuation (K := Spectrum.H x.toSpectrum))
    (w := NormedField.valuation (K := Spectrum.H x.toSpectrum))
    (RingHom.id (Spectrum.H x.toSpectrum)) (fun _ => rfl)
    (SchemeCompletedFibre.affineTensorIso (B := C) x.toSpectrum).hom hdiag
  have hp := ht.comp_mapOverBase
    (w := NormedField.valuation (K := Spectrum.H x.toSpectrum))
    (RingHom.id (Spectrum.H x.toSpectrum)) (fun _ => rfl)
    (SchemeCompletedFibre.affineTensorIso (B := C) x.toSpectrum).hom hdiag
  have heq : (fun y => RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y)) =
      SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum := by
    funext y
    rfl
  change RelativeSchemeValuedPoint.IsLocallyNetPSHOn
    ((fun y => RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y)) ⁻¹' U)
    (fun y => u (RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y))) at hp
  have hequ : (fun y => u (RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y))) =
      (fun y => u (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum y)) := by
    funext y
    exact congrArg u (congrFun heq y)
  simpa only [heq, hequ] using hp


end NativeCompletedAffineFibre

namespace ProjSubvariety.BlowupCenter
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
  (B : V.BlowupCenter M') (i : Fin (M + 1))
  [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- The genuine original chart PL net pulls back term by term to the actual
completed tensor fibre, without any field-countability assumption. -/
theorem fc_isLocallyNetPSHOn_completedChartFibre {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (t : Berk k (ProjBerk.QuotChartAlg V.ideal (X i) 1)) :
    RelativeSpectrum.IsLocallyNetPSHOn Set.univ
      (fun z => B.fcChartPotential i a φ hg hg0 (Berk.fcCompletedFibreInclusion t z)) := by
  obtain ⟨J, _, _, _, w, hw, hanti, hlim⟩ := B.fc_exists_convexPL_net_chartPotential i h hg hg0
  have hpresent : RelativeSpectrum.IsDecrConvexPLNetLimitOn Set.univ
      (fun z => B.fcChartPotential i a φ hg hg0 (Berk.fcCompletedFibreInclusion t z)) := by
    refine ⟨J, inferInstance, inferInstance, inferInstance,
      (fun j z => w j (Berk.fcCompletedFibreInclusion t z)), ?_, ?_, ?_⟩
    · intro j
      simpa only [Set.preimage_univ] using (hw j).fc_comp_completedFibre t
    · intro z hz
      exact hanti _
    · intro z hz
      exact hlim _
  exact hpresent.isLocallyNetPSHOn

/-- Original chart normalization is one finite real constant on the actual
completed scheme fibre, so the unchanged original potential retains a local
native directed PL presentation there. -/
theorem fc_isLocallyNetPSHOn_nativeChartFibre {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (t : Berk k (ProjBerk.QuotChartAlg V.ideal (X i) 1)) :
    Berkovich.RelativeSchemeValuedPoint.IsLocallyNetPSHOn Set.univ
      (fun z => φ (B.chartPoint i hg hg0 (Berk.fcNativeCompletedFibreHomeomorph t z).1)) := by
  have hN : RelativeSchemeValuedPoint.IsLocallyNetPSHOn
      (v := NormedField.valuation (K := Spectrum.H t.toSpectrum))
      (f := SchemeCompletedFibre.affineStructureMap
        (B := blowupChart (B.centerSet i) g) t.toSpectrum) Set.univ
      (fun z => B.fcChartPotential i a φ hg hg0
        (Berk.fcNativeCompletedFibreHomeomorph t z).1) := by
    have h0 := fc_isLocallyNetPSHOn_affineNativeFibre t
      (B.fc_isLocallyNetPSHOn_completedChartFibre i h hg hg0 t)
    have h1 : RelativeSchemeValuedPoint.IsLocallyNetPSHOn
        (v := NormedField.valuation (K := Spectrum.H t.toSpectrum))
        (f := SchemeCompletedFibre.affineStructureMap
          (B := blowupChart (B.centerSet i) g) t.toSpectrum) Set.univ
        (fun z => B.fcChartPotential i a φ hg hg0
          (Berk.fcCompletedFibreInclusion t
            (SchemeCompletedFibre.affineTensorRelativeHomeomorph
              (B := blowupChart (B.centerSet i) g) t.toSpectrum z))) := h0
    exact h1.congr (fun z hz => rfl)
  let c : ℝ := (a : ℝ) * Real.log ((Finset.univ.sup fun j =>
    t.val (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) : ℝ≥0) : ℝ)
  have hraw := hN.add_const (-c)
  have hcancel (w : Berk k (blowupChart (B.centerSet i) g))
      (hw : Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w = t) :
      B.fcChartPotential i a φ hg hg0 w + ((-c : ℝ) : EReal) =
        φ (B.chartPoint i hg hg0 w) := by
    rw [B.fcChartPotential_eq_on_affineFibre i a φ hg hg0 t w hw]
    change (φ (B.chartPoint i hg hg0 w) + (c : EReal)) + ((-c : ℝ) : EReal) = _
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  exact hraw.congr (fun z hz => hcancel _ (Berk.fcNativeCompletedFibreHomeomorph t z).2)

end ProjSubvariety.BlowupCenter
end EnvelopeProperty

namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
  (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
  (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual original blowup psh potential is intrinsically locally psh
on the whole actual proper completed-field scheme fibre. The actual cover,
comparison and local presentations are constructed, not assumed. -/
theorem fc_isLocallyNetPSHOn_wholeCompletedFibre {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ) :
    RelativeSchemeValuedPoint.IsLocallyNetPSHOn Set.univ
      (fun y => φ (B.fcAffineCompletedFibreHomeomorph t i hi y).1) := by
  let := fc_isDomain_baseChart t i hi
  let b := V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)
  let 𝒰 := ReesPresentation.fcFiniteCompletedOpenCover (B.centerGen i) b.toSpectrum
  apply RelativeSchemeValuedPoint.IsLocallyNetPSHOn.of_openCover 𝒰
    (fun l => SchemeCompletedFibre.affineStructureMap
      (B := blowupChart (B.centerSet i) (B.centerGen i l.1)) b.toSpectrum)
    (fun l => ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i) b.toSpectrum l.1 l.2)
  intro l
  simp only [Set.preimage_univ]
  have hchart := B.fc_isLocallyNetPSHOn_nativeChartFibre i h
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
  change RelativeSchemeValuedPoint.IsLocallyNetPSHOn Set.univ
    (fun y => φ (B.fcAffineCompletedFibreHomeomorph t i hi
      (RelativeSchemeValuedPoint.map
        (ReesPresentation.fcFiniteCompletedChartMap (B.centerGen i) b.toSpectrum l.1 l.2)
        (ReesPresentation.fcFiniteCompletedChartMap_structure (B.centerGen i) b.toSpectrum l.1 l.2) y)).1)
  exact hfun.symm ▸ hchart

end EnvelopeProperty.ProjSubvariety.BlowupCenter
