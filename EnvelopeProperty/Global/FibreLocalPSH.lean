/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupDescentCharts
import EnvelopeProperty.Global.FibreModel
import EnvelopeProperty.Berkovich.ExtensionLifts
import EnvelopeProperty.Berkovich.SchemeAffineLocalPSH
import EnvelopeProperty.Berkovich.SchemeLocalPSHAlgebra

/-!
# Local plurisubharmonicity of an arbitrary blowup potential

For any `Φ ∈ PSH(B, (a, 0))`, the normalized potential on every actual Rees
chart is a decreasing limit of convex PL functions. This is the chartwise
producer for `lem:fc-fibre-psh`, Fang–Han–Xia Lemma 5.4(2), without a
hypothesis that Φ descends through the blowup projection. The completed-field
fibre identification is a separate producer.
-/

open scoped NNReal ENNReal Topology
open Topology Filter MvPolynomial
noncomputable section
namespace EnvelopeProperty
universe u
open ProjBerk (QuotChartAlg)

section CompletedAffineFibre
open scoped TensorProduct
variable {k A C : Type u} [Field k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    (x : Berk k A)

set_option backward.isDefEq.respectTransparency false in
/-- Original affine convex PL presentations restrict to the genuine
completed-field tensor fibre with coefficients `1 ⊗ c`. -/
theorem IsConvexPLOn.fc_comp_completedFibre
    {U : Set (Berk k C)} {u : Berk k C → EReal} (hu : IsConvexPLOn U u) :
    Berkovich.RelativeSpectrum.IsConvexPLOn (Berk.fcCompletedFibreInclusion x ⁻¹' U)
      (fun z => u (Berk.fcCompletedFibreInclusion x z)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, n, a, s, hs, ha, hform⟩ :=
    hu (Berk.fcCompletedFibreInclusion x y) hy
  refine ⟨Berk.fcCompletedFibreInclusion x ⁻¹' W,
    hW.preimage (Berk.continuous_fcCompletedFibreInclusion x), hyW,
    Set.preimage_mono hWU, n, (fun i => (1 : Berk.H x) ⊗ₜ[A] a i), s, hs, ?_, ?_⟩
  · intro z hz i
    exact ha (Berk.fcCompletedFibreInclusion x z) hz i
  · intro z hz
    exact hform (Berk.fcCompletedFibreInclusion x z) hz

set_option backward.isDefEq.respectTransparency false in
/-- A decreasing convex PL sequence restricts termwise to the actual fibre. -/
theorem IsDecrConvexPLLimitOn.fc_comp_completedFibre
    {U : Set (Berk k C)} {u : Berk k C → EReal} (hu : IsDecrConvexPLLimitOn U u) :
    Berkovich.RelativeSpectrum.IsDecrConvexPLLimitOn
      (Berk.fcCompletedFibreInclusion x ⁻¹' U)
      (fun z => u (Berk.fcCompletedFibreInclusion x z)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨fun j z => a j (Berk.fcCompletedFibreInclusion x z),
    fun j => (ha j).fc_comp_completedFibre x,
    fun z hz => hanti _ hz, fun z hz => hlim _ hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Locally psh functions restrict to the genuine completed-residue-field
fibre without any constancy or descent assumption. -/
theorem IsLocallyPSHOn.fc_comp_completedFibre
    {U : Set (Berk k C)} {u : Berk k C → EReal} (hu : IsLocallyPSHOn U u) :
    Berkovich.RelativeSpectrum.IsLocallyPSHOn
      (Berk.fcCompletedFibreInclusion x ⁻¹' U)
      (fun z => u (Berk.fcCompletedFibreInclusion x z)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (Berk.fcCompletedFibreInclusion x y) hy
  exact ⟨Berk.fcCompletedFibreInclusion x ⁻¹' W,
    hW.preimage (Berk.continuous_fcCompletedFibreInclusion x), hyW,
    Set.preimage_mono hWU, hloc.fc_comp_completedFibre x⟩
end CompletedAffineFibre

section NativeCompletedAffineFibre
open Berkovich
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
variable {k A C : Type u} [Field k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    (x : Berk k A)

omit [Algebra k C] [IsScalarTower k A C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual local presentations on the tensor algebra give intrinsic
regular-unit local psh presentations on the same scheme-theoretic fibre. -/
theorem fc_isLocallyPSHOn_affineNativeFibre
    {U : Set (RelativeSpectrum (NormedField.valuation (K := Spectrum.H x.toSpectrum)) (Spectrum.H x.toSpectrum ⊗[A] C))}
    {u : RelativeSpectrum (NormedField.valuation (K := Spectrum.H x.toSpectrum)) (Spectrum.H x.toSpectrum ⊗[A] C) → EReal}
    (hu : RelativeSpectrum.IsLocallyPSHOn U u) :
    RelativeSchemeValuedPoint.IsLocallyPSHOn
      (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum ⁻¹' U)
      (fun y => u (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum y)) := by
  have ht := RelativeSchemeValuedPoint.IsLocallyPSHOn.of_affineSpectrum hu
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
  change RelativeSchemeValuedPoint.IsLocallyPSHOn
    ((fun y => RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y)) ⁻¹' U)
    (fun y => u (RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y))) at hp
  have hequ : (fun y => u (RelativeSchemeValuedPoint.affineSpectrumHomeomorph (p y))) =
      (fun y => u (SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum y)) := by
    funext y
    exact congrArg u (congrFun heq y)
  simpa only [heq, hequ] using hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local psh functions on the paper affine space pull back to intrinsic
regular-unit local psh functions on its actual completed scheme fibre. -/
theorem IsLocallyPSHOn.fc_comp_nativeCompletedFibre
    {U : Set (Berk k C)} {u : Berk k C → EReal} (hu : EnvelopeProperty.IsLocallyPSHOn U u) :
    RelativeSchemeValuedPoint.IsLocallyPSHOn
      ((fun y => (Berk.fcNativeCompletedFibreHomeomorph x y).1) ⁻¹' U)
      (fun y => u (Berk.fcNativeCompletedFibreHomeomorph x y).1) :=
  fc_isLocallyPSHOn_affineNativeFibre x (hu.fc_comp_completedFibre x)

end NativeCompletedAffineFibre

namespace ProjSubvariety.BlowupCenter
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))
    [IsDomain (QuotChartAlg V.ideal (X i) 1)]

/-- The pullback of Φ to a Rees chart after trivializing its `(a, 0)` class
by the base coordinate `xᵢ`. -/
def fcChartPotential (a : ℝ) (φ : B.an → EReal)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) : EReal :=
  φ (B.chartPoint i hg hg0 w) +
    ((a * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) : ℝ) : EReal)

/-- The normalization scale is precisely the usual base-coordinate
trivialization of the `(a, 0)` class; this formula does not require Φ to descend. -/
theorem fcChartPotential_eq_baseTrivialization (a : ℝ) (φ : B.an → EReal)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    B.fcChartPotential i a φ hg hg0 w = φ (B.chartPoint i hg hg0 w) +
      -(a : EReal) * ProjBerk.logAbs (X i) (B.proj (B.chartPoint i hg hg0 w)).1 := by
  have hc := B.descentChartFun_comap_chartMap a (fun _ => 0) hg hg0 w
  simp only [descentChartFun, zero_add] at hc
  rw [← B.proj_chartPoint hg hg0 w] at hc
  exact congrArg (fun c => φ (B.chartPoint i hg hg0 w) + c) hc.symm

/-- On an actual affine algebra fibre, the normalization term of the chart
potential is the finite real constant determined by its base point. -/
theorem fcChartPotential_eq_on_affineFibre (a : ℝ) (φ : B.an → EReal)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (t : Berk k (QuotChartAlg V.ideal (X i) 1))
    (w : Berk k (blowupChart (B.centerSet i) g))
    (hw : Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w = t) :
    B.fcChartPotential i a φ hg hg0 w = φ (B.chartPoint i hg hg0 w) +
      (((a * Real.log ((Finset.univ.sup fun j =>
        t.val (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) : ℝ≥0) : ℝ)) : ℝ) : EReal) := by
  unfold fcChartPotential
  rw [B.scaleX_chartHom, hw]

/-- Dyadic finite Fubini–Study approximants, read on an actual Rees chart,
produce a decreasing convex PL sequence for every blowup psh potential. -/
theorem fc_isDecrConvexPLLimitOn_chartPotential [Countable k] {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsDecrConvexPLLimitOn Set.univ (B.fcChartPotential i a φ hg hg0) := by
  have : Algebra.FiniteType k (QuotChartAlg V.ideal (X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (isHomogeneous_X k i)
  have h' : B.IsPSH ![((a : ℚ) : ℝ), ((0 : ℚ) : ℝ)] φ := by
    rw [Rat.cast_zero]
    exact h
  obtain ⟨Φ, hΦ, hanti, hlim⟩ := h'.exists_isFinFS_seq_dyadic
  choose D hDrat hDne hDeq using fun j => isFinFS_iff.1 (hΦ j)
  have hG : ∀ (j : ℕ) (w : Berk k (blowupChart (B.centerSet i) g)),
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) =
        Φ j (B.chartPoint i hg hg0 w) +
          (((((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
            ((((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := fun j w =>
    (B.sup_fsTerm_chartTerms hg hg0 (D j) (hDrat j) w).trans
      (congrArg (· + _) (hDeq j _).symm)
  have hGanti : ∀ w : Berk k (blowupChart (B.centerSet i) g), Antitone fun j =>
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
    intro w j j' hjj'
    exact (hG j' w).trans_le ((add_le_add (hanti _ hjj') (EReal.coe_le_coe_iff.2
      (antitone_dyadic_coeff a (B.log_scaleX_chartHom_nonneg g w)
        (B.log_scaleY_chartHom_nonneg hg hg0 w) hjj'))).trans_eq (hG j w).symm)
  refine ⟨fun j => ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
    (B.chartTerms_pos g (D j))).eval,
    fun j => ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
      (B.chartTerms_pos g (D j))).isConvexPLOn_univ,
    fun w _ j j' hjj' => ?_, fun w _ => ?_⟩
  · simp only [FSData.eval_addTerms]
    exact max_le_max (FSData.antitone_truncStd k _ w hjj') (hGanti w hjj')
  · show B.fcChartPotential i a φ hg hg0 w =
      ⨅ j, ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w
    have hlx := B.log_scaleX_chartHom_nonneg g w
    have hly := B.log_scaleY_chartHom_nonneg hg hg0 w
    have hr : ⨅ j : ℕ, (((((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
        ((((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) =
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) : ℝ) : EReal) :=
      iInf_eq_of_tendsto_of_antitone
        (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly hjj'))
        ((continuous_coe_real_ereal.tendsto _).comp (tendsto_dyadic_coeff a _ _))
    have hsum := iInf_add_of_antitone (hanti (B.chartPoint i hg hg0 w))
      (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly hjj'))
      ((hΦ 0).isFS.ne_top _) (EReal.coe_ne_top _)
    have e1 : (⨅ j, ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w) =
        ⨅ j, ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
      rw [← FSData.iInf_max_truncStd k _ (hGanti w) w]
      refine iInf_congr fun j => ?_
      rw [FSData.eval_addTerms, max_comm]
    rw [e1, fcChartPotential, ← hr, hlim, ← hsum]
    exact iInf_congr fun j => (hG j w).symm

/-- Every blowup psh potential is locally psh on each Rees chart after
trivializing the class by `xᵢ`. No descent assumption on the potential is used. -/
theorem fc_isLocallyPSHOn_chartPotential [Countable k] {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsLocallyPSHOn Set.univ (B.fcChartPotential i a φ hg hg0) :=
  (B.fc_isDecrConvexPLLimitOn_chartPotential i h hg hg0).isLocallyPSHOn
    isOpen_univ (Set.subset_univ _)

/-- The normalized arbitrary psh potential is locally psh on the actual
completed-field tensor algebra of each Rees chart in the fibre. -/
theorem fc_isLocallyPSHOn_completedChartFibre [Countable k] {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (t : Berk k (QuotChartAlg V.ideal (X i) 1)) :
    Berkovich.RelativeSpectrum.IsLocallyPSHOn Set.univ
      (fun z => B.fcChartPotential i a φ hg hg0 (Berk.fcCompletedFibreInclusion t z)) := by
  simpa only [Set.preimage_univ] using
    (B.fc_isLocallyPSHOn_chartPotential i h hg hg0).fc_comp_completedFibre t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the actual completed scheme fibre of a Rees chart, the original
blowup potential itself is intrinsically locally psh. Its base-coordinate
normalization is a single finite real constant on that fibre. -/
theorem fc_isLocallyPSHOn_nativeChartFibre [Countable k] {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (t : Berk k (QuotChartAlg V.ideal (X i) 1)) :
    Berkovich.RelativeSchemeValuedPoint.IsLocallyPSHOn Set.univ
      (fun z => φ (B.chartPoint i hg hg0 (Berk.fcNativeCompletedFibreHomeomorph t z).1)) := by
  have hN := (B.fc_isLocallyPSHOn_chartPotential i h hg hg0).fc_comp_nativeCompletedFibre t
  simp only [Set.preimage_univ] at hN
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
  have hfun :
      (fun z => B.fcChartPotential i a φ hg hg0 (Berk.fcNativeCompletedFibreHomeomorph t z).1 +
        ((-c : ℝ) : EReal)) =
      (fun z => φ (B.chartPoint i hg hg0 (Berk.fcNativeCompletedFibreHomeomorph t z).1)) :=
    funext fun z => hcancel _ (Berk.fcNativeCompletedFibreHomeomorph t z).2
  rw [hfun] at hraw
  exact hraw

end ProjSubvariety.BlowupCenter
end EnvelopeProperty
