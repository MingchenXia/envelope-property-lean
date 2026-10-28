import EnvelopeProperty.AlgGeom.NativeAdmissibleChartBase
import EnvelopeProperty.AlgGeom.NativeAdmissibleChartFractions
import EnvelopeProperty.Berkovich.GradedNativeAwayCharts

/-! # Whole original admissible analytic charts are their actual native scheme charts -/
open scoped Classical NNReal
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.ProjBerk EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] nativeQuotientAwayAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance qgr : GradedRing (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous

/-- The literal whole original ambient homogeneous-away ring map to the
SAME original admissible quotient algebra, with its actual quotient map. -/
def nativeAdmissibleAmbientChartHom {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    Away (ProjectiveGrading k n) F →+* QuotChartAlg X.ideal F d :=
  (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.symm.toRingHom.comp
    (Away.map (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal) F)

/-- EVERY original whole homogeneous fraction maps to the SAME original
quotient-chart numerator, not merely to an element with the same ideal. -/
theorem nativeAdmissibleAmbientChartHom_mk
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (m : ℕ)
    (G : MvPolynomial (Fin (n+1)) k) (hG : G.IsHomogeneous (m*d)) :
    X.nativeAdmissibleAmbientChartHom hF hFI (Away.mk (ProjectiveGrading k n)
      hF m G (by simpa only [smul_eq_mul,ProjectiveGrading,MvPolynomial.mem_homogeneousSubmodule] using hG)) =
      quotChartMk X.ideal F d m G := by
  unfold nativeAdmissibleAmbientChartHom
  change (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.symm
    (Away.map (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal) F _) = _
  erw [Away.map_mk]
  apply (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.injective
  rw [RingEquiv.apply_symm_apply]
  exact (X.quotChartNativeAwayEquiv_quotChartMk hF hFI m G hG).symm

private def chartRingIso {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    CommRingCat.of (QuotChartAlg X.ideal F d) ≅ CommRingCat.of (X.nativeQuotientAway F) :=
  (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.toCommRingCatIso

/-- The WHOLE actual arbitrary admissible native chart/inclusion square is
the spectrum of the SAME original ambient fraction homomorphism. -/
theorem nativeAdmissibleChartMap_inclusion
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    X.nativeAdmissibleChartMap hF hFI hd ≫ X.nativeInclusion =
      Spec.map (CommRingCat.ofHom
        (R := Away (ProjectiveGrading k n) F) (S := QuotChartAlg X.ideal F d)
        (X.nativeAdmissibleAmbientChartHom (F := F) (d := d) hF hFI)) ≫
        Proj.awayι (ProjectiveGrading k n) F hF hd := by
  dsimp only [nativeAdmissibleChartMap]
  rw [Category.assoc,Category.assoc,X.quotientNativeIso_inclusion]
  change (Scheme.Spec.mapIso (chartRingIso X hF hFI).op).inv ≫
    Proj.awayι (GradedQuotient.grading (ProjectiveGrading k n) X.ideal)
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal) F)
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hF) hd ≫
        Proj.map (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal)
          (GradedQuotient.irrelevant_le_map (ProjectiveGrading k n) X.homogeneousIdeal) = _
  rw [Proj.awayι_comp_map,← Category.assoc,Functor.mapIso_inv]
  change (Scheme.Spec.map (chartRingIso X hF hFI).op.inv ≫
    Scheme.Spec.map (CommRingCat.ofHom
      (Away.map (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal) F)).op) ≫
      Proj.awayι (ProjectiveGrading k n) F hF hd = _
  rw [← Scheme.Spec.map_comp]
  rfl

private theorem chartInv_fractionSpectrum
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (z : Berk k (QuotChartAlg X.ideal F d)) :
    Spectrum.comap (algebraMap (Away (ProjectiveGrading k n) F) (Localization.Away F))
      (Spectrum.awayLift F
        (normalizedSpectrumHomeomorph (X.chartInv F d hF hd z).1).1.1
        (X.chartInv_val_ne_zero hF hd z)) =
      Spectrum.comap (A := Away (ProjectiveGrading k n) F)
        (B := QuotChartAlg X.ideal F d)
        (X.nativeAdmissibleAmbientChartHom (F := F) (d := d) hF hFI) (Berk.toSpectrum z) := by
  apply Spectrum.ext_val
  intro q
  obtain ⟨m,G,hG,rfl⟩ := Away.mk_surjective (ProjectiveGrading k n) hF q
  have hGh : G.IsHomogeneous (m*d) := by
    simpa only [smul_eq_mul,ProjectiveGrading,MvPolynomial.mem_homogeneousSubmodule] using hG
  change (Spectrum.awayLift F
    (normalizedSpectrumHomeomorph (X.chartInv F d hF hd z).1).1.1
    (X.chartInv_val_ne_zero hF hd z)).val
      (Away.mk (ProjectiveGrading k n) hF m G hG).val =
        z.val (X.nativeAdmissibleAmbientChartHom (F := F) (d := d) hF hFI (Away.mk (ProjectiveGrading k n) hF m G hG))
  rw [X.nativeAdmissibleAmbientChartHom_mk hF hFI m G hGh,
    Away.val_mk,Localization.mk_eq_mk']
  change (Spectrum.Away.lift (Localization.Away F) F
    (normalizedSpectrumHomeomorph (X.chartInv F d hF hd z).1).1.1
    (X.chartInv_val_ne_zero hF hd z)).val _ = _
  rw [Spectrum.Away.lift_val_mk']
  have h := X.chartMap_val_quotChartMk (σ := F) (d := d)
    (X.chartInv F d hF hd z) (X.chartInv_val_ne_zero hF hd z) hGh
  rw [X.chartMap_chartInv hF hd z] at h
  exact h.symm

/-- The ORIGINAL admissible analytic chart inverse is LITERALLY the WHOLE
actual native scheme chart map on the SAME original affine seminorm point.
Original residue valuations are retained; no preservation premise is added. -/
theorem nativeAnalyticHomeomorph_chartInv
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (z : Berk k (QuotChartAlg X.ideal F d)) :
    (X.nativeAnalyticHomeomorph (X.chartInv F d hF hd z)).1 =
      SchemeValuedPoint.map (X.nativeAdmissibleChartMap hF hFI hd)
        (SchemeValuedPoint.spectrumHomeomorph.symm (Berk.toSpectrum z)) := by
  let w := X.chartInv F d hF hd z
  let x := (normalizedSpectrumHomeomorph w.1).1
  have hx : NormalizedProjectiveSpectrum.nativeSupport x ∈ Proj.basicOpen (ProjectiveGrading k n) F :=
    X.chartInv_val_ne_zero hF hd z
  have hleft := RelevantGradedSpectrum.nativePoint_eq_map_awayι (ProjectiveGrading k n)
    (NormalizedProjectiveSpectrum.toRelevantGradedSpectrum x) F hF hd hx
  change (ProjBerk.nativeHomeomorph w.1).1 = _ at hleft
  apply SchemeValuedPoint.map_injective_of_isClosedImmersion X.nativeInclusion
  have hinc := congrArg Subtype.val (X.nativeAnalyticHomeomorph_inclusion w)
  change SchemeValuedPoint.map X.nativeInclusion _ = _ at hinc
  rw [hinc,← SchemeValuedPoint.map_comp,X.nativeAdmissibleChartMap_inclusion,
    SchemeValuedPoint.map_comp,hleft]
  apply congrArg (SchemeValuedPoint.map (Proj.awayι (ProjectiveGrading k n) F hF hd))
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [Homeomorph.apply_symm_apply,SchemeValuedPoint.spectrumHomeomorph_map,
    Homeomorph.apply_symm_apply]
  exact chartInv_fractionSpectrum X hF hFI hd z
end EnvelopeProperty.ProjSubvariety
