import EnvelopeProperty.Berkovich.GradedNativeValuedPoints

/-! # Whole genuine native homogeneous-away charts and their original values -/
open scoped Classical NNReal Topology
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelevantGradedSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The WHOLE actual native support-open homogeneous chart is the entire
original homogeneous-away seminorm spectrum via its actual scheme iso. -/
def nativeAwayHomeomorph (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    {y : SchemeValuedPoint (Proj 𝒜) // y.point ∈ Proj.basicOpen 𝒜 f} ≃ₜ
      Spectrum (HomogeneousLocalization.Away 𝒜 f) :=
  (SchemeValuedPoint.restrictionHomeomorph (Proj.basicOpen 𝒜 f)).symm.trans
    ((SchemeValuedPoint.isoHomeomorph (Proj.basicOpenIsoSpec 𝒜 f hf hd)).trans
      SchemeValuedPoint.spectrumHomeomorph)

/-- EVERY original fraction value under the whole genuine native chart is
the actual evaluation of its SAME original awayToSection section. -/
theorem nativeAwayHomeomorph_val (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (y : {y : SchemeValuedPoint (Proj 𝒜) // y.point ∈ Proj.basicOpen 𝒜 f})
    (q : HomogeneousLocalization.Away 𝒜 f) :
    (nativeAwayHomeomorph 𝒜 f hf hd y).val q =
      SchemeValuedPoint.eval y.1 (Proj.basicOpen 𝒜 f) y.2 (Proj.awayToSection 𝒜 f q) := by
  let U := Proj.basicOpen 𝒜 f
  let z := (SchemeValuedPoint.restrictionHomeomorph U).symm y
  have hz : SchemeValuedPoint.map U.ι z = y.1 :=
    congrArg Subtype.val ((SchemeValuedPoint.restrictionHomeomorph U).apply_symm_apply y)
  change (SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.map (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom z)).val q = _
  rw [SchemeValuedPoint.spectrumHomeomorph_val_apply, SchemeValuedPoint.evalTop_map]
  have hs : (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom.appTop
      ((Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).inv q) =
      U.topIso.inv (Proj.awayToSection 𝒜 f q) := by
    rw [Proj.basicOpenIsoSpec_hom]
    change (Proj.basicOpenToSpec 𝒜 f).app ⊤ _ = _
    rw [Proj.basicOpenToSpec_app_top]
    change U.topIso.inv (Proj.awayToSection 𝒜 f
      ((Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).hom
        ((Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).inv q))) = _
    rw [Iso.inv_hom_id_apply]
  rw [hs]
  have he := SchemeValuedPoint.eval_map_ι_topIso U z (Proj.awayToSection 𝒜 f q)
  simpa only [hz] using he.symm

/-- The canonical actual native point has the ENTIRE original localized
fraction seminorm under the whole genuine homogeneous chart. -/
theorem nativeAwayHomeomorph_nativePoint (x : RelevantGradedSpectrum 𝒜)
    (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hx : support x ∈ Proj.basicOpen 𝒜 f) :
    nativeAwayHomeomorph 𝒜 f hf hd ⟨nativePoint x,hx⟩ =
      Spectrum.comap (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
        (Spectrum.awayLift f x.1 hx) := by
  apply Spectrum.ext_val
  intro q
  rw [nativeAwayHomeomorph_val, nativePoint_eval_awayToSection x f hf hx]
  rfl
/-- EVERY genuine native homogeneous-away point is recovered by the whole
actual native chart, with its SAME entire original affine seminorm. -/
theorem nativeAwayHomeomorph_map_awayι (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (z : SchemeValuedPoint (Spec (.of (HomogeneousLocalization.Away 𝒜 f)))) :
    nativeAwayHomeomorph 𝒜 f hf hd
      ⟨SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd) z, by
        have h : (Proj.awayι 𝒜 f hf hd) z.point ∈ (Proj.awayι 𝒜 f hf hd).opensRange :=
          ⟨z.point,rfl⟩
        simpa only [Proj.opensRange_awayι,SchemeValuedPoint.map_point] using h⟩ =
      SchemeValuedPoint.spectrumHomeomorph z := by
  have h : (⟨SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd) z, by
      have h : (Proj.awayι 𝒜 f hf hd) z.point ∈ (Proj.awayι 𝒜 f hf hd).opensRange :=
        ⟨z.point,rfl⟩
      simpa only [Proj.opensRange_awayι,SchemeValuedPoint.map_point] using h⟩ :
      {y : SchemeValuedPoint (Proj 𝒜) // y.point ∈ Proj.basicOpen 𝒜 f}) =
    SchemeValuedPoint.restrictionHomeomorph (Proj.basicOpen 𝒜 f)
      (SchemeValuedPoint.map (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv z) := by
    apply Subtype.ext
    change SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd) z =
      SchemeValuedPoint.map (Proj.basicOpen 𝒜 f).ι
        (SchemeValuedPoint.map (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv z)
    rw [← SchemeValuedPoint.map_comp]
    rfl
  rw [h]
  dsimp only [nativeAwayHomeomorph,Homeomorph.trans_apply]
  rw [Homeomorph.symm_apply_apply]
  change SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.map (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom
      (SchemeValuedPoint.map (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv z)) = _
  rw [← SchemeValuedPoint.map_comp,Iso.inv_hom_id,SchemeValuedPoint.map_id]

/-- The canonical WHOLE original native point is exactly the actual original
homogeneous-away chart point of its genuine fraction seminorm. -/
theorem nativePoint_eq_map_awayι (x : RelevantGradedSpectrum 𝒜)
    (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hx : support x ∈ Proj.basicOpen 𝒜 f) :
    nativePoint x = SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd)
      (SchemeValuedPoint.spectrumHomeomorph.symm
        (Spectrum.comap (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
          (Spectrum.awayLift f x.1 hx))) := by
  let z := SchemeValuedPoint.spectrumHomeomorph.symm
    (Spectrum.comap (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
      (Spectrum.awayLift f x.1 hx))
  have hz : (SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd) z).point ∈ Proj.basicOpen 𝒜 f := by
    have h : (Proj.awayι 𝒜 f hf hd) z.point ∈ (Proj.awayι 𝒜 f hf hd).opensRange := ⟨z.point,rfl⟩
    simpa only [Proj.opensRange_awayι,SchemeValuedPoint.map_point] using h
  have h : nativeAwayHomeomorph 𝒜 f hf hd ⟨nativePoint x,hx⟩ =
      nativeAwayHomeomorph 𝒜 f hf hd ⟨SchemeValuedPoint.map (Proj.awayι 𝒜 f hf hd) z,hz⟩ := by
    rw [nativeAwayHomeomorph_nativePoint,nativeAwayHomeomorph_map_awayι]
    exact (SchemeValuedPoint.spectrumHomeomorph.apply_symm_apply _).symm
  exact congrArg Subtype.val ((nativeAwayHomeomorph 𝒜 f hf hd).injective h)
end EnvelopeProperty.Berkovich.RelevantGradedSpectrum
