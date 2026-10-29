import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussLocalTotalFrame

/-! # Whole actual native frame coherence for original Gauss local model frames

Every comparison below is proved from native pullback naturality and actual
geometric triangles. No scalar, frame, norm or metric comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich Scheme.Modules CanonicalGeometry

/-- Native pullback naturality proves the ENTIRE original frame/module-iso transport identity. -/
theorem originalFrameViaFactor_mapIso {A B D : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ D) (f : A ⟶ D) (hg : g ≫ b = f)
    {M N : D.Modules} (σ : M ≅ N) (e : (pullback b).obj N ≅ unitObj B) :
    frameViaFactor g b f hg ((pullback b).mapIso σ ≪≫ e) =
      (pullback f).mapIso σ ≪≫ frameViaFactor g b f hg e := by
  have hc : (frameFactorIso g b f hg M).inv ≫
        (pullback g).map ((pullback b).map σ.hom) =
      (pullback f).map σ.hom ≫ (frameFactorIso g b f hg N).inv := by
    simpa only [frameFactorIso, Iso.trans_inv, NatTrans.comp_app, Iso.app_inv, Functor.comp_map]
      using (((pullbackComp g b) ≪≫ pullbackCongr hg).inv.naturality σ.hom).symm
  apply Iso.ext
  simp only [frameViaFactor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have h := congrArg (fun q => q ≫ (pullback g).map e.hom ≫ (pullbackUnitIso g).hom) hc
  simpa only [Category.assoc] using h

/-- The ACTUAL native isoOpensRange round trip contracts as a WHOLE frame iso. -/
theorem originalFrameViaFactor_isoOpensRange {A B Y : Scheme.{u}}
    (i : A ⟶ B) (b : B ⟶ Y) [IsOpenImmersion b] (f : A ⟶ Y) (hi : i ≫ b = f)
    {M : Y.Modules} (e : (pullback b).obj M ≅ unitObj B) :
    frameViaFactor (i ≫ b.isoOpensRange.hom) b.opensRange.ι f
        (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]; exact hi)
        (frameViaFactor b.isoOpensRange.inv b b.opensRange.ι
          (Scheme.Hom.isoOpensRange_inv_comp b) e) =
      frameViaFactor i b f hi e := by
  have h := frameViaFactor_comp (i ≫ b.isoOpensRange.hom) b.isoOpensRange.inv b
    b.opensRange.ι (Scheme.Hom.isoOpensRange_inv_comp b) f
    (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]; exact hi) e
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The inverse ACTUAL pullbackComp pairing commutes with native whole frame transport. -/
theorem originalFrameViaFactor_pullbackComp_symm {A B C D : Scheme.{u}}
    (i : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hi : i ≫ b = f) (g : C ⟶ D)
    {M : D.Modules} (e : (pullback b).obj ((pullback g).obj M) ≅ unitObj B) :
    frameViaFactor i (b ≫ g) (f ≫ g) (by rw [← Category.assoc, hi])
        (((pullbackComp b g).app M).symm ≪≫ e) =
      ((pullbackComp f g).app M).symm ≪≫ frameViaFactor i b f hi e := by
  have h := frameViaFactor_pullbackComp i b f hi g (((pullbackComp b g).app M).symm ≪≫ e)
  have h' := congrArg (fun z => ((pullbackComp f g).app M).symm ≪≫ z) h
  simpa only [Iso.self_symm_id_assoc, Iso.symm_self_id_assoc] using h'.symm

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) (U : X.left.Opens) (hx : x.1.point ∈ U)
  (r : ℝ≥0) (hr : 0 < r)

/-- The ACTUAL original V factor followed by original total inclusion has its DERIVED whole triangle. -/
theorem originalTestConfigurationGaussLocalUnitFieldMorph_total_comp :
    originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr hx ≫
      (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι) =
        originalTestConfigurationGaussFieldMorph C x r hr := by
  have h := congrArg (fun a => a ≫ C.unitOpen.ι)
    (originalTestConfigurationGaussLocalUnitFieldMorph_comp C x U hx r hr)
  simpa only [Category.assoc, originalTestConfigurationGaussFieldMorph] using h

variable (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ)

/-- The SAME actual original Gauss local power frame contracts from the genuine W frame to V,
as an ENTIRE native iso. No local frame or value comparison is supplied. -/
theorem originalTestConfigurationGaussLocalModelPowerFieldFrame_contractImage :
    originalTestConfigurationGaussLocalModelPowerFieldFrame C x U r hr M L
        linearization fibreOneIdentification δ m hx =
      frameViaFactor (originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr hx)
        (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)
        (originalTestConfigurationGaussFieldMorph C x r hr)
        (originalTestConfigurationGaussLocalUnitFieldMorph_total_comp C x U hx r hr)
        (originalTestConfigurationLocalModelPowerFrame C U M L linearization fibreOneIdentification δ m) := by
  simpa only [originalTestConfigurationGaussLocalModelPowerFieldFrame,
    originalTestConfigurationGaussLocalTotalFieldMorph,
    originalTestConfigurationLocalTotalModelPowerFrame] using
    originalFrameViaFactor_isoOpensRange (originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr hx)
      (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)
      (originalTestConfigurationGaussFieldMorph C x r hr)
      (originalTestConfigurationGaussLocalUnitFieldMorph_total_comp C x U hx r hr)
      (originalTestConfigurationLocalModelPowerFrame C U M L linearization fibreOneIdentification δ m)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
