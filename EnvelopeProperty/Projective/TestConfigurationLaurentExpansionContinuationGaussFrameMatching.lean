import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussFrameCoherence

/-! # Actual original local and Laurent Gauss power frames agree

The comparisons are conclusions of genuine native pullback functoriality and
the original scheme projection squares, with no frame or metric certificate.
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

/-- Whole native polarization transport follows from actual pullback naturality. -/
theorem originalFrameViaFactor_polarization {A B S Y Z : Scheme.{u}}
    (i : A ⟶ B) (b : B ⟶ S) (f : A ⟶ S) (hi : i ≫ b = f)
    (j : S ⟶ Y) (p : S ⟶ Z) (w : A ⟶ Y) (hw : f ≫ j = w)
    {M : Y.Modules} {L : Z.Modules}
    (σ : (pullback j).obj M ≅ (pullback p).obj L)
    (e : (pullback (b ≫ p)).obj L ≅ unitObj B) :
    frameViaFactor i (b ≫ j) w (by rw [← Category.assoc, hi]; exact hw)
        (((pullbackComp b j).app M).symm ≪≫ (pullback b).mapIso σ ≪≫
          (pullbackComp b p).app L ≪≫ e) =
      (frameFactorIso f j w hw M).symm ≪≫ (pullback f).mapIso σ ≪≫
        (pullbackComp f p).app L ≪≫
          frameViaFactor i (b ≫ p) (f ≫ p) (by rw [← Category.assoc, hi]) e := by
  subst w
  have hid : frameFactorIso f j (f ≫ j) rfl M = (pullbackComp f j).app M := by
    apply Iso.ext
    simp only [frameFactorIso, Iso.trans_hom, Iso.app_hom,
      show (pullbackCongr (rfl : f ≫ j = f ≫ j)).hom.app M = 𝟙 _ from rfl,
      Category.comp_id]
  rw [hid, originalFrameViaFactor_pullbackComp_symm i b f hi j,
    originalFrameViaFactor_mapIso i b f hi σ, frameViaFactor_pullbackComp i b f hi p]

/-- Equality of actual scheme factors transports the same whole native frame. -/
theorem originalFrameViaFactor_congrFactor {A B Y : Scheme.{u}}
    (i i' : A ⟶ B) (b : B ⟶ Y) (f : A ⟶ Y) (hi : i ≫ b = f)
    (hi' : i' ≫ b = f) (h : i = i') {M : Y.Modules}
    (e : (pullback b).obj M ≅ unitObj B) :
    frameViaFactor i b f hi e = frameViaFactor i' b f hi' e := by
  subst i'
  rfl

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) [IsProper X.hom]
  (hb : ∀ a, v a ≤ 1) (U : X.left.Opens)
  (hc : RelativeSchemeValuedPoint.center hb x ∈ U) (r : ℝ≥0) (hr : 0 < r)

/-- The original whole projection square derives the actual X-local Gauss factor. -/
theorem originalTestConfigurationGaussLocalUnitFieldMorph_projection :
    originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr
        (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc) ≫
        ((originalTestConfigurationUnitProjection C) ∣_ U) =
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
          (X.left.residueField x.1.point)[T;T⁻¹]))) ≫
        RelativeSchemeValuedPoint.localGenericFactor hb x U hc := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, morphismRestrict_ι,
    RelativeSchemeValuedPoint.localGenericFactor_comp]
  rw [← Category.assoc, originalTestConfigurationGaussLocalUnitFieldMorph_comp]
  simp only [Category.assoc, originalTestConfigurationGaussMorph_projection]

/-- The entire actual local projection frame equals the SAME original Laurent frame. -/
theorem originalTestConfigurationGaussLocalProjectionFrame_eq (L : X.left.Modules)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    frameViaFactor
        (originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr
          (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc))
        (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫
          originalTestConfigurationUnitProjection C)
        (((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
            (originalNativeLaurentGaussPoint x.1.residueVal r hr).point ≫
          originalTestConfigurationGaussMorph C x) ≫ originalTestConfigurationUnitProjection C)
        (by rw [← Category.assoc, originalTestConfigurationGaussLocalUnitFieldMorph_comp])
        (frameViaFactor ((originalTestConfigurationUnitProjection C) ∣_ U) U.ι
          (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫
            originalTestConfigurationUnitProjection C)
          (morphismRestrict_ι (originalTestConfigurationUnitProjection C) U) δ) =
      frameViaFactor
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)
        (originalTestConfigurationGaussMorph C x ≫ originalTestConfigurationUnitProjection C)
        (((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
            (originalNativeLaurentGaussPoint x.1.residueVal r hr).point ≫
          originalTestConfigurationGaussMorph C x) ≫ originalTestConfigurationUnitProjection C)
        (Category.assoc _ _ _).symm
        (originalTestConfigurationGaussProjectionLineFrame C x L
          (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δ)) := by
  rw [frameViaFactor_comp]
  unfold originalTestConfigurationGaussProjectionLineFrame
    RelativeSchemeValuedPoint.localFrameGenericIso
  rw [frameViaFactor_comp, frameViaFactor_comp]
  apply originalFrameViaFactor_congrFactor
  exact originalTestConfigurationGaussLocalUnitFieldMorph_projection C x hb U hc r hr

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

/-- All original local model-power field frames equal the frozen original Gauss frames. -/
theorem originalTestConfigurationGaussLocalModelPowerFieldFrame_eq :
    originalTestConfigurationGaussLocalModelPowerFieldFrame C x U r hr M L
        linearization fibreOneIdentification δ m
        (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc) =
      originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
        fibreOneIdentification m
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc
          (originalTestConfigurationLocalPowerFrame U L δ m)) r hr := by
  rw [originalTestConfigurationGaussLocalModelPowerFieldFrame_contractImage]
  unfold originalTestConfigurationLocalModelPowerFrame
    originalTestConfigurationGaussModelPowerFieldFrame originalTestConfigurationGaussModelPowerFrame
  rw [originalFrameViaFactor_polarization
      (originalTestConfigurationGaussLocalUnitFieldMorph C x U r hr
        (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc))
      ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι
      (((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point) ≫
        originalTestConfigurationGaussMorph C x)
      (originalTestConfigurationGaussLocalUnitFieldMorph_comp C x U
        (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc) r hr)
      C.unitOpen.ι (originalTestConfigurationUnitProjection C)
      (originalTestConfigurationGaussFieldMorph C x r hr)
      (Category.assoc _ _ _)]
  rw [originalFrameViaFactor_polarization
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
        (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)
      (originalTestConfigurationGaussMorph C x)
      (((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point) ≫
        originalTestConfigurationGaussMorph C x) rfl
      C.unitOpen.ι (originalTestConfigurationUnitProjection C)
      (originalTestConfigurationGaussFieldMorph C x r hr)
      (Category.assoc _ _ _)]
  rw [originalTestConfigurationGaussLocalProjectionFrame_eq C x hb U hc r hr]

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
