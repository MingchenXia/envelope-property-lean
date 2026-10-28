import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOpenResidueFrameDescent

/-! # Actual original local total-model opens and all-power Gauss field frames

Original Gauss geometry constructs the genuine local open factors. Original
source linearization and fibre-one data construct each model-power frame.
No local-map, frame, norm or metric comparison is supplied.
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

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom)
  (U : X.left.Opens) (hx : x.1.point ∈ U) (r : ℝ≥0) (hr : 0 < r)

/-- The ACTUAL original projection square puts the SAME Gauss field map in the genuine preimage open. -/
def originalTestConfigurationGaussLocalUnitFieldMorph (hx : x.1.point ∈ U) :
    Spec (CommRingCat.of
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
        (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)) ⟶
      ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).toScheme := by
  let ρ := (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
    (originalNativeLaurentGaussPoint x.1.residueVal r hr).point
  refine IsOpenImmersion.lift ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι
    (ρ ≫ originalTestConfigurationGaussMorph C x) ?_
  rintro z ⟨s, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (originalTestConfigurationUnitProjection C)
    ((originalTestConfigurationGaussMorph C x) (ρ s)) ∈ U
  have h := congrArg
    (fun f : Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹]) ⟶ X.left => f (ρ s))
    (originalTestConfigurationGaussMorph_projection C x)
  simp only [Scheme.Hom.comp_apply] at h
  rw [h]
  exact (X.left.fromSpecResidueField_apply x.1.point
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
      (X.left.residueField x.1.point)[T;T⁻¹]))) (ρ s))).symm ▸ hx

/-- The constructed ACTUAL original local unit-open factor has the ENTIRE genuine scheme triangle. -/
theorem originalTestConfigurationGaussLocalUnitFieldMorph_comp :
    originalTestConfigurationGaussLocalUnitFieldMorph C x U (hx := hx) r hr ≫
      ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι =
        (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point ≫
            originalTestConfigurationGaussMorph C x := by
  unfold originalTestConfigurationGaussLocalUnitFieldMorph
  apply IsOpenImmersion.lift_fac

/-- A genuine native open-image iso constructs the SAME Gauss field map into an ACTUAL total open. -/
def originalTestConfigurationGaussLocalTotalFieldMorph (hx : x.1.point ∈ U) :
    Spec (CommRingCat.of
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
        (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)) ⟶
      ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).toScheme :=
  originalTestConfigurationGaussLocalUnitFieldMorph C x U (hx := hx) r hr ≫
    (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).isoOpensRange.hom

/-- The ENTIRE constructed total-open triangle recovers EXACTLY the SAME original GaussFieldMorph. -/
theorem originalTestConfigurationGaussLocalTotalFieldMorph_comp :
    originalTestConfigurationGaussLocalTotalFieldMorph C x U (hx := hx) r hr ≫
      ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι =
        originalTestConfigurationGaussFieldMorph C x r hr := by
  unfold originalTestConfigurationGaussLocalTotalFieldMorph
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have h := congrArg (fun a => a ≫ C.unitOpen.ι)
    (originalTestConfigurationGaussLocalUnitFieldMorph_comp C x U (hx := hx) r hr)
  simpa only [Category.assoc, originalTestConfigurationGaussFieldMorph] using h

/-- An ACTUAL original local degree-one frame constructs genuine pullback frames for ALL powers. -/
def originalTestConfigurationLocalPowerFrame (L : X.left.Modules)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ) :
    (pullback U.ι).obj (bundleTensorPower L m) ≅ unitObj U.toScheme :=
  TestConfigurationSectionTransport.tensorPowerPullbackIso U.ι L m ≪≫
    bundleTensorPowerTrivialization δ m

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

/-- The DERIVED original sigma_m and genuine local projection construct an ACTUAL total-model frame. -/
def originalTestConfigurationLocalModelPowerFrame :
    (pullback (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)).obj
      (bundleTensorPower M m) ≅ unitObj (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).toScheme) :=
  ((pullbackComp ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι C.unitOpen.ι).app
    (bundleTensorPower M m)).symm ≪≫
  (pullback ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι).mapIso
    (originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m) ≪≫
  (pullbackComp ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι
    (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
  frameViaFactor ((originalTestConfigurationUnitProjection C) ∣_ U) U.ι
    (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ originalTestConfigurationUnitProjection C)
    (morphismRestrict_ι (originalTestConfigurationUnitProjection C) U)
    (originalTestConfigurationLocalPowerFrame U L δ m)

/-- The native actual open-image inverse constructs an original model-power frame on the TRUE total open. -/
def originalTestConfigurationLocalTotalModelPowerFrame :
    (pullback ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι).obj
      (bundleTensorPower M m) ≅
        unitObj (((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).toScheme) :=
  frameViaFactor (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).isoOpensRange.inv
    (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)
    ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι
    (Scheme.Hom.isoOpensRange_inv_comp _)
    (originalTestConfigurationLocalModelPowerFrame C U M L linearization fibreOneIdentification δ m)

/-- The DERIVED actual total-open field square constructs a frame on the EXACT original Gauss power fiber. -/
def originalTestConfigurationGaussLocalModelPowerFieldFrame (hx : x.1.point ∈ U) :
    (pullback (originalTestConfigurationGaussFieldMorph C x r hr)).obj (bundleTensorPower M m) ≅
      unitObj (Spec (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point))) :=
  frameViaFactor (originalTestConfigurationGaussLocalTotalFieldMorph C x U (hx := hx) r hr)
    ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι
    (originalTestConfigurationGaussFieldMorph C x r hr)
    (originalTestConfigurationGaussLocalTotalFieldMorph_comp C x U (hx := hx) r hr)
    (originalTestConfigurationLocalTotalModelPowerFrame C U M L linearization fibreOneIdentification δ m)

/-- Actual original properness and invertibility INTERNALLY construct a center-local frame containing support. -/
theorem exists_originalModelBaseCenterLocalFrame [IsProper X.hom]
    (hb : ∀ a, v a ≤ 1) (N : X.left.Modules) (hN : IsInvertible N) :
    ∃ U : X.left.Opens, RelativeSchemeValuedPoint.center hb x ∈ U ∧ x.1.point ∈ U ∧
      Nonempty ((pullback U.ι).obj N ≅ unitObj U.toScheme) := by
  obtain ⟨ι, V, hcover, htriv⟩ := hN
  have hc : RelativeSchemeValuedPoint.center hb x ∈ iSup V := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  exact ⟨V i, hi, RelativeSchemeValuedPoint.support_mem_of_center_mem hb x (V i) hi, htriv i⟩

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
