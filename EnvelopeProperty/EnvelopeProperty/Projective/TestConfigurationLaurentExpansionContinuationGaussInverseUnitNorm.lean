import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussFrameMatching

/-! # The true total-support inverse-unit norm in the original Gauss formula

Actual original total opens and full frame coherence identify the factor with
the native model norm of the SAME original support-residue inverse-unit section.
The total center need not lie in the unit open, and no norm-one premise occurs.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation SchemeLineSectionUnitFrames Scheme.Modules CanonicalGeometry
open SchemeModuleFrameCoefficients

/-- Actual X-local geometry computes the coefficient norm for ANY original module/frame. -/
theorem originalResidueFramedSectionCoefficients_local_value
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    {v : Valuation k ℝ≥0} (hb : ∀ a, v a ≤ 1) (x : RelativeSchemeValuedPoint v X.hom)
    (N : X.left.Modules) (hN : IsInvertible N) (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δ : (pullback U.ι).obj N ≅ unitObj U.toScheme) (s : Γ(N, ⊤)) :
    x.1.residueVal (originalResidueFramedSectionCoefficients x N
      (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δ) s) =
      RelativeSchemeValuedPoint.modelLineNorm hb x hN
        (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom N s))) := by
  have h := originalResidueFramedSectionCoefficients_center_value hb x N hN
    (RelativeSchemeValuedPoint.centerLocalFrame hb x U hc δ) s
  rw [RelativeSchemeValuedPoint.centerFrameGenericIso_localFrame] at h
  exact h

/-- Any ACTUAL native residue frame computes whole original sections by its genuine field pullback. -/
theorem originalFieldResidueFrame_whole_modelNorm
    {K : Type u} [Field K] {Y : Scheme.{u}} (f : Spec (CommRingCat.of K) ⟶ Y)
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : IsInvertible M)
    (E : (pullback (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      unitObj (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))))
    (s : Γ(M, ⊤)) :
    let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
    RelativeSchemeValuedPoint.modelLineNorm hb y hM
        (sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y.1.point) (topSectionHom M s))) =
      w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (frameScalar (originalFieldResidueLineFrame f E)
          (pullbackSectionHom f (topSectionHom M s)))) *
        RelativeSchemeValuedPoint.modelLineNorm hb y hM (unitSection E) := by
  let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
  let β := pullbackSectionHom (Y.fromSpecResidueField y.1.point) (topSectionHom M s)
  have hc := originalFieldResidueSectionHom_value f w E β
  have hwhole := originalFieldResidueSectionHom_global f (topSectionHom M s)
  change originalFieldResidueSectionHom f β = pullbackSectionHom f (topSectionHom M s) at hwhole
  rw [hwhole, ← originalFrameScalar_apply] at hc
  have hproject {B : Scheme.{u}} {N : B.Modules}
      (a : N ≅ unitObj B) (α : unitObj B ⟶ N) :
      coefficient a (sectionAtOne α) = frameScalar a α := (originalFrameScalar_apply a α).symm
  have hn := RelativeSchemeValuedPoint.modelLineNorm_eq_genericFrameCoefficient_mul hb y hM E (sectionAtOne β)
  simp only [RelativeSchemeValuedPoint.genericFrameCoefficient, hproject] at hn
  exact hn.trans (congrArg (fun a : ℝ≥0 => a *
    RelativeSchemeValuedPoint.modelLineNorm hb y hM (unitSection E)) hc.symm)

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (U : Y.Opens) (g : Spec (CommRingCat.of K) ⟶ U.toScheme)
  (f : Spec (CommRingCat.of K) ⟶ Y)

/-- An actual whole scheme triangle constructs a frame at the SAME original support. -/
def originalFactoredOpenFieldResidueFrame (hg : g ≫ U.ι = f) {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (pullback (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      unitObj (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))) := by
  subst f
  exact originalOpenFieldResidueFrame U g a

/-- The entire native field-frame equality is derived from the actual whole triangle. -/
theorem originalFactoredOpenFieldResidueFrame_field (hg : g ≫ U.ι = f) {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    originalFieldResidueLineFrame f (originalFactoredOpenFieldResidueFrame U g f hg a) =
      frameViaFactor g U.ι f hg a := by
  subst f
  exact originalOpenFieldResidueFrame_field U g a

/-- The true inverse-unit norm is nonzero and computes EVERY actual original whole section. -/
theorem originalFactoredOpenFieldResidueFrame_whole_modelNorm
    (hg : g ≫ U.ι = f)
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : IsInvertible M)
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
    RelativeSchemeValuedPoint.modelLineNorm hb y hM
        (unitSection (originalFactoredOpenFieldResidueFrame U g f hg a)) ≠ 0 ∧
      ∀ s : Γ(M, ⊤),
        RelativeSchemeValuedPoint.modelLineNorm hb y hM
            (sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y.1.point)
              (topSectionHom M s))) =
          w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
            (frameScalar (frameViaFactor g U.ι f hg a)
              (pullbackSectionHom f (topSectionHom M s)))) *
            RelativeSchemeValuedPoint.modelLineNorm hb y hM
              (unitSection (originalFactoredOpenFieldResidueFrame U g f hg a)) := by
  subst f
  exact ⟨(originalOpenFieldResidueFrame_modelNorm U g q hb w hbase hM a).1,
    fun s => originalOpenFieldResidueFrame_whole_modelNorm U g q hb w hbase hM a s⟩

section OriginalPowerFrame
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) (U : X.left.Opens)
  (r : ℝ≥0) (hr : 0 < r) (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ)

/-- The genuine total open constructs an actual M-power frame at the SAME total Gauss support. -/
def originalTestConfigurationGaussLocalResidueModelPowerFrame (hx : x.1.point ∈ U) :
    (pullback (C.total.fromSpecResidueField
      (originalTestConfigurationGaussFieldRelativePoint C x r hr).1.point)).obj (bundleTensorPower M m) ≅
        unitObj (Spec (CommRingCat.of (C.total.residueField
          (originalTestConfigurationGaussFieldRelativePoint C x r hr).1.point))) :=
  originalFactoredOpenFieldResidueFrame
    ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange)
    (originalTestConfigurationGaussLocalTotalFieldMorph C x U r hr hx)
    (originalTestConfigurationGaussFieldMorph C x r hr)
    (originalTestConfigurationGaussLocalTotalFieldMorph_comp C x U hx r hr)
    (originalTestConfigurationLocalTotalModelPowerFrame C U M L linearization fibreOneIdentification δ m)

/-- The actual residue-frame pullback equals the SAME frozen original Gauss power frame. -/
theorem originalTestConfigurationGaussLocalResidueModelPowerFrame_field [IsProper X.hom]
    (hb : ∀ a, v a ≤ 1) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    originalFieldResidueLineFrame (originalTestConfigurationGaussFieldMorph C x r hr)
        (originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
          fibreOneIdentification δ m (RelativeSchemeValuedPoint.support_mem_of_center_mem hb x U hc)) =
      originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization fibreOneIdentification m
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc
          (originalTestConfigurationLocalPowerFrame U L δ m)) r hr := by
  rw [originalTestConfigurationGaussLocalResidueModelPowerFrame,
    originalFactoredOpenFieldResidueFrame_field]
  exact originalTestConfigurationGaussLocalModelPowerFieldFrame_eq C x hb U hc r hr M L
    linearization fibreOneIdentification δ m

/-- The original field scalar has the SAME original finite coefficient-support Gauss maximum,
for ANY actual X residue-line frame, without any decomposition or value comparison input. -/
theorem exists_unique_original_testConfiguration_field_coefficient_max [IsProper X.hom]
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
    (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤)) :
    let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a)) =
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)) ∧
      z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
          (frameScalar (originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
            fibreOneIdentification m e r hr)
            (pullbackSectionHom (originalTestConfigurationGaussFieldMorph C x r hr)
              (topSectionHom (bundleTensorPower M m) s)))) =
        c.support.sup (fun n => x.1.residueVal
          (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e (c n)) * r ^ n) := by
  dsimp only
  let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
  obtain ⟨c, hcoeff, _huniq⟩ := exists_unique_original_testConfiguration_whole_power_coefficient_max
    x C M L linearization fibreOneIdentification m e r hr hL s
  refine ⟨c, ⟨hcoeff.1, ?_⟩, fun a ha => ?_⟩
  · have hp := congrArg
      (fun a : Γ(Spec (CommRingCat.of
          ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤) =>
        z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
          ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom a))
      (originalTestConfigurationGaussModelPowerFieldFrame_whole C x M L linearization
        fibreOneIdentification m e r hr s)
    have hv := originalNativeResidueField_value_top z
      (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
        (bundleTensorPower M m)
        (originalTestConfigurationGaussModelPowerFrame C x M L linearization fibreOneIdentification m e) s)
    exact hp.trans (hv.trans hcoeff.2.2)
  · let t := (originalTestConfigurationModelPowerSectionsIso C M L linearization
      fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)
    obtain ⟨c₀, _hc₀, huniq⟩ := exists_unique_original_testConfiguration_unit_power_laurent_expansion
      C L hL m t
    exact (huniq a ha.1).trans (huniq c hcoeff.1).symm
end OriginalPowerFrame

attribute [local instance] originalGaussModelProjectionIsProper

section OriginalNativeNorm
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
  (C : NativeTestConfiguration.TestConfiguration k X)
  (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
  (U : X.left.Opens) (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ)
  (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- The true original total inverse-unit factor multiplies the SAME actual original Gauss scalar. -/
theorem originalTestConfigurationGaussLocalResidueModelPowerFrame_whole_modelNorm
    (hM : IsInvertible M) (s : Γ(bundleTensorPower M m, ⊤)) :
    let y := originalTestConfigurationGaussFieldRelativePoint C x r hr
    let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
    let hb := originalTrivialPolynomialGauss_bounded (k := k) r hr₁
    let hMm := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m
    let E := originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
      fibreOneIdentification δ m
      (RelativeSchemeValuedPoint.support_mem_of_center_mem Valuation.one_apply_le_one x U hc)
    RelativeSchemeValuedPoint.modelLineNorm hb y hMm
        (sectionAtOne (pullbackSectionHom (C.total.fromSpecResidueField y.1.point)
          (topSectionHom (bundleTensorPower M m) s))) =
      z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
          (frameScalar (originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
            fibreOneIdentification m (RelativeSchemeValuedPoint.localFrameGenericIso
              Valuation.one_apply_le_one x U hc (originalTestConfigurationLocalPowerFrame U L δ m)) r hr)
            (pullbackSectionHom (originalTestConfigurationGaussFieldMorph C x r hr)
              (topSectionHom (bundleTensorPower M m) s)))) *
        RelativeSchemeValuedPoint.modelLineNorm hb y hMm (unitSection E) := by
  have h := originalFieldResidueFrame_whole_modelNorm
    (originalTestConfigurationGaussFieldMorph C x r hr)
    C.projection (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal
    (originalTestConfigurationGaussFieldRelativePoint C x r hr).property
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    (originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
      fibreOneIdentification δ m
      (RelativeSchemeValuedPoint.support_mem_of_center_mem Valuation.one_apply_le_one x U hc)) s
  rw [originalTestConfigurationGaussLocalResidueModelPowerFrame_field] at h
  exact h

end OriginalNativeNorm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
