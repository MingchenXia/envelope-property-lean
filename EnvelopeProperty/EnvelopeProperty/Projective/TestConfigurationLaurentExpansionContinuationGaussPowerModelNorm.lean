import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussWholeCoefficientMax
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussModelFrameFactor

/-! # The actual original whole model-power norm from its SAME finite Gauss coefficients

Original source geometry constructs the actual field frame. Genuine
properness constructs its actual valuative norm factor; original whole H0
constructs every coefficient family. No scalar/norm comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules SchemeLineSectionUnitFrames CanonicalGeometry

/-- The ACTUAL canonical residue morphism and valuation recover the SAME native original evaluation. -/
theorem originalNativeResidueField_value_top {S : Scheme.{u}} (z : SchemeValuedPoint S)
    (γ : Γ(S, ⊤)) :
    z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (S.residueField z.point))).hom
        ((S.fromSpecResidueField z.point).appTop γ)) =
      SchemeValuedPoint.eval z ⊤ trivial γ := by
  have h := originalFieldValuedPoint_evalTop (S.fromSpecResidueField z.point) z.residueVal γ
  rw [originalFieldValuedPoint_fromResidueField] at h
  exact h.symm

section ActualPowerFrame
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
  (r : ℝ≥0) (hr : 0 < r)

/-- The SAME actual canonical Gauss residue morphism constructs the ORIGINAL power field frame. -/
def originalTestConfigurationGaussModelPowerFieldFrame :
    (pullback (originalTestConfigurationGaussFieldMorph C x r hr)).obj (bundleTensorPower M m) ≅
      unitObj (Spec (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point))) :=
  frameViaFactor
    ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)
    (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
    (originalTestConfigurationGaussFieldMorph C x r hr) rfl
    (originalTestConfigurationGaussModelPowerFrame C x M L linearization fibreOneIdentification m e)

/-- EVERY original whole model-power section has its ACTUAL canonical residue scalar pullback. -/
theorem originalTestConfigurationGaussModelPowerFieldFrame_whole
    (s : Γ(bundleTensorPower M m, ⊤)) :
    frameScalar (originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
        fibreOneIdentification m e r hr)
        (pullbackSectionHom (originalTestConfigurationGaussFieldMorph C x r hr)
          (topSectionHom (bundleTensorPower M m) s)) =
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
        (originalNativeLaurentGaussPoint x.1.residueVal r hr).point).appTop.hom
        (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
          (bundleTensorPower M m)
          (originalTestConfigurationGaussModelPowerFrame C x M L linearization
            fibreOneIdentification m e) s) := by
  rw [originalFramedGlobalPullback_apply, originalFrameScalar_apply]
  exact frameViaFactor_sectionHom_scalar_apply _ _ _ rfl _
    (topSectionHom (bundleTensorPower M m) s) _ (frameScalar_identity _ _)
end ActualPowerFrame

attribute [local instance] originalGaussModelProjectionIsProper

section ActualPowerNorm
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)
  (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
  (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- Literal code for the SAME actual native norm identity, PROVED below;
it is never accepted as a factor, decomposition or comparison certificate. -/
def originalTestConfigurationGaussPowerModelNormFormula
    (hM : IsInvertible M) : Prop :=
  let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
  let y := originalTestConfigurationGaussFieldRelativePoint C x r hr
  let hb := originalTrivialPolynomialGauss_bounded (k := k) r hr₁
  let hMm := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m
  ∃ u : Γ(Spec (CommRingCat.of
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤)ˣ,
    z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
      ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
        (u : Γ(Spec (CommRingCat.of
          ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤))) ≠ 0 ∧
    ∀ s : Γ(bundleTensorPower M m, ⊤),
      ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
        (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
          (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
              affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a)) =
          (originalTestConfigurationModelPowerSectionsIso C M L linearization
            fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)) ∧
        RelativeSchemeValuedPoint.modelLineNorm hb y hMm
          (sectionAtOne (pullbackSectionHom (C.total.fromSpecResidueField y.1.point)
            (topSectionHom (bundleTensorPower M m) s))) =
          c.support.sup (fun n => x.1.residueVal
            (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e (c n)) * r ^ n) *
          z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
            ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
              (u : Γ(Spec (CommRingCat.of
                ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤)))

/-- The ORIGINAL native total-model power norm equals the SAME original finite Gauss maximum
times ONE internally constructed nonzero actual unit value, uniformly for EVERY whole section. -/
theorem originalTestConfigurationGaussPower_modelNorm [IsProper X.hom]
    (hM : IsInvertible M) (hL : IsInvertible L) :
    originalTestConfigurationGaussPowerModelNormFormula C x M L linearization
      fibreOneIdentification m e r hr hr₁ hM := by
  dsimp only [originalTestConfigurationGaussPowerModelNormFormula]
  let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
  let y := originalTestConfigurationGaussFieldRelativePoint C x r hr
  let hb := originalTrivialPolynomialGauss_bounded (k := k) r hr₁
  have hn := originalFieldModelNorm_frameFactor
    (originalTestConfigurationGaussFieldMorph C x r hr)
    (R := Polynomial k) (vR := gaussValuation (1 : Valuation k ℝ≥0) r) C.projection
    hb z.residueVal y.property (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    (originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
      fibreOneIdentification m e r hr)
  dsimp only [originalFieldModelNormFrameFactorFormula] at hn
  obtain ⟨u, hu, _hgeneric, hwhole⟩ := hn
  refine ⟨u, hu, fun s => ?_⟩
  obtain ⟨c, hc, _huniq⟩ := exists_unique_original_testConfiguration_whole_power_coefficient_max
    x C M L linearization fibreOneIdentification m e r hr hL s
  refine ⟨c, ⟨hc.1, ?_⟩, fun d hd => ?_⟩
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
        (originalTestConfigurationGaussModelPowerFrame C x M L linearization
          fibreOneIdentification m e) s)
    exact (hwhole (topSectionHom (bundleTensorPower M m) s)).trans
      (congrArg (fun a : ℝ≥0 => a * z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
          (show Γ(Spec (CommRingCat.of
            ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤) from u.val)))
        (hp.trans (hv.trans hc.2.2)))
  · let t := (originalTestConfigurationModelPowerSectionsIso C M L linearization
      fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)
    obtain ⟨c₀, _hc₀, huniq⟩ := exists_unique_original_testConfiguration_unit_power_laurent_expansion
      C L hL m t
    exact (huniq d hd.1).trans (huniq c hc.1).symm
end ActualPowerNorm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
