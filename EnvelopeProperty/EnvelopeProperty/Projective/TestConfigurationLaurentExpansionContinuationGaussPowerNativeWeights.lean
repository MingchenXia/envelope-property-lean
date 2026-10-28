import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussPowerModelNorm

/-! # Genuine original X model norms are the SAME original finite coefficient weights

Actual properness and invertibility construct the X valuative frame internally.
No frame-normalization, coefficient, model-norm or metric comparison is assumed.
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

/-- An ACTUAL original valuative frame computes the SAME native norm of EVERY original coefficient. -/
theorem originalResidueFramedSectionCoefficients_center_value
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    {v : Valuation k ℝ≥0} (hb : ∀ a, v a ≤ 1) (x : RelativeSchemeValuedPoint v X.hom)
    (N : X.left.Modules) (hN : IsInvertible N)
    (d : RelativeSchemeValuedPoint.centerLineModule hb x N ≅
      unitObj (Spec (CommRingCat.of (RelativeSchemeValuedPoint.CenterRing x))))
    (s : Γ(N, ⊤)) :
    x.1.residueVal (originalResidueFramedSectionCoefficients x N
      (RelativeSchemeValuedPoint.centerFrameGenericIso hb x d) s) =
      RelativeSchemeValuedPoint.modelLineNorm hb x hN
        (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom N s))) := by
  rw [originalResidueFramedSectionCoefficients_apply, originalFrameScalar_apply]
  exact (RelativeSchemeValuedPoint.modelLineNorm_eq_frame hb x hN d _).symm

attribute [local instance] originalGaussModelProjectionIsProper

section ActualPowerNativeNorm
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
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
  (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- Literal SAME entire native norm identity; proved below, never an incoming comparison certificate. -/
def originalTestConfigurationGaussPowerNativeNormFormula
    (hM : IsInvertible M) (hL : IsInvertible L) : Prop :=
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
          c.support.sup (fun n => RelativeSchemeValuedPoint.modelLineNorm Valuation.one_apply_le_one x
            (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
            (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
              (topSectionHom (bundleTensorPower L m) (c n)))) * r ^ n) *
          z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
            ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
              (u : Γ(Spec (CommRingCat.of
                ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point)), ⊤)))

/-- EVERY actual original whole model-power norm is the SAME original coefficient-model-norm maximum
with ONE actual nonzero frame-unit value, constructed internally and uniform for ALL whole sections. -/
theorem originalTestConfigurationGaussPower_nativeNorm
    (hM : IsInvertible M) (hL : IsInvertible L) :
    originalTestConfigurationGaussPowerNativeNormFormula C x M L linearization
      fibreOneIdentification m r hr hr₁ hM hL := by
  dsimp only [originalTestConfigurationGaussPowerNativeNormFormula]
  let hbX : ∀ a : k, (1 : Valuation k ℝ≥0) a ≤ 1 := Valuation.one_apply_le_one
  let hLm := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m
  obtain ⟨d⟩ := RelativeSchemeValuedPoint.exists_centerLineUnitIso hbX x hLm
  let e := RelativeSchemeValuedPoint.centerFrameGenericIso hbX x d
  have hn := originalTestConfigurationGaussPower_modelNorm C x M L linearization
    fibreOneIdentification m e r hr hr₁ hM hL
  dsimp only [originalTestConfigurationGaussPowerModelNormFormula] at hn
  obtain ⟨u, hu, hwhole⟩ := hn
  refine ⟨u, hu, fun s => ?_⟩
  obtain ⟨c, hc, _huniq⟩ := hwhole s
  refine ⟨c, ⟨hc.1, ?_⟩, fun a ha => ?_⟩
  · have hweights : c.support.sup
        (fun n => x.1.residueVal
          (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e (c n)) * r ^ n) =
        c.support.sup (fun n => RelativeSchemeValuedPoint.modelLineNorm hbX x hLm
          (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
            (topSectionHom (bundleTensorPower L m) (c n)))) * r ^ n) := by
      apply Finset.sup_congr rfl
      intro n _
      rw [originalResidueFramedSectionCoefficients_center_value hbX x
        (bundleTensorPower L m) hLm d]
    exact hc.2.trans (congrArg (fun a : ℝ≥0 => a *
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal
        ((Scheme.ΓSpecIso (CommRingCat.of
          ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
            (originalNativeLaurentGaussPoint x.1.residueVal r hr).point))).hom
              (show Γ(Spec (CommRingCat.of
                ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
                  (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)), ⊤) from u.val))) hweights)
  · let t := (originalTestConfigurationModelPowerSectionsIso C M L linearization
      fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)
    obtain ⟨c₀, _hc₀, huniq⟩ := exists_unique_original_testConfiguration_unit_power_laurent_expansion
      C L hL m t
    exact (huniq a ha.1).trans (huniq c hc.1).symm
end ActualPowerNativeNorm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
