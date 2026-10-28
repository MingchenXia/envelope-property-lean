import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussExtractedCoefficientMaximum

/-! # True total-model norm from the SAME actual extracted original coefficients -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial NNReal Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry NativeTestConfiguration Berkovich
open SchemeLineSectionEvaluation SchemeLineSectionUnitFrames SchemeModuleFrameCoefficients
attribute [local instance] originalGaussModelProjectionIsProper
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
  (C : NativeTestConfiguration.TestConfiguration k X)
  (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- The unchanged actual native total model norm of each original whole model-power section. -/
def originalTestConfigurationWholePowerNativeNorm (hM : IsInvertible M) (m : ℕ)
    (s : Γ(bundleTensorPower M m, ⊤)) : ℝ≥0 :=
  let y := originalTestConfigurationGaussFieldRelativePoint C x r hr
  RelativeSchemeValuedPoint.modelLineNorm (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    (sectionAtOne (pullbackSectionHom (C.total.fromSpecResidueField y.1.point)
      (topSectionHom (bundleTensorPower M m) s)))

/-- The TRUE native total-support inverse-unit section norm from actual total-open geometric descent. -/
def originalTestConfigurationLocalPowerInverseUnitNorm (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (hM : IsInvertible M) (m : ℕ) : ℝ≥0 :=
  let y := originalTestConfigurationGaussFieldRelativePoint C x r hr
  let E := originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
    fibreOneIdentification δ m
    (RelativeSchemeValuedPoint.support_mem_of_center_mem Valuation.one_apply_le_one x U hc)
  RelativeSchemeValuedPoint.modelLineNorm (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m) (unitSection E)

/-- The actual total residue-frame inverse-unit norm never vanishes; its center need not be in the unit open. -/
theorem originalTestConfigurationLocalPowerInverseUnitNorm_ne_zero (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (hM : IsInvertible M) (m : ℕ) :
    originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
      r hr hr₁ U hc δ hM m ≠ 0 :=
  RelativeSchemeValuedPoint.modelLineNorm_genericFrameUnit_ne_zero
    (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    (originalTestConfigurationGaussFieldRelativePoint C x r hr)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    (originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
      fibreOneIdentification δ m
      (RelativeSchemeValuedPoint.support_mem_of_center_mem Valuation.one_apply_le_one x U hc))

/-- The actual original whole scalar factorization, retaining the TRUE native inverse-unit norm. -/
theorem originalTestConfigurationWholePowerNativeNorm_eq_field_mul (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (hM : IsInvertible M) (m : ℕ)
    (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerNativeNorm C x M r hr hr₁ hM m s =
      originalTestConfigurationWholePowerFieldValue x C M L linearization fibreOneIdentification m
        (RelativeSchemeValuedPoint.localFrameGenericIso Valuation.one_apply_le_one x U hc
          (originalTestConfigurationLocalPowerFrame U L δ m)) r hr s *
      originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
        r hr hr₁ U hc δ hM m :=
  originalTestConfigurationGaussLocalResidueModelPowerFrame_whole_modelNorm C x U hc M L
    linearization fibreOneIdentification δ m r hr hr₁ hM s

/-- The true total norm is the SAME actual extracted original coefficient model-norm maximum times its true unit factor. -/
theorem originalTestConfigurationWholePowerNativeNorm_eq_extracted_max (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (hM : IsInvertible M) (hL : IsInvertible L)
    (m : ℕ) (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerNativeNorm C x M r hr hr₁ hM m s =
      originalModelCoefficientWeightedMaximum x Valuation.one_apply_le_one (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) r
        (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
          fibreOneIdentification m hL s) *
      originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
        r hr hr₁ U hc δ hM m :=
  (originalTestConfigurationWholePowerNativeNorm_eq_field_mul C x M L linearization
    fibreOneIdentification r hr hr₁ U hc δ hM m s).trans
      (congrArg (fun a : ℝ≥0 => a * originalTestConfigurationLocalPowerInverseUnitNorm C x M L
        linearization fibreOneIdentification r hr hr₁ U hc δ hM m)
        (originalTestConfigurationWholePowerFieldValue_eq_local_model_max x C M L linearization
          fibreOneIdentification m Valuation.one_apply_le_one hL U hc
          (originalTestConfigurationLocalPowerFrame U L δ m) r hr s))

/-- The original SAME extracted family has its exact original reconstruction AND true native total norm. -/
theorem originalTestConfigurationWholePowerNativeNorm_reconstruction_and_max (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (hM : IsInvertible M) (hL : IsInvertible L)
    (m : ℕ) (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerCoefficientReconstruction C M L linearization fibreOneIdentification m s
        (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization fibreOneIdentification m hL s) ∧
      originalTestConfigurationWholePowerNativeNorm C x M r hr hr₁ hM m s =
        originalModelCoefficientWeightedMaximum x Valuation.one_apply_le_one (bundleTensorPower L m)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) r
          (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
            fibreOneIdentification m hL s) *
        originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
          r hr hr₁ U hc δ hM m :=
  ⟨(originalTestConfigurationWholePowerCoefficientReconstruction_iff C M L linearization
      fibreOneIdentification m hL s _).mpr rfl,
    originalTestConfigurationWholePowerNativeNorm_eq_extracted_max C x M L linearization
      fibreOneIdentification r hr hr₁ U hc δ hM hL m s⟩

/-- Original geometry internally chooses ONE genuine degree-one local frame for ALL powers and EVERY original section. -/
theorem exists_original_testConfiguration_all_power_native_norm_max (hM : IsInvertible M) (hL : IsInvertible L) :
    ∃ (U : X.left.Opens) (hc : RelativeSchemeValuedPoint.center Valuation.one_apply_le_one x ∈ U)
      (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme), ∀ m : ℕ,
      originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
          r hr hr₁ U hc δ hM m ≠ 0 ∧
        ∀ s : Γ(bundleTensorPower M m, ⊤),
          originalTestConfigurationWholePowerCoefficientReconstruction C M L linearization fibreOneIdentification m s
              (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
                fibreOneIdentification m hL s) ∧
            originalTestConfigurationWholePowerNativeNorm C x M r hr hr₁ hM m s =
              originalModelCoefficientWeightedMaximum x Valuation.one_apply_le_one (bundleTensorPower L m)
                (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) r
                (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
                  fibreOneIdentification m hL s) *
              originalTestConfigurationLocalPowerInverseUnitNorm C x M L linearization fibreOneIdentification
                r hr hr₁ U hc δ hM m := by
  obtain ⟨U, hc, _hx, ⟨δ⟩⟩ := exists_originalModelBaseCenterLocalFrame x Valuation.one_apply_le_one L hL
  refine ⟨U, hc, δ, fun m => ⟨?_, ?_⟩⟩
  · exact originalTestConfigurationLocalPowerInverseUnitNorm_ne_zero C x M L linearization
      fibreOneIdentification r hr hr₁ U hc δ hM m
  · intro s
    exact originalTestConfigurationWholePowerNativeNorm_reconstruction_and_max C x M L linearization
      fibreOneIdentification r hr hr₁ U hc δ hM hL m s

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
