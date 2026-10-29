import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationWholeCoefficientExtractor
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussInverseUnitMaximum

/-! # The actual extracted original coefficients in the original Gauss field maximum -/
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
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  {v : Valuation k ℝ≥0} (x : RelativeSchemeValuedPoint v X.hom)

/-- The unchanged SAME-support original residue coefficient maximum. -/
def originalResidueCoefficientWeightedMaximum (N : X.left.Modules)
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj N ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
    (r : ℝ≥0) (c : ℤ →₀ originalBaseSections X.hom N) : ℝ≥0 :=
  c.support.sup (fun n => x.1.residueVal (originalResidueFramedSectionCoefficients x N e (c n)) * r ^ n)

/-- The unchanged SAME-support original whole-section native model-norm maximum. -/
def originalModelCoefficientWeightedMaximum [IsProper X.hom] (hb : ∀ a, v a ≤ 1)
    (N : X.left.Modules) (hN : IsInvertible N)
    (r : ℝ≥0) (c : ℤ →₀ originalBaseSections X.hom N) : ℝ≥0 :=
  c.support.sup (fun n => RelativeSchemeValuedPoint.modelLineNorm hb x hN
    (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
      (topSectionHom N (c n)))) * r ^ n)

/-- Actual local geometry equates these physical finite maxima for EVERY original family. -/
theorem originalResidueCoefficientWeightedMaximum_local [IsProper X.hom]
    (hb : ∀ a, v a ≤ 1) (N : X.left.Modules) (hN : IsInvertible N)
    (U : X.left.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δ : (pullback U.ι).obj N ≅ unitObj U.toScheme)
    (r : ℝ≥0) (c : ℤ →₀ originalBaseSections X.hom N) :
    originalResidueCoefficientWeightedMaximum x N
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δ) r c =
      originalModelCoefficientWeightedMaximum x hb N hN r c :=
  congrArg (fun F : Γ(N, ⊤) → ℝ≥0 => c.support.sup (fun n => F (c n) * r ^ n))
    (originalResidueFramedSectionCoefficients_local_value_fun hb x N hN U hc δ)

variable (C : NativeTestConfiguration.TestConfiguration k X)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)

/-- A named literal original reconstruction predicate, with no comparison premise. -/
def originalTestConfigurationWholePowerCoefficientReconstruction
    (s : Γ(bundleTensorPower M m, ⊤))
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) : Prop :=
  originalTestConfigurationUnitPowerLaurentReconstruction C L m c =
    originalTestConfigurationWholePowerUnitSection C M L linearization fibreOneIdentification m s

/-- The actual original H0 inverse identifies exactly the original reconstruction predicate. -/
theorem originalTestConfigurationWholePowerCoefficientReconstruction_iff [IsProper X.hom]
    (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤))
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :
    originalTestConfigurationWholePowerCoefficientReconstruction C M L linearization
        fibreOneIdentification m s c ↔
      c = originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
        fibreOneIdentification m hL s :=
  originalTestConfigurationWholePowerLaurentCoefficients_eq_iff C M L linearization
    fibreOneIdentification m hL s c

/-- The identical original Gauss support-residue field scalar as an actual function of original sections. -/
def originalTestConfigurationWholePowerFieldValue
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
    (r : ℝ≥0) (hr : 0 < r) (s : Γ(bundleTensorPower M m, ⊤)) : ℝ≥0 :=
  let z := originalNativeLaurentGaussPoint x.1.residueVal r hr
  z.residueVal ((Scheme.ΓSpecIso (CommRingCat.of
    ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField z.point))).hom
      (frameScalar (originalTestConfigurationGaussModelPowerFieldFrame C x M L linearization
        fibreOneIdentification m e r hr)
        (pullbackSectionHom (originalTestConfigurationGaussFieldMorph C x r hr)
          (topSectionHom (bundleTensorPower M m) s))))

/-- ANY genuine residue frame factors the actual scalar through the actual original finite coefficient map. -/
theorem originalTestConfigurationWholePowerFieldValue_eq_extracted_max [IsProper X.hom]
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
    (r : ℝ≥0) (hr : 0 < r) (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerFieldValue x C M L linearization fibreOneIdentification m e r hr s =
      originalResidueCoefficientWeightedMaximum x (bundleTensorPower L m) e r
        (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
          fibreOneIdentification m hL s) := by
  obtain ⟨c, hc, _⟩ := exists_unique_original_testConfiguration_field_coefficient_max
    C x r hr M L linearization fibreOneIdentification m e hL s
  have hrec : originalTestConfigurationWholePowerCoefficientReconstruction C M L linearization
      fibreOneIdentification m s c := by
    rw [originalTestConfigurationWholePowerCoefficientReconstruction,
      originalTestConfigurationUnitPowerLaurentReconstruction_apply,
      originalTestConfigurationWholePowerUnitSection_apply]
    exact hc.1
  have heq := (originalTestConfigurationWholePowerCoefficientReconstruction_iff C M L linearization
    fibreOneIdentification m hL s c).mp hrec
  have hv : originalTestConfigurationWholePowerFieldValue x C M L linearization fibreOneIdentification
      m e r hr s = originalResidueCoefficientWeightedMaximum x (bundleTensorPower L m) e r c := hc.2
  exact hv.trans (congrArg (originalResidueCoefficientWeightedMaximum x (bundleTensorPower L m) e r) heq)

/-- Genuine local geometry gives the true model-norm maximum of the SAME actual extracted coefficients. -/
theorem originalTestConfigurationWholePowerFieldValue_eq_local_model_max [IsProper X.hom]
    (hb : ∀ a, v a ≤ 1) (hL : IsInvertible L) (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δp : (pullback U.ι).obj (bundleTensorPower L m) ≅ unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerFieldValue x C M L linearization fibreOneIdentification m
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δp) r hr s =
      originalModelCoefficientWeightedMaximum x hb (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) r
        (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
          fibreOneIdentification m hL s) :=
  (originalTestConfigurationWholePowerFieldValue_eq_extracted_max x C M L linearization
    fibreOneIdentification m (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δp) r hr hL s).trans
      (originalResidueCoefficientWeightedMaximum_local x hb (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) U hc δp r _)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
