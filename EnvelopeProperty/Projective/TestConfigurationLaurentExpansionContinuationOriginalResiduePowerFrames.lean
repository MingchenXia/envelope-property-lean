import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOriginalLocalPowerFrames

/-! # Genuine original open-residue and Gauss-support model frames preserve all powers -/
open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Actual native residue/open factor geometry DERIVES the entire genuine power-frame equality. -/
theorem originalOpenFieldResidueFrame_power {K : Type u} [Field K] {Y : Scheme.{u}}
    (U : Y.Opens) (g : Spec (CommRingCat.of K) ⟶ U.toScheme) {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) (m : ℕ) :
    originalOpenFieldResidueFrame U g
        (tensorPowerPullbackIso U.ι M m ≪≫ bundleTensorPowerTrivialization a m) =
      tensorPowerPullbackIso
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1) M m ≪≫
          bundleTensorPowerTrivialization (originalOpenFieldResidueFrame U g a) m :=
  originalFrameViaFactor_power (originalOpenFieldResidueFactor U g) U.ι
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)
    (originalOpenFieldResidueFactor_comp U g) a m

/-- The SAME actual factored field point and native residue field retain genuine power frames. -/
theorem originalFactoredOpenFieldResidueFrame_power {K : Type u} [Field K] {Y : Scheme.{u}}
    (U : Y.Opens) (g : Spec (CommRingCat.of K) ⟶ U.toScheme)
    (f : Spec (CommRingCat.of K) ⟶ Y) (hg : g ≫ U.ι = f) {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) (m : ℕ) :
    originalFactoredOpenFieldResidueFrame U g f hg
        (tensorPowerPullbackIso U.ι M m ≪≫ bundleTensorPowerTrivialization a m) =
      tensorPowerPullbackIso (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1) M m ≪≫
        bundleTensorPowerTrivialization (originalFactoredOpenFieldResidueFrame U g f hg a) m := by
  subst f
  exact originalOpenFieldResidueFrame_power U g a m

section OriginalGaussFrames
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) (U : X.left.Opens) (r : ℝ≥0) (hr : 0 < r)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
        (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
  (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme)

/-- ACTUAL original Gauss support residue frame of M itself, derived from the true total open. -/
def originalTestConfigurationGaussLocalResidueDegreeOneModelFrame (hx : x.1.point ∈ U) :
    (pullback (C.total.fromSpecResidueField
      (originalTestConfigurationGaussFieldRelativePoint C x r hr).1.point)).obj M ≅
        unitObj (Spec (CommRingCat.of (C.total.residueField
          (originalTestConfigurationGaussFieldRelativePoint C x r hr).1.point))) :=
  originalFactoredOpenFieldResidueFrame
    ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange)
    (originalTestConfigurationGaussLocalTotalFieldMorph C x U r hr hx)
    (originalTestConfigurationGaussFieldMorph C x r hr)
    (originalTestConfigurationGaussLocalTotalFieldMorph_comp C x U hx r hr)
    (originalTestConfigurationLocalDegreeOneTotalModelFrame C U M L linearization fibreOneIdentification δ)

/-- SAME frozen original Gauss residue model-power frame is the power of a TRUE M-frame, ALL m0. -/
theorem originalTestConfigurationGaussLocalResidueModelPowerFrame_eq_degreeOne_power
    (m : ℕ) (hx : x.1.point ∈ U) :
    originalTestConfigurationGaussLocalResidueModelPowerFrame C x U r hr M L linearization
        fibreOneIdentification δ m hx =
      tensorPowerPullbackIso
        (C.total.fromSpecResidueField (originalTestConfigurationGaussFieldRelativePoint C x r hr).1.point)
        M m ≪≫ bundleTensorPowerTrivialization
          (originalTestConfigurationGaussLocalResidueDegreeOneModelFrame C x U r hr M L linearization
            fibreOneIdentification δ hx) m := by
  unfold originalTestConfigurationGaussLocalResidueModelPowerFrame
    originalTestConfigurationGaussLocalResidueDegreeOneModelFrame
  rw [originalTestConfigurationLocalTotalModelPowerFrame_eq_degreeOne_power]
  exact originalFactoredOpenFieldResidueFrame_power _ _ _ _ _ m

end OriginalGaussFrames
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
