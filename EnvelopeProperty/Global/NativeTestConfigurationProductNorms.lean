import EnvelopeProperty.Global.NativeTestConfigurationLaurentSections
import EnvelopeProperty.Global.NativeTestConfigurationGaussNorms
import EnvelopeProperty.Berkovich.SchemeModelNormFramedPullback

/-! # True original TC model norms as native original product residue coefficients -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X)

/-- The actual original product Gauss point has the ENTIRE original polynomial Gauss base. -/
def productGaussSource {v : Valuation k ℝ≥0}
    (x : RelativeSchemeValuedPoint v X.hom) (r : ℝ≥0) (hr : 0 < r) :
    RelativeSchemeValuedPoint (Spectrum.gauss (Spectrum.ofValuation v) r).val
      (C.productTotalMap ≫ C.projection) :=
  ⟨(SchemePointLaurentGauss.productPoint X.hom x r hr).1, by
    change SchemeValuedPoint.map (C.productTotalMap ≫ C.projection)
      (SchemePointLaurentGauss.productPoint X.hom x r hr).1 = _
    rw [SchemeValuedPoint.map_comp, C.productTotalMap_gaussPoint]
    exact (C.relativeGaussPoint x r hr).2⟩

/-- Its native relative image is the SAME actual original total Gauss point. -/
theorem productGaussSource_map {v : Valuation k ℝ≥0}
    (x : RelativeSchemeValuedPoint v X.hom) (r : ℝ≥0) (hr : 0 < r) :
    RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr) =
      C.relativeGaussPoint x r hr :=
  Subtype.ext (C.productTotalMap_gaussPoint x r hr)

private local instance projectionProper : IsProper C.projection := C.projection_isProper

variable (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)

/-- Actual properness/invertibility derive ONE native product residue frame
computing EVERY original total-space section's TRUE Gauss model norm at once. -/
theorem exists_productResidueFrame_gaussPowerSectionNorm
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (n : ℕ) :
    let P := (SchemePointLaurentGauss.productPoint X.hom x r hr).1
    let N := (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
      (bundleTensorPower L n)
    ∃ eN : (pullback ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField
          P.point)).obj N ≅
        unitObj (Spec (.of ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.residueField P.point))),
      ∀ s : Γ(bundleTensorPower M n, ⊤),
        C.gaussPowerSectionNorm M hM r hr hru x n s =
          P.residueVal (SchemeFramedSectionPullback.residueFrameCoefficient P N eN
            (C.globalProductPowerSection M L α e₁ n s)) := by
  let y := C.productGaussSource x r hr
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let B := bundleTensorPower M n
  let hB := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n
  obtain ⟨eN, he⟩ := exists_sourceResidueFrame_modelLineNorm hb C.productTotalMap y hB
    (C.productTotalLinePowerIso M L α e₁ n)
  refine ⟨eN, fun s => ?_⟩
  let F : RelativeSchemeValuedPoint (Spectrum.trivialGaussValuation k r) C.projection → ℝ≥0 :=
    fun z => modelLineNorm hb z hB
      (affinePullbackUnitTop (C.total.fromSpecResidueField z.1.point) B s)
  have hp : F (C.relativeGaussPoint x r hr) =
      F (RelativeSchemeValuedPoint.map C.productTotalMap rfl y) :=
    congrArg F (C.productGaussSource_map x r hr).symm
  have hu := SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
    (C.total.fromSpecResidueField (C.relativeGaussPoint x r hr).1.point) B s
  have hn := congrArg (modelLineNorm hb (C.relativeGaussPoint x r hr) hB) hu.symm
  exact hn.trans (hp.trans (he s))

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
