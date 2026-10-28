import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationCenterFrameFactors

/-! # The native model potential of a tensor power

For the power data of `…ContinuationTensorComparisons` and an ample generic power `L^{⊗ n}`:

* `gaussNativeNormFactor_power_comparisons`: the native factor of `M^{⊗ n}` is the `n`-th
  power of the native factor of `M`;
* `gaussNativeModelPotential_power_comparisons`: hence `pot(M^{⊗ n}) = n · pot(M)`.

The proof computes the factor of `M^{⊗ n}` with the `n`-th power of the chosen centre frame
(`gaussNativeNormFactor_eq_centerFactor`) and identifies the induced product frame with the
canonical power frame (`productTotalLineIso_power_comparisons`).  This is `φ_{b𝓛} = b φ_𝓛`
(FHX §2.3, BJ22 §2).
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
open SchemePulledPowerFrames Berkovich.SchemeLinePowerFrameNorms
open Berkovich.SchemeResidueFrameComparison
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (hL : IsInvertible L)
private local instance projectionProper : IsProper C.projection := C.projection_isProper

/-- The actual native factor of the SAME internally constructed power
action and fibre-one data is the original native factor to that power.
Only ordinary ampleness of the original generic power line is used. -/
theorem gaussNativeNormFactor_power_comparisons (n : ℕ)
    (hAmpN : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower L n))
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    C.gaussNativeNormFactor (bundleTensorPower M n)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
        (bundleTensorPower L n) (C.powerLineActionComparison M alpha n)
        (C.powerFibreOneComparison M L e n)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) r hr hru x =
      C.gaussNativeNormFactor M hM L alpha e hL r hr hru x ^ n := by
  let : IsProper X.hom := C.original_isProper
  let P := (C.productGaussSource x r hr).1
  let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let F := C.originalCenterOpenFrame L hL x
  let eC := C.gaussCompatibleCenterFrame M hM r hr hru x
  let eCn := centerPowerFrame z hb eC n
  let eM := C.gaussCompatibleTargetFrame M hM r hr hru x
  let hMn := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n
  let hLn := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let alphaN := C.powerLineActionComparison M alpha n
  let eN := C.powerFibreOneComparison M L e n
  have hy : P.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ F.1 := by
    have hh := congrArg SchemeValuedPoint.point
      (SchemePointLaurentLocalFrame.openPoint_comp
          X.hom x Valuation.one_apply_le_one F.1 F.2.2 r hr)
    change (SchemePointLaurentGauss.productPoint X.hom x r hr).1.point ∈
      (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ F.1
    rw [← hh]
    exact (SchemePointLaurentLocalFrame.openPoint X.hom x Valuation.one_apply_le_one
      F.1 F.2.2 r hr).point.property
  have htarget : C.gaussCenterTargetFrame (bundleTensorPower M n) r hr hru x eCn =
      pullbackPowerFrame (C.total.fromSpecResidueField (C.productTotalMap P.point)) eM n :=
    (centerFrameGenericIso_centerPowerFrame z hb eC n).trans
      (pullbackPowerFrame_generic z eM n).symm
  have hmodel : C.productModelResidueFrame (bundleTensorPower M n) (bundleTensorPower L n)
      alphaN eN P (C.gaussCenterTargetFrame (bundleTensorPower M n) r hr hru x eCn) =
      C.productModelPowerResidueFrame M L alpha e P eM n := by
    dsimp only [productModelResidueFrame, productModelPowerResidueFrame]
    rw [htarget, C.productTotalLineIso_power_comparisons M L alpha e n]
  have hnative := C.gaussNativeNormFactor_eq_centerFactor (bundleTensorPower M n) hMn
    r hr hru x eCn (bundleTensorPower L n) alphaN eN F.1 hy
    (pullbackPowerFrame F.1.ι F.2.1 n) hLn hAmpN F.2.2
  refine hnative.trans ?_
  change P.residueVal (transitionUnit
    (productReferenceResidueFrame (bundleTensorPower L n) P F.1 hy
      (pullbackPowerFrame F.1.ι F.2.1 n))
    (C.productModelResidueFrame (bundleTensorPower M n) (bundleTensorPower L n)
      alphaN eN P (C.gaussCenterTargetFrame (bundleTensorPower M n) r hr hru x eCn))).val = _
  rw [hmodel]
  exact C.productPowerFrame_transitionUnit_value M L alpha e P eM F.1 hy F.2.1 P.residueVal n

/-- Taking minus the logarithm of the DERIVED original factor power law
gives the actual model potential power law, with the same original action. -/
theorem gaussNativeModelPotential_power_comparisons (n : ℕ)
    (hAmpN : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower L n))
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    C.gaussNativeModelPotential (bundleTensorPower M n)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
        (bundleTensorPower L n) (C.powerLineActionComparison M alpha n)
        (C.powerFibreOneComparison M L e n)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) r hr hru x =
      (n : ℝ) * C.gaussNativeModelPotential M hM L alpha e hL r hr hru x := by
  dsimp only [gaussNativeModelPotential]
  rw [C.gaussNativeNormFactor_power_comparisons M hM L alpha e hL n hAmpN r hr hru x]
  simp only [NNReal.coe_pow, Real.log_pow, mul_neg]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
