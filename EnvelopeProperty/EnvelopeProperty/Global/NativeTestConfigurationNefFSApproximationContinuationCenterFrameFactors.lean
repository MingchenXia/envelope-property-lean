import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationPowerCoherence
import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorCoherence

/-! # The native norm factor computed from an arbitrary model-centre frame

The native model potential of a linearized line `(M, α, e)` on a test configuration is
`-log c(x)`, where `c(x) = C.gaussNativeNormFactor …` is the valuation of a transition unit
at the Gauss point over `x`, defined with one CHOSEN frame at the centre of that Gauss point.
For the power and tensor laws one needs the same factor computed with other centre frames
(powers and tensors of chosen frames).  This file proves:

* `gaussPowerSectionNorm_eq_centerFactor`: for any centre frame `e_C`, the Gauss norm of
  every section `s` of `M^{⊗ n}` is `c(e_C)^n` times its weighted Laurent norm;
* `gaussNativeNormFactor_eq_centerFactor`: if the generic line `L` is ample, then
  `c(e_C)` is the native factor, by uniqueness of such a factor
  (`existsUnique_weightedLaurentPowerSectionNorm_powerFactor`).

This is the frame-independence of `log |s|` used in FHX §2.2 (after `eq:FS-function`:
"the choice of trivialization does not matter").
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
open SchemePulledPowerFrames Berkovich.SchemeLinePowerFrameNorms SchemeModuleFrameCoefficients
open Berkovich.SchemeFramedSectionPullback Berkovich.SchemeResidueFrameComparison
variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (C : TestConfiguration k X)
private local instance projectionProper : IsProper C.projection := C.projection_isProper

/-- An actual whole line frame on the proper valuation centre of the SAME
original product Gauss model point. -/
def gaussModelCenterFrame (M : C.total.Modules) (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :=
  centerLineModule (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) M ≅
    unitObj (Spec (.of (CenterRing
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)))))

variable (M : C.total.Modules) (hM : IsInvertible M)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (eC : C.gaussModelCenterFrame M r hr hru x)

/-- The actual generic frame induced by the whole original model centre frame. -/
def gaussCenterTargetFrame :=
  centerFrameGenericIso (Spectrum.trivialGaussValuation_le_one k r hru)
    (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) eC

/-- Every genuine original centre frame gives model norm one in all actual powers. -/
theorem gaussCenterTargetFrame_power_norm_one (n : ℕ) :
    modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
      (unitSection (pullbackPowerFrame
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
        (C.gaussCenterTargetFrame M r hr hru x eC) n)) = 1 := by
  let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let F := fun E => modelLineNorm hb z (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
    (unitSection E)
  have hp := congrArg F (pullbackPowerFrame_generic z (C.gaussCenterTargetFrame M r hr hru x eC) n)
  have hc := congrArg F (centerFrameGenericIso_centerPowerFrame z hb eC n).symm
  exact hp.trans (hc.trans (modelLineNorm_centerPowerFrame_unitSection z hb hM eC n))

variable (L : X.left.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)

/-- Actual model unit norms, rather than a chosen frame equality, compute
the original norm in every degree and for every original total section. -/
theorem gaussPowerSectionNorm_eq_centerFrame (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.gaussPowerSectionNorm M hM r hr hru x n s =
      (C.productGaussSource x r hr).1.residueVal
        (residueFrameCoefficient (C.productGaussSource x r hr).1
          ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
              (bundleTensorPower L n))
          (C.productModelPowerResidueFrame M L alpha e (C.productGaussSource x r hr).1
            (C.gaussCenterTargetFrame M r hr hru x eC) n)
          (C.globalProductPowerSection M L alpha e n s)) := by
  let y := C.productGaussSource x r hr
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let B := bundleTensorPower M n
  let hB := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n
  let ep := pullbackPowerFrame (C.total.fromSpecResidueField (C.productTotalMap y.1.point))
    (C.gaussCenterTargetFrame M r hr hru x eC) n
  have h := modelLineNorm_framedPullback hb C.productTotalMap y hB
    (C.productTotalLinePowerIso M L alpha e n) ep s
  have hu := C.gaussCenterTargetFrame_power_norm_one M hM r hr hru x eC n
  have he := h.trans ((congrArg (fun a => y.1.residueVal
    (residueFrameCoefficient y.1 _ (C.productModelPowerResidueFrame M L alpha e y.1
      (C.gaussCenterTargetFrame M r hr hru x eC) n)
      (C.globalProductPowerSection M L alpha e n s)) * a) hu).trans (mul_one _))
  let F : RelativeSchemeValuedPoint (Spectrum.trivialGaussValuation k r) C.projection → ℝ≥0 :=
    fun z => modelLineNorm hb z hB
      (affinePullbackUnitTop (C.total.fromSpecResidueField z.1.point) B s)
  have hp : F (C.relativeGaussPoint x r hr) =
      F (RelativeSchemeValuedPoint.map C.productTotalMap rfl y) :=
    congrArg F (C.productGaussSource_map x r hr).symm
  have hs := SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
    (C.total.fromSpecResidueField (C.relativeGaussPoint x r hr).1.point) B s
  have hn := congrArg (modelLineNorm hb (C.relativeGaussPoint x r hr) hB) hs.symm
  exact hn.trans (hp.trans he)

variable (U : X.left.Opens)
    (hy : (C.productGaussSource x r hr).1.point ∈
        (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme)

/-- The actual factor determined by this same whole model centre frame. -/
def gaussCenterNormFactor : ℝ≥0 :=
  (C.productGaussSource x r hr).1.residueVal
    (C.productFrameTransitionUnit M L alpha e (C.productGaussSource x r hr).1
      (C.gaussCenterTargetFrame M r hr hru x eC) U hy eU).val

/-- Actual transition units force positivity independently of section existence. -/
theorem gaussCenterNormFactor_pos :
    0 < C.gaussCenterNormFactor M r hr hru x eC L alpha e U hy eU :=
  C.productFrameTransitionUnit_value_pos M L alpha e (C.productGaussSource x r hr).1
    (C.gaussCenterTargetFrame M r hr hru x eC) U hy eU
    (C.productGaussSource x r hr).1.residueVal

section OriginalFrame
variable [IsProper X.hom]

/-- Every actual original centre frame satisfies the same whole section
norm factor law, retaining the original sections, action and fibre one. -/
theorem gaussPowerSectionNorm_eq_centerFactor (hL : IsInvertible L)
    (hc : center Valuation.one_apply_le_one x ∈ U)
    (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.gaussPowerSectionNorm M hM r hr hru x n s =
      C.gaussCenterNormFactor M r hr hru x eC L alpha e U hy eU ^ n *
        C.weightedLaurentPowerSectionNorm M L alpha e hL r x n s := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  let P := (C.productGaussSource x r hr).1
  let N := (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
      (bundleTensorPower L n)
  let eM := C.gaussCenterTargetFrame M r hr hru x eC
  let eX := productReferenceResidueFrame (bundleTensorPower L n) P U hy
      (pullbackPowerFrame U.ι eU n)
  let eTC := C.productModelPowerResidueFrame M L alpha e P eM n
  let tau := C.globalProductPowerSection M L alpha e n s
  have hn := C.gaussPowerSectionNorm_eq_centerFrame M hM r hr hru x eC L alpha e n s
  have he := residueFrameCoefficient_value_change P N eX eTC tau
  have hu := C.productPowerFrame_transitionUnit_value M L alpha e P eM U hy eU P.residueVal n
  have hx := SchemeSupportFrameEvaluation.laurentSupportFrame_value X.hom x
      Valuation.one_apply_le_one
    (bundleTensorPower L n) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
    U hc (pullbackPowerFrame U.ι eU n) r hr tau
  have hx' : P.residueVal (residueFrameCoefficient P N eX tau) =
      C.weightedLaurentPowerSectionNorm M L alpha e hL r x n s := hx
  exact hn.trans (he.trans (congrArg₂ (fun a b : ℝ≥0 => a * b) hu hx'))

/-- Ordinary ampleness of the actual generic line makes every genuine
model centre frame compute the SAME defined native factor. -/
theorem gaussNativeNormFactor_eq_centerFactor (hL : IsInvertible L)
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (hc : center Valuation.one_apply_le_one x ∈ U) :
    C.gaussNativeNormFactor M hM L alpha e hL r hr hru x =
      C.gaussCenterNormFactor M r hr hru x eC L alpha e U hy eU := by
  obtain ⟨c, _, hu⟩ := C.existsUnique_weightedLaurentPowerSectionNorm_powerFactor
    M hM L hAmp alpha e r hr hru x
  have hnative := hu (C.gaussNativeNormFactor M hM L alpha e hL r hr hru x)
    ⟨C.gaussNativeNormFactor_pos M hM L alpha e hL r hr hru x,
      fun n s => C.gaussNativeNormFactor_spec M hM L alpha e hL r hr hru x n s⟩
  have hcenter := hu (C.gaussCenterNormFactor M r hr hru x eC L alpha e U hy eU)
    ⟨C.gaussCenterNormFactor_pos M r hr hru x eC L alpha e U hy eU,
      fun n s => C.gaussPowerSectionNorm_eq_centerFactor
        M hM r hr hru x eC L alpha e U hy eU hL hc n s⟩
  exact hnative.trans hcenter.symm

end OriginalFrame
end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
