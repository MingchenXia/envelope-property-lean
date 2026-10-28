import EnvelopeProperty.Global.NativeTestConfigurationCompatiblePowerFrames
import EnvelopeProperty.Global.NativeTestConfigurationWeightedSectionNorms

/-! # One genuine proper-center frame and ONE positive factor before ALL degrees and sections -/
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

variable (M : C.total.Modules) (hM : IsInvertible M)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)

/-- ONE actual proper-center original unit frame is chosen before ALL degrees and sections. -/
def gaussCompatibleCenterFrame :=
  Classical.choice (exists_centerLineUnitIso (Spectrum.trivialGaussValuation_le_one k r hru)
    (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hM)

/-- The actual generic target frame comes from that SAME original proper-center frame. -/
def gaussCompatibleTargetFrame :=
  centerFrameGenericIso (Spectrum.trivialGaussValuation_le_one k r hru)
    (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
    (C.gaussCompatibleCenterFrame M hM r hr hru x)

/-- EVERY actual compatible target power-frame unit has true original proper-model norm one. -/
theorem gaussCompatibleTargetFrame_power_norm_one (n : ℕ) :
    modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
      (unitSection (pullbackPowerFrame
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
        (C.gaussCompatibleTargetFrame M hM r hr hru x) n)) = 1 := by
  let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let eC := C.gaussCompatibleCenterFrame M hM r hr hru x
  let F := fun E => modelLineNorm hb z (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n) (unitSection E)
  have hp := congrArg F (pullbackPowerFrame_generic z (C.gaussCompatibleTargetFrame M hM r hr hru x) n)
  have hc := congrArg F (centerFrameGenericIso_centerPowerFrame z hb eC n).symm
  exact hp.trans (hc.trans (modelLineNorm_centerPowerFrame_unitSection z hb hM eC n))

variable (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)

/-- ONE actual proper-center target frame computes EVERY degree and EVERY original section's true norm. -/
theorem gaussPowerSectionNorm_eq_compatibleFrame (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.gaussPowerSectionNorm M hM r hr hru x n s =
      (C.productGaussSource x r hr).1.residueVal
        (residueFrameCoefficient (C.productGaussSource x r hr).1
          ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj (bundleTensorPower L n))
          (C.productModelPowerResidueFrame M L α e₁ (C.productGaussSource x r hr).1
            (C.gaussCompatibleTargetFrame M hM r hr hru x) n)
          (C.globalProductPowerSection M L α e₁ n s)) := by
  let y := C.productGaussSource x r hr
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let B := bundleTensorPower M n
  let hB := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n
  let ep := pullbackPowerFrame (C.total.fromSpecResidueField (C.productTotalMap y.1.point))
    (C.gaussCompatibleTargetFrame M hM r hr hru x) n
  have h := modelLineNorm_framedPullback hb C.productTotalMap y hB
    (C.productTotalLinePowerIso M L α e₁ n) ep s
  have hu := C.gaussCompatibleTargetFrame_power_norm_one M hM r hr hru x n
  have he := h.trans ((congrArg (fun a => y.1.residueVal
    (residueFrameCoefficient y.1 _ (C.productModelPowerResidueFrame M L α e₁ y.1
      (C.gaussCompatibleTargetFrame M hM r hr hru x) n) (C.globalProductPowerSection M L α e₁ n s)) * a) hu).trans (mul_one _))
  let F : RelativeSchemeValuedPoint (Spectrum.trivialGaussValuation k r) C.projection → ℝ≥0 :=
    fun z => modelLineNorm hb z hB (affinePullbackUnitTop (C.total.fromSpecResidueField z.1.point) B s)
  have hp : F (C.relativeGaussPoint x r hr) = F (RelativeSchemeValuedPoint.map C.productTotalMap rfl y) :=
    congrArg F (C.productGaussSource_map x r hr).symm
  have hs := SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
    (C.total.fromSpecResidueField (C.relativeGaussPoint x r hr).1.point) B s
  have hn := congrArg (modelLineNorm hb (C.relativeGaussPoint x r hr) hB) hs.symm
  exact hn.trans (hp.trans he)

variable (U : X.left.Opens)
    (hy : (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme)

/-- The ACTUAL native unit valuation defines one factor before every degree and every section. -/
def gaussCompatibleNormFactor : ℝ≥0 :=
  (C.productGaussSource x r hr).1.residueVal
    (C.productFrameTransitionUnit M L α e₁ (C.productGaussSource x r hr).1
      (C.gaussCompatibleTargetFrame M hM r hr hru x) U hy eU).val

/-- Positivity follows from the actual native unit, without any section-existence argument. -/
theorem gaussCompatibleNormFactor_pos :
    0 < C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hy eU :=
  C.productFrameTransitionUnit_value_pos M L α e₁ (C.productGaussSource x r hr).1
    (C.gaussCompatibleTargetFrame M hM r hr hru x) U hy eU (C.productGaussSource x r hr).1.residueVal

section OriginalFrame
variable [IsProper X.hom]

private theorem gaussPoint_mem_frameOpen
    (hc : center Valuation.one_apply_le_one x ∈ U) :
    (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U := by
  have h := congrArg SchemeValuedPoint.point
    (SchemePointLaurentLocalFrame.openPoint_comp X.hom x Valuation.one_apply_le_one U hc r hr)
  change (SchemePointLaurentGauss.productPoint X.hom x r hr).1.point ∈
    (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U
  rw [← h]
  exact (SchemePointLaurentLocalFrame.openPoint X.hom x Valuation.one_apply_le_one U hc r hr).point.property

/-- This ONE actual proper-center-frame factor works in EVERY degree for EVERY original total-space section. -/
theorem gaussPowerSectionNorm_eq_compatibleFactor (hL : IsInvertible L)
    (hc : center Valuation.one_apply_le_one x ∈ U) (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.gaussPowerSectionNorm M hM r hr hru x n s =
      C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U
        (gaussPoint_mem_frameOpen C r hr x U hc) eU ^ n *
          C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  let P := (C.productGaussSource x r hr).1
  let N := (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj (bundleTensorPower L n)
  let hP := gaussPoint_mem_frameOpen C r hr x U hc
  let eM := C.gaussCompatibleTargetFrame M hM r hr hru x
  let eX := productReferenceResidueFrame (bundleTensorPower L n) P U hP (pullbackPowerFrame U.ι eU n)
  let eTC := C.productModelPowerResidueFrame M L α e₁ P eM n
  let τ := C.globalProductPowerSection M L α e₁ n s
  have hn := C.gaussPowerSectionNorm_eq_compatibleFrame M hM r hr hru x L α e₁ n s
  have he := residueFrameCoefficient_value_change P N eX eTC τ
  have hu := C.productPowerFrame_transitionUnit_value M L α e₁ P eM U hP eU P.residueVal n
  have hx := SchemeSupportFrameEvaluation.laurentSupportFrame_value X.hom x Valuation.one_apply_le_one
    (bundleTensorPower L n) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
    U hc (pullbackPowerFrame U.ι eU n) r hr τ
  have hx' : P.residueVal (residueFrameCoefficient P N eX τ) =
      C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s := hx
  exact hn.trans (he.trans (congrArg₂ (fun a b : ℝ≥0 => a * b) hu hx'))

end OriginalFrame

omit U hy eU in
/-- Original invertibility DERIVES ONE positive native factor BEFORE ALL degrees and ALL original sections. -/
theorem exists_weightedLaurentPowerSectionNorm_powerFactor (hL : IsInvertible L) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ n : ℕ, ∀ s : Γ(bundleTensorPower M n, ⊤),
      C.gaussPowerSectionNorm M hM r hr hru x n s =
        c ^ n * C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨ι, U, hU, hframe⟩ := hL
  have hc : center Valuation.one_apply_le_one x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  obtain ⟨eU⟩ := hframe i
  let hp := gaussPoint_mem_frameOpen C r hr x (U i) hi
  refine ⟨C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ (U i) hp eU,
    C.gaussCompatibleNormFactor_pos M hM r hr hru x L α e₁ (U i) hp eU, ?_⟩
  intro n s
  exact C.gaussPowerSectionNorm_eq_compatibleFactor M hM r hr hru x L α e₁ (U i) eU
    ⟨ι, U, hU, hframe⟩ hi n s

omit U hy eU in
/-- The SAME native positive factor works for ALL degrees, ALL original sections and ALL original finite families. -/
theorem exists_weightedLaurentPowerNorms_powerFactor (hL : IsInvertible L) :
    ∃ c : ℝ≥0, 0 < c ∧
      (∀ n : ℕ, ∀ s : Γ(bundleTensorPower M n, ⊤),
        C.gaussPowerSectionNorm M hM r hr hru x n s =
          c ^ n * C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s) ∧
      (∀ n : ℕ, ∀ G : Finset Γ(bundleTensorPower M n, ⊤),
        G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) =
          c ^ n * (C.globalPowerLaurentTerms M L α e₁ hL n G).sup (fun t =>
            C.originalPowerSectionNorm L hL x n t.1 * r ^ t.2)) := by
  obtain ⟨c, hc, hs⟩ := C.exists_weightedLaurentPowerSectionNorm_powerFactor M hM r hr hru x L α e₁ hL
  refine ⟨c, hc, hs, fun n G => ?_⟩
  let : IsProper X.hom := C.original_isProper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  simp_rw [hs]
  rw [← Finset.mul_sup₀]
  congr 1
  simp only [globalPowerLaurentTerms, globalProductPowerFamily, SchemeModuleLaurentCoefficients.terms,
    Finset.sup_biUnion, Finset.sup_image]
  rfl

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
