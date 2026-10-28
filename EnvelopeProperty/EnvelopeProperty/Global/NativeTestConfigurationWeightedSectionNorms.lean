import EnvelopeProperty.Global.NativeTestConfigurationProductNorms
import EnvelopeProperty.Berkovich.SchemeSupportFrameEvaluation
import EnvelopeProperty.Berkovich.SchemeResidueFrameComparison
import Mathlib.Algebra.Order.Ring.Finset

/-! # True total-model section norms and weighted original Laurent coefficients -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X)

variable (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (hL : IsInvertible L)

/-- The genuine original proper-model norm of an original section of the original line power. -/
def originalPowerSectionNorm
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (n : ℕ)
    (s : Γ(bundleTensorPower L n, ⊤)) : ℝ≥0 := by
  letI : IsProper X.hom := C.original_isProper
  exact modelLineNorm Valuation.one_apply_le_one x
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
    (affinePullbackUnitTop (X.left.fromSpecResidueField x.1.point)
      (bundleTensorPower L n) s)

/-- The actual weighted maximum of the genuine original whole Laurent coefficients. -/
def weightedLaurentPowerSectionNorm (r : ℝ≥0)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (n : ℕ)
    (s : Γ(bundleTensorPower M n, ⊤)) : ℝ≥0 :=
  (C.globalPowerLaurentCoefficients M L α e₁ hL n s).support.sup fun i =>
    C.originalPowerSectionNorm L hL x n
      (C.globalPowerLaurentCoefficients M L α e₁ hL n s i) * r ^ i

/-- ONE derived positive factor compares ALL actual original sections in the same degree. -/
theorem exists_weightedLaurentPowerSectionNorm_factor
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ s : Γ(bundleTensorPower M n, ⊤),
      C.gaussPowerSectionNorm M hM r hr hru x n s =
        c * C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s := by
  let : IsProper X.hom := C.original_isProper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  obtain ⟨eTC, hTC⟩ :=
    C.exists_productResidueFrame_gaussPowerSectionNorm M hM L α e₁ r hr hru x n
  obtain ⟨eX, hX⟩ := SchemeSupportFrameEvaluation.exists_laurentSupportFrame_values_of_isInvertible
    X.hom x Valuation.one_apply_le_one (bundleTensorPower L n)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) r hr
  let P := (SchemePointLaurentGauss.productPoint X.hom x r hr).1
  let N := (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
    (bundleTensorPower L n)
  let c := P.residueVal (SchemeResidueFrameComparison.transitionUnit eX eTC).val
  refine ⟨c, SchemeResidueFrameComparison.transitionUnit_value_pos eX eTC P.residueVal, ?_⟩
  intro s
  exact (hTC s).trans
    ((SchemeResidueFrameComparison.residueFrameCoefficient_value_change P N eX eTC
      (C.globalProductPowerSection M L α e₁ n s)).trans
      (congrArg (fun a : ℝ≥0 => c * a) (hX (C.globalProductPowerSection M L α e₁ n s))))

/-- The same positive factor works for EVERY original finite family chosen before evaluation. -/
theorem exists_weightedLaurentPowerFamilyNorm_factor
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ G : Finset Γ(bundleTensorPower M n, ⊤),
      G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) =
        c * (C.globalPowerLaurentTerms M L α e₁ hL n G).sup (fun t =>
          C.originalPowerSectionNorm L hL x n t.1 * r ^ t.2) := by
  let : IsProper X.hom := C.original_isProper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  obtain ⟨c, hc, hs⟩ :=
    C.exists_weightedLaurentPowerSectionNorm_factor M hM L α e₁ hL r hr hru x n
  refine ⟨c, hc, fun G => ?_⟩
  simp_rw [hs]
  rw [← Finset.mul_sup₀]
  congr 1
  simp only [globalPowerLaurentTerms,
    globalProductPowerFamily, SchemeModuleLaurentCoefficients.terms,
    Finset.sup_biUnion, Finset.sup_image]
  rfl

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
