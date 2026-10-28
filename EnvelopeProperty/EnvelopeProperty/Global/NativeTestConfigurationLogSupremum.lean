import EnvelopeProperty.Global.NativeTestConfigurationGaussNorms
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-! # Genuine original all-degree logarithmic base-ideal convergence and supremum -/
open AlgebraicGeometry CategoryTheory Scheme.Modules Filter Topology Set
open scoped NNReal ENNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)

private local instance logProjectionProper : IsProper C.projection := C.projection_isProper

/-- The actual ALL-original-global-section base ideal's normalized logarithmic norm. -/
def gaussPowerBaseIdealLogNormalized (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (m : ℕ) : EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
    (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m)
      (Spectrum.trivialGaussValuation_le_one k r hru) (C.relativeGaussPoint x r hr))

/-- The literal old real normalized root has EXACTLY the genuine normalized ideal logarithm. -/
theorem gaussPowerBaseIdealLogNormalized_eq_rootLog
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (m : ℕ) :
    C.gaussPowerBaseIdealLogNormalized M hM r hr hru x m =
      ENNReal.log (ENNReal.ofReal (C.gaussPowerBaseIdealNormalizedRoot M hM r hr hru x m)) := by
  let I := modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m)
    (Spectrum.trivialGaussValuation_le_one k r hru) (C.relativeGaussPoint x r hr)
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (modelIdealNorm_le_one _ _ _)
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log I =
    ENNReal.log (ENNReal.ofReal (I.toReal ^ (1 / (m : ℝ))))
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hI, ENNReal.log_rpow, one_div]

variable (L : X.left.Modules) (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)

include L hAmp α e₁ in
/-- Actual source ampleness derives the finite nonpositive log limit and supremum over ALL positive degrees. -/
theorem exists_gauss_log_normalized_supremum
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    ∃ a : ℝ, a ≤ 0 ∧
      Tendsto (C.gaussPowerBaseIdealLogNormalized M hM r hr hru x) atTop (𝓝 (a : EReal)) ∧
      IsLUB {q : EReal | ∃ m : ℕ, 0 < m ∧
        q = C.gaussPowerBaseIdealLogNormalized M hM r hr hru x m} (a : EReal) := by
  obtain ⟨b, hb, hbone, hlim, hsup⟩ := C.exists_gauss_normalized_supremum M hM L hAmp α e₁ r hr hru x
  have hlogb : ENNReal.log (ENNReal.ofReal b) = (Real.log b : EReal) :=
    ENNReal.log_ofReal_of_pos hb
  have hloglim := (ENNReal.continuous_log.tendsto (ENNReal.ofReal b)).comp
    ((ENNReal.continuous_ofReal.tendsto b).comp hlim)
  have hlim' : Tendsto (C.gaussPowerBaseIdealLogNormalized M hM r hr hru x) atTop
      (𝓝 ((Real.log b : ℝ) : EReal)) := by
    have hf : C.gaussPowerBaseIdealLogNormalized M hM r hr hru x =
        ENNReal.log ∘ ENNReal.ofReal ∘ C.gaussPowerBaseIdealNormalizedRoot M hM r hr hru x :=
      funext (C.gaussPowerBaseIdealLogNormalized_eq_rootLog M hM r hr hru x)
    rw [hf]
    simpa only [hlogb] using hloglim
  refine ⟨Real.log b, Real.log_nonpos hb.le hbone, hlim', ?_, ?_⟩
  · rintro q ⟨m, hm, rfl⟩
    rw [C.gaussPowerBaseIdealLogNormalized_eq_rootLog M hM, ← hlogb]
    exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (hsup.1 ⟨m, hm, rfl⟩))
  · intro c hc
    apply le_of_tendsto hlim'
    exact eventually_atTop.mpr ⟨1, fun m hm => hc ⟨m, hm, rfl⟩⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
