import EnvelopeProperty.Global.NativeTestConfigurationGaussPoint
import EnvelopeProperty.Global.NativeTestConfigurationNormalizedSupremum

/-! # Genuine original TC norm limits and finite families at the actual Gauss point -/
open AlgebraicGeometry CategoryTheory Scheme.Modules Set Filter Topology
open scoped Classical Polynomial NNReal ENNReal
noncomputable section
universe u

namespace EnvelopeProperty.Berkovich.Spectrum

/-- The actual Gauss maximum on EVERY original polynomial is bounded by one
when the original coefficient values and the radius are bounded by one. -/
theorem gauss_val_le_one {A : Type u} [CommRing A] (y : Spectrum A)
    (hy : ∀ a, y.val a ≤ 1) (r : ℝ≥0) (hr : r ≤ 1) (F : A[X]) :
    (gauss y r).val F ≤ 1 := by
  apply (gauss_val_le_iff y r F 1).mpr
  intro i
  exact (mul_le_mul' (hy _) (pow_le_one₀ (show 0 ≤ r from bot_le) hr)).trans (by simp)

/-- The native polynomial Gauss valuation of the ORIGINAL trivially valued field. -/
def trivialGaussValuation (k : Type u) [Field k] (r : ℝ≥0) : Valuation k[X] ℝ≥0 :=
  (gauss (ofValuation (1 : Valuation k ℝ≥0)) r).val

@[simp] theorem trivialGaussValuation_X (k : Type u) [Field k] (r : ℝ≥0) :
    trivialGaussValuation k r (Polynomial.X : k[X]) = r :=
  gauss_val_X _ _

/-- Boundedness of the ENTIRE actual original parameter ring is DERIVED. -/
theorem trivialGaussValuation_le_one (k : Type u) [Field k] (r : ℝ≥0) (hr : r ≤ 1)
    (F : k[X]) : trivialGaussValuation k r F ≤ 1 :=
  gauss_val_le_one _ Valuation.one_apply_le_one r hr F

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)

private local instance actualProjectionProper : IsProper C.projection := C.projection_isProper

/-- The true ALL-section ideal norm root evaluated at the ACTUAL original Gauss point. -/
def gaussPowerBaseIdealNormalizedRoot (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (m : ℕ) : ℝ :=
  powerBaseIdealNormalizedRoot hM (Spectrum.trivialGaussValuation_le_one k r hru)
    (C.relativeGaussPoint x r hr) m

/-- The norm of the SAME actual original global section at the actual original Gauss point. -/
def gaussPowerSectionNorm (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (m : ℕ)
    (s : Γ(bundleTensorPower M m, ⊤)) : ℝ≥0 :=
  modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
    (C.relativeGaussPoint x r hr) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    (fibreSection (C.relativeGaussPoint x r hr)
      (SchemeModuleGlobalSections.sectionHom (bundleTensorPower M m) s))

variable (L : X.left.Modules) (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L)

include L hAmp α e₁

/-- Genuine original ampleness yields the ACTUAL original Gauss norm limit
and its supremum over ALL positive original degrees, with no matching input. -/
theorem exists_gauss_normalized_supremum (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
      Tendsto (C.gaussPowerBaseIdealNormalizedRoot M hM r hr hru x) atTop (𝓝 b) ∧
      IsLUB {q : ℝ | ∃ m : ℕ, 0 < m ∧
        q = C.gaussPowerBaseIdealNormalizedRoot M hM r hr hru x m} b := by
  have ht : Spectrum.trivialGaussValuation k r Polynomial.X ≠ 0 := by
    rw [Spectrum.trivialGaussValuation_X]
    exact hr.ne'
  exact C.exists_powerBaseIdeal_normalized_supremum M hM L hAmp α e₁
    (Spectrum.trivialGaussValuation_le_one k r hru) ht (C.relativeGaussPoint x r hr)

/-- ONE genuine original finite total-section family per eventual degree is
chosen BEFORE x and computes every actual original Gauss-point ideal norm. -/
theorem exists_eventual_finite_gauss_power_section_norms
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ G : Finset Γ(bundleTensorPower M m, ⊤),
      ∀ x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom,
        modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m)
            (Spectrum.trivialGaussValuation_le_one k r hru) (C.relativeGaussPoint x r hr) =
          ((G.sup fun s => C.gaussPowerSectionNorm M hM r hr hru x m s : ℝ≥0) : ℝ≥0∞) ∧
        0 < G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x m s) ∧
        G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x m s) ≤ 1 := by
  have ht : Spectrum.trivialGaussValuation k r Polynomial.X ≠ 0 := by
    rw [Spectrum.trivialGaussValuation_X]
    exact hr.ne'
  obtain ⟨N, hN⟩ := C.exists_eventual_finite_power_section_norms M hM L hAmp α e₁
    (Spectrum.trivialGaussValuation_le_one k r hru) ht
  exact ⟨N, fun m hm => let ⟨G, hG⟩ := hN m hm; ⟨G, fun x => hG (C.relativeGaussPoint x r hr)⟩⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
