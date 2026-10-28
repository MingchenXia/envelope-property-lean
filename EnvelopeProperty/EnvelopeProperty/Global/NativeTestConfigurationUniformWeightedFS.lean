import EnvelopeProperty.Global.NativeTestConfigurationCoherentPowerNorms
import EnvelopeProperty.Global.NativeTestConfigurationWeightedFS
import EnvelopeProperty.Global.NativeTestConfigurationLogSupremum

/-! # One actual original logarithmic shift BEFORE every degree and family -/
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped NNReal ENNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (hL : IsInvertible L)

/-- The SAME actual real shift works BEFORE ALL positive degrees and ALL original finite families. -/
theorem exists_weightedFSData_uniformTotalLog_factor
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    letI : IsProper X.hom := C.original_isProper
    ∃ a : ℝ, ∀ n : ℕ, ∀ hn : 0 < n, ∀ G : Finset Γ(bundleTensorPower M n, ⊤),
      (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
        ((G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) : ℝ≥0) : ℝ≥0∞) =
          (a : EReal) + (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨c, hc, _, hG⟩ :=
    C.exists_weightedLaurentPowerNorms_powerFactor M hM r hr hru x L α e₁ hL
  refine ⟨Real.log (c : ℝ), fun n hn G => ?_⟩
  have hcoef : (n : ℝ)⁻¹ * Real.log ((c ^ n : ℝ≥0) : ℝ) = Real.log (c : ℝ) := by
    rw [NNReal.coe_pow, Real.log_pow, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  rw [hG n G, ENNReal.coe_mul, ENNReal.log_mul_add,
    ENNReal.log_of_nnreal (pow_ne_zero _ hc.ne'),
    ProjBerk.ereal_coe_mul_add (by positivity), ← EReal.coe_mul, hcoef,
    C.weightedFSData_eval M L α e₁ hL n hn G r hr x]

/-- Original source ampleness produces actual eventual all-section base-ideal FS identities with ONE function. -/
theorem exists_eventual_weightedFSData_idealLog_shift
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1) :
    letI : IsProper X.hom := C.original_isProper
    ∃ φ : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom → ℝ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
        ∃ G : Finset Γ(bundleTensorPower M n, ⊤),
          ∀ x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom,
            (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x =
              (φ x : EReal) + C.gaussPowerBaseIdealLogNormalized M hM r hr hru x n := by
  let : IsProper X.hom := C.original_isProper
  choose a ha using fun x => C.exists_weightedFSData_uniformTotalLog_factor M hM L α e₁ hL r hr hru x
  obtain ⟨N, hN⟩ := C.exists_eventual_finite_gauss_power_section_norms M hM L hAmp α e₁ r hr hru
  refine ⟨fun x => -a x, N, fun n hn hnpos => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  refine ⟨G, fun x => ?_⟩
  have h := ha x n hnpos G
  have hi := (hG x).1
  have hlog : C.gaussPowerBaseIdealLogNormalized M hM r hr hru x n =
      (a x : EReal) + (C.weightedFSData M L α e₁ hL n hnpos G r).eval X.hom hL x := by
    change (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log _ = _
    rw [hi]
    exact h
  rw [hlog, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
