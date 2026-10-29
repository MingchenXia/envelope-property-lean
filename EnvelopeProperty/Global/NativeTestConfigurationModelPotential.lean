import EnvelopeProperty.Global.NativeTestConfigurationIntrinsicNormFactor
import EnvelopeProperty.Global.NativeTestConfigurationUniformWeightedFS

/-! # Actual native model potentials and genuine finite rational FS minorants -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory Scheme.Modules
open scoped NNReal ENNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
open SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (hL : IsInvertible L)
private local instance actualProjectionProper : IsProper C.projection := C.projection_isProper

/-- The model potential is the negative real logarithm of an ACTUAL native geometric transition-unit value. -/
def gaussNativeModelPotential (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) : ℝ :=
  -Real.log (C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x : ℝ)

/-- Original ampleness proves the actual potential agrees with EVERY genuine original center-open frame. -/
theorem gaussNativeModelPotential_eq_compatibleFactor
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) :
    letI : IsProper X.hom := C.original_isProper
    ∀ (U : X.left.Opens) (_hc : center Valuation.one_apply_le_one x ∈ U)
      (hy : (C.productGaussSource x r hr).1.point ∈
        (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
      (e : (pullback U.ι).obj L ≅ unitObj U.toScheme),
      C.gaussNativeModelPotential M hM L α e₁ hL r hr hru x =
        -Real.log (C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hy e : ℝ) := by
  let : IsProper X.hom := C.original_isProper
  intro U _hc hy e
  exact congrArg (fun c : ℝ≥0 => -Real.log (c : ℝ))
    (C.gaussNativeNormFactor_eq_compatibleFactor M hM L α e₁ hL r hr hru x hAmp U _hc hy e)

/-- The ACTUAL defined factor computes EVERY whole original finite family in EVERY degree. -/
theorem gaussPowerFamilyNorm_eq_nativeFactor
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (n : ℕ) (G : Finset Γ(bundleTensorPower M n, ⊤)) :
    G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) =
      C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x ^ n *
        (C.globalPowerLaurentTerms M L α e₁ hL n G).sup (fun t =>
          C.originalPowerSectionNorm L hL x n t.1 * r ^ t.2) := by
  let : IsProper X.hom := C.original_isProper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  simp_rw [C.gaussNativeNormFactor_spec M hM L α e₁ hL r hr hru x]
  rw [← Finset.mul_sup₀]
  congr 1
  simp only [globalPowerLaurentTerms,
    globalProductPowerFamily, SchemeModuleLaurentCoefficients.terms,
    Finset.sup_biUnion, Finset.sup_image]
  rfl

/-- EVERY actual original weighted FS family has the SAME actual native model-potential comparison. -/
theorem gaussNativeModelPotential_weightedFSData_eval
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (n : ℕ) (hn : 0 < n) (G : Finset Γ(bundleTensorPower M n, ⊤)) :
    letI : IsProper X.hom := C.original_isProper
    (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x =
      (C.gaussNativeModelPotential M hM L α e₁ hL r hr hru x : EReal) +
        (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
          ((G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) : ℝ≥0) : ℝ≥0∞) := by
  let : IsProper X.hom := C.original_isProper
  let c := C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x
  have hc : 0 < c := C.gaussNativeNormFactor_pos M hM L α e₁ hL r hr hru x
  have hcoef : (n : ℝ)⁻¹ * Real.log ((c ^ n : ℝ≥0) : ℝ) = Real.log (c : ℝ) := by
    rw [NNReal.coe_pow, Real.log_pow, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  have hshift : (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
      ((G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) : ℝ≥0) : ℝ≥0∞) =
        (Real.log (c : ℝ) : EReal) + (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x := by
    rw [C.gaussPowerFamilyNorm_eq_nativeFactor M hM L α e₁ hL r hr hru x n G,
      ENNReal.coe_mul, ENNReal.log_mul_add, ENNReal.log_of_nnreal (pow_ne_zero _ hc.ne'),
      ProjBerk.ereal_coe_mul_add (by positivity), ← EReal.coe_mul, hcoef,
      C.weightedFSData_eval M L α e₁ hL n hn G r hr x]
  rw [hshift, gaussNativeModelPotential, ← add_assoc, ← EReal.coe_add,
    neg_add_cancel, EReal.coe_zero, zero_add]

/-- Original ampleness produces true finite rational FS functions below the ACTUAL native model potential. -/
theorem exists_eventual_finiteFS_modelPotential_minorants
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) :
    letI : IsProper X.hom := C.original_isProper
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
      ∃ G : Finset Γ(bundleTensorPower M n, ⊤),
        NativeLineFubiniStudy.IsFinFS X.hom L hL 1
          (fun x => (C.weightedFSData M L α e₁ hL n hn G weightedFSRadius).eval X.hom hL x) ∧
        ∀ x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom,
          (C.weightedFSData M L α e₁ hL n hn G weightedFSRadius).eval X.hom hL x =
            (C.gaussNativeModelPotential M hM L α e₁ hL weightedFSRadius
              weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x : EReal) +
              C.gaussPowerBaseIdealLogNormalized M hM weightedFSRadius
                weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x n ∧
          (C.weightedFSData M L α e₁ hL n hn G weightedFSRadius).eval X.hom hL x ≤
            (C.gaussNativeModelPotential M hM L α e₁ hL weightedFSRadius
              weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x : EReal) := by
  let : IsProper X.hom := C.original_isProper
  let r := weightedFSRadius
  let hr := weightedFSRadius_properties.1
  let hru := weightedFSRadius_properties.2.1
  obtain ⟨N, hN⟩ := C.exists_eventual_finite_gauss_power_section_norms M hM L hAmp α e₁ r hr hru
  refine ⟨N, fun n hn hnpos => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let D := C.weightedFSData M L α e₁ hL n hnpos G r
  have he (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
      D.eval X.hom hL x =
        (C.gaussNativeModelPotential M hM L α e₁ hL r hr hru x : EReal) +
          C.gaussPowerBaseIdealLogNormalized M hM r hr hru x n := by
    have h := C.gaussNativeModelPotential_weightedFSData_eval M hM L α e₁ hL r hr hru x n hnpos G
    change D.eval X.hom hL x = _ at h
    rw [← (hG x).1] at h
    exact h
  have hNZ (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
      ∃ q ∈ D.terms, globalSectionNorm Valuation.one_apply_le_one x
        (bundleTensorPower L D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 ≠ 0 := by
    apply (D.eval_ne_bot_iff_exists_norm_ne_zero X.hom L hL x).mp
    rw [C.gaussNativeModelPotential_weightedFSData_eval M hM L α e₁ hL r hr hru x n hnpos G,
      ENNReal.log_of_nnreal (hG x).2.1.ne', ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  refine ⟨G, ⟨D, C.weightedFSData_isRational M L α e₁ hL n hnpos G, hNZ, fun _ => rfl⟩, fun x => ⟨he x, ?_⟩⟩
  rw [he x]
  have hlog : C.gaussPowerBaseIdealLogNormalized M hM r hr hru x n ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    exact ENNReal.log_le_zero_iff.mpr (modelIdealNorm_le_one _ _ _)
  have hbound :
      (C.gaussNativeModelPotential M hM L α e₁ hL r hr hru x : EReal) +
        C.gaussPowerBaseIdealLogNormalized M hM r hr hru x n ≤
      (C.gaussNativeModelPotential M hM L α e₁ hL r hr hru x : EReal) + 0 :=
    add_le_add le_rfl hlog
  simpa only [add_zero] using hbound

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
