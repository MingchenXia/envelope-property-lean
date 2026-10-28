import EnvelopeProperty.Global.NativeTestConfigurationNormFactorUniqueness

/-! # Actual native unit factor, with original-center frame independence -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (C : TestConfiguration k X)

/-- Choose ACTUAL original center-open/frame data, before every radius, power and section. -/
def originalCenterOpenFrame (L : X.left.Modules) (hL : IsInvertible L)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    letI : IsProper X.hom := C.original_isProper
    Σ U : X.left.Opens, { _e : (pullback U.ι).obj L ≅ unitObj U.toScheme //
      center Valuation.one_apply_le_one x ∈ U } := by
  let : IsProper X.hom := C.original_isProper
  apply Classical.choice
  obtain ⟨ι, U, hU, hframe⟩ := hL
  have hc : center Valuation.one_apply_le_one x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  obtain ⟨e⟩ := hframe i
  exact ⟨⟨U i, e, hi⟩⟩

private theorem productPoint_mem_centerOpen [IsProper X.hom]
    (r : ℝ≥0) (hr : 0 < r) (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (U : X.left.Opens) (hc : center Valuation.one_apply_le_one x ∈ U) :
    (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U := by
  have h := congrArg SchemeValuedPoint.point
    (SchemePointLaurentLocalFrame.openPoint_comp X.hom x Valuation.one_apply_le_one U hc r hr)
  change (SchemePointLaurentGauss.productPoint X.hom x r hr).1.point ∈
    (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U
  rw [← h]
  exact (SchemePointLaurentLocalFrame.openPoint X.hom x Valuation.one_apply_le_one U hc r hr).point.property

variable (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (hL : IsInvertible L) (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)

/-- Define the factor by the ACTUAL native transition unit of actual original geometric frames. -/
def gaussNativeNormFactor : ℝ≥0 := by
  letI : IsProper X.hom := C.original_isProper
  let F := C.originalCenterOpenFrame L hL x
  exact C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ F.1
    (productPoint_mem_centerOpen C r hr x F.1 F.2.2) F.2.1

/-- Positivity of the actual native unit factor. -/
theorem gaussNativeNormFactor_pos : 0 < C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x := by
  let : IsProper X.hom := C.original_isProper
  let F := C.originalCenterOpenFrame L hL x
  exact C.gaussCompatibleNormFactor_pos M hM r hr hru x L α e₁ F.1
    (productPoint_mem_centerOpen C r hr x F.1 F.2.2) F.2.1

/-- The actual native unit definition satisfies EVERY original degree and EVERY original section's true norm identity. -/
theorem gaussNativeNormFactor_spec (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.gaussPowerSectionNorm M hM r hr hru x n s =
      C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x ^ n *
        C.weightedLaurentPowerSectionNorm M L α e₁ hL r x n s := by
  let : IsProper X.hom := C.original_isProper
  let F := C.originalCenterOpenFrame L hL x
  exact C.gaussPowerSectionNorm_eq_compatibleFactor M hM r hr hru x L α e₁ F.1 F.2.1 hL F.2.2 n s

/-- Original geometric ampleness proves independence from EVERY actual original center-open/frame choice. -/
theorem gaussNativeNormFactor_eq_compatibleFactor [IsProper X.hom]
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) (U : X.left.Opens)
    (hc : center Valuation.one_apply_le_one x ∈ U)
    (hy : (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    C.gaussNativeNormFactor M hM L α e₁ hL r hr hru x =
      C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hy e := by
  let F := C.originalCenterOpenFrame L hL x
  exact C.gaussCompatibleNormFactor_eq_of_frames M hM L hAmp α e₁ r hr hru x F.1 U F.2.2 hc
    (productPoint_mem_centerOpen C r hr x F.1 F.2.2) hy F.2.1 e

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
