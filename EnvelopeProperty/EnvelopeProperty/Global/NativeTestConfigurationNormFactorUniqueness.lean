import EnvelopeProperty.Global.NativeTestConfigurationCoherentPowerNorms

/-! # Original ampleness derives uniqueness and original-frame independence of the actual norm factor -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules) (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)

include L hAmp α e₁

/-- Genuine original ampleness DERIVES an actual positive-degree original section of positive true Gauss norm. -/
theorem exists_positive_gaussPowerSectionNorm :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(bundleTensorPower M n, ⊤),
      0 < C.gaussPowerSectionNorm M hM r hr hru x n s := by
  obtain ⟨N, hN⟩ := C.exists_eventual_finite_gauss_power_section_norms M hM L hAmp α e₁ r hr hru
  obtain ⟨G, hG⟩ := hN (N + 1) (Nat.le_add_right N 1)
  obtain ⟨s, _, hs⟩ := Finset.lt_sup_iff.mp (hG x).2.1
  exact ⟨N + 1, Nat.zero_lt_succ N, s, hs⟩

/-- The factor genuinely produced from actual native frames is UNIQUE across ALL original degrees and sections. -/
theorem existsUnique_weightedLaurentPowerSectionNorm_powerFactor :
    ∃! c : ℝ≥0, 0 < c ∧ ∀ n : ℕ, ∀ s : Γ(bundleTensorPower M n, ⊤),
      C.gaussPowerSectionNorm M hM r hr hru x n s =
        c ^ n * C.weightedLaurentPowerSectionNorm M L α e₁ hAmp.1 r x n s := by
  obtain ⟨c, hc, hs⟩ := C.exists_weightedLaurentPowerSectionNorm_powerFactor M hM r hr hru x L α e₁ hAmp.1
  refine ⟨c, ⟨hc, hs⟩, ?_⟩
  intro d hd
  obtain ⟨n, hn, s, hp⟩ := C.exists_positive_gaussPowerSectionNorm M hM L hAmp α e₁ r hr hru x
  have hw : C.weightedLaurentPowerSectionNorm M L α e₁ hAmp.1 r x n s ≠ 0 := by
    intro hz
    have h := hs n s
    rw [hz, mul_zero] at h
    exact hp.ne' h
  have hpow : d ^ n = c ^ n := mul_right_cancel₀ hw ((hd.2 n s).symm.trans (hs n s))
  exact (pow_left_inj₀ hd.1.le hc.le hn.ne').mp hpow

/-- ANY actual original proper-center open/frame choices give the SAME positive actual native factor. -/
theorem gaussCompatibleNormFactor_eq_of_frames [IsProper X.hom]
    (U V : X.left.Opens)
    (hcU : center Valuation.one_apply_le_one x ∈ U) (hcV : center Valuation.one_apply_le_one x ∈ V)
    (hyU : (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (hyV : (C.productGaussSource x r hr).1.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ V)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme) (eV : (pullback V.ι).obj L ≅ unitObj V.toScheme) :
    C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hyU eU =
      C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ V hyV eV := by
  obtain ⟨c, _, hu⟩ := C.existsUnique_weightedLaurentPowerSectionNorm_powerFactor M hM L hAmp α e₁ r hr hru x
  have hU := hu (C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hyU eU)
    ⟨C.gaussCompatibleNormFactor_pos M hM r hr hru x L α e₁ U hyU eU,
      fun n s => C.gaussPowerSectionNorm_eq_compatibleFactor M hM r hr hru x L α e₁ U eU hAmp.1 hcU n s⟩
  have hV := hu (C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ V hyV eV)
    ⟨C.gaussCompatibleNormFactor_pos M hM r hr hru x L α e₁ V hyV eV,
      fun n s => C.gaussPowerSectionNorm_eq_compatibleFactor M hM r hr hru x L α e₁ V eV hAmp.1 hcV n s⟩
  exact hU.trans hV.symm

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
