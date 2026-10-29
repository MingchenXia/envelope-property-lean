import EnvelopeProperty.Global.NativeTestConfigurationWeightedSectionNorms
import EnvelopeProperty.AlgGeom.NativeLineFubiniStudyNonvanishing
import EnvelopeProperty.Local.FiniteFlatNorm

/-! # Genuine whole original weighted FS data from total-space Laurent coefficients -/
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
open SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X)
    (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (hL : IsInvertible L)

/-- Actual whole original FS data, with original line L and degree/denominator n. -/
def weightedFSData (n : ℕ) (hn : 0 < n)
    (G : Finset Γ(bundleTensorPower M n, ⊤)) (r : ℝ≥0) :
    NativeLineFubiniStudy.FSData L 1 where
  m := n
  m_pos := hn
  deg := n
  deg_eq := by simp
  terms := (C.globalPowerLaurentTerms M L α e₁ hL n G).image fun t =>
    (t.1, (t.2 : ℝ) * Real.log (r : ℝ))

/-- The actual native pullback-unit norm is the SAME original whole section-morphism norm. -/
theorem originalPowerSectionNorm_eq_globalSectionNorm
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (n : ℕ) (s : Γ(bundleTensorPower L n, ⊤)) :
    letI : IsProper X.hom := C.original_isProper
    C.originalPowerSectionNorm L hL x n s =
      globalSectionNorm Valuation.one_apply_le_one x (bundleTensorPower L n)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s := by
  let : IsProper X.hom := C.original_isProper
  exact congrArg (modelLineNorm Valuation.one_apply_le_one x
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n))
    (SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
      (X.left.fromSpecResidueField x.1.point) (bundleTensorPower L n) s)

/-- Entire actual FS evaluation equals the normalized logarithm of the actual original weighted maximum. -/
theorem weightedFSData_eval (n : ℕ) (hn : 0 < n)
    (G : Finset Γ(bundleTensorPower M n, ⊤)) (r : ℝ≥0) (hr : 0 < r)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    letI : IsProper X.hom := C.original_isProper
    (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x =
      (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
        (((C.globalPowerLaurentTerms M L α e₁ hL n G).sup
          (fun t => C.originalPowerSectionNorm L hL x n t.1 * r ^ t.2) : ℝ≥0) : ℝ≥0∞) := by
  let : IsProper X.hom := C.original_isProper
  change (((n : ℝ)⁻¹ : ℝ) : EReal) *
    ((C.globalPowerLaurentTerms M L α e₁ hL n G).image
      (fun t => (t.1, (t.2 : ℝ) * Real.log (r : ℝ)))).sup
        (fun q => ENNReal.log (globalSectionNorm Valuation.one_apply_le_one x
          (bundleTensorPower L n) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
          q.1 : ℝ≥0∞) + (q.2 : EReal)) = _
  rw [Finset.sup_image, log_coe_nnreal_finsetSup]
  congr 1
  apply Finset.sup_congr rfl
  intro t ht
  rw [ENNReal.coe_mul, ENNReal.log_mul_add,
    C.originalPowerSectionNorm_eq_globalSectionNorm L hL x n t.1,
    ENNReal.log_of_nnreal (zpow_ne_zero _ hr.ne'), NNReal.coe_zpow, Real.log_zpow]
  rfl

/-- ONE derived real additive factor works for ALL actual original finite section families. -/
theorem exists_weightedFSData_totalLog_factor
    (n : ℕ) (hn : 0 < n) (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    letI : IsProper X.hom := C.original_isProper
    ∃ a : ℝ, ∀ G : Finset Γ(bundleTensorPower M n, ⊤),
      (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
        ((G.sup (fun s => C.gaussPowerSectionNorm M hM r hr hru x n s) : ℝ≥0) : ℝ≥0∞) =
          (a : EReal) + (C.weightedFSData M L α e₁ hL n hn G r).eval X.hom hL x := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨c, hc, hG⟩ :=
    C.exists_weightedLaurentPowerFamilyNorm_factor M hM L α e₁ hL r hr hru x n
  refine ⟨(n : ℝ)⁻¹ * Real.log (c : ℝ), fun G => ?_⟩
  rw [hG G, ENNReal.coe_mul, ENNReal.log_mul_add,
    ENNReal.log_of_nnreal hc.ne',
    ProjBerk.ereal_coe_mul_add (by positivity), ← EReal.coe_mul,
    C.weightedFSData_eval M L α e₁ hL n hn G r hr x]

include hM in
/-- Actual ampleness derives one original finite family per eventual degree with NO common native zero. -/
theorem exists_eventual_weightedFSData_noCommonZero
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1) :
    letI : IsProper X.hom := C.original_isProper
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
      ∃ G : Finset Γ(bundleTensorPower M n, ⊤),
        ∀ x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom,
          ∃ q ∈ (C.weightedFSData M L α e₁ hL n hn G r).terms,
            globalSectionNorm Valuation.one_apply_le_one x (bundleTensorPower L n)
              (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) q.1 ≠ 0 := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨N, hN⟩ := C.exists_eventual_finite_gauss_power_section_norms M hM L hAmp α e₁ r hr hru
  refine ⟨N, fun n hn hnpos => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  refine ⟨G, fun x => ?_⟩
  obtain ⟨c, hc, he⟩ :=
    C.exists_weightedLaurentPowerFamilyNorm_factor M hM L α e₁ hL r hr hru x n
  have hNZ : ∃ t ∈ C.globalPowerLaurentTerms M L α e₁ hL n G,
      C.originalPowerSectionNorm L hL x n t.1 ≠ 0 := by
    by_contra h
    have hz : (C.globalPowerLaurentTerms M L α e₁ hL n G).sup
        (fun t => C.originalPowerSectionNorm L hL x n t.1 * r ^ t.2) = 0 := by
      change _ = ⊥
      rw [Finset.sup_eq_bot_iff]
      intro t ht
      have ht0 : C.originalPowerSectionNorm L hL x n t.1 = 0 := by
        by_contra hh
        exact h ⟨t, ht, hh⟩
      rw [ht0, zero_mul]
      rfl
    have heG := he G
    rw [hz, mul_zero] at heG
    exact (hG x).2.1.ne' heG
  obtain ⟨t, ht, htNZ⟩ := hNZ
  refine ⟨(t.1, (t.2 : ℝ) * Real.log (r : ℝ)), Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  exact (C.originalPowerSectionNorm_eq_globalSectionNorm L hL x n t.1) ▸ htNZ

/-- The genuine fixed exponential radius used for actual rational Laurent weights. -/
def weightedFSRadius : ℝ≥0 := ⟨Real.exp (-1), (Real.exp_pos _).le⟩

/-- Its positivity, polynomial boundedness and exact real logarithm are internally derived. -/
theorem weightedFSRadius_properties :
    0 < weightedFSRadius ∧ weightedFSRadius ≤ 1 ∧ Real.log (weightedFSRadius : ℝ) = -1 := by
  refine ⟨Real.exp_pos _, ?_, Real.log_exp _⟩
  change Real.exp (-1) ≤ (1 : ℝ)
  exact Real.exp_le_one_iff.mpr (by norm_num)

/-- Every actual original integer exponent gives a rational weight at the fixed exponential radius. -/
theorem weightedFSData_isRational (n : ℕ) (hn : 0 < n)
    (G : Finset Γ(bundleTensorPower M n, ⊤)) :
    (C.weightedFSData M L α e₁ hL n hn G weightedFSRadius).IsRational := by
  intro q hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  refine ⟨-(t.2 : ℚ), ?_⟩
  change (t.2 : ℝ) * Real.log (Real.exp (-1)) = ((-(t.2 : ℚ) : ℚ) : ℝ)
  simp

include hM in
/-- Original ampleness produces genuine finite rational FS functions of the SAME original line/class. -/
theorem exists_eventual_weightedFSData_isFinFS
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) :
    letI : IsProper X.hom := C.original_isProper
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
      ∃ G : Finset Γ(bundleTensorPower M n, ⊤),
        NativeLineFubiniStudy.IsFinFS X.hom L hL 1
          (fun x => (C.weightedFSData M L α e₁ hL n hn G weightedFSRadius).eval X.hom hL x) := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨N, hN⟩ := C.exists_eventual_weightedFSData_noCommonZero M hM L α e₁ hL hAmp
    weightedFSRadius weightedFSRadius_properties.1 weightedFSRadius_properties.2.1
  refine ⟨N, fun n hn hnpos => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn hnpos
  exact ⟨G, C.weightedFSData M L α e₁ hL n hnpos G weightedFSRadius,
    C.weightedFSData_isRational M L α e₁ hL n hnpos G, hG, fun _ => rfl⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
