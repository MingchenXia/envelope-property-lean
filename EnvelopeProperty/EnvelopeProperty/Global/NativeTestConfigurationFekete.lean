import EnvelopeProperty.Global.NativeTestConfigurationBaseIdealNorms
import EnvelopeProperty.Algebra.TailSubadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Genuine Fekete limits of original all-section base-ideal norms -/
open AlgebraicGeometry CategoryTheory Set Filter Topology Scheme.Modules
open scoped NNReal ENNReal
noncomputable section
universe u

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]

/-- Whole original ideal-sheaf inclusion preserves the actual intrinsic norm. -/
theorem modelIdealNorm_mono {I J : X.IdealSheafData} (hIJ : I ≤ J)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm I hb y ≤ modelIdealNorm J hb y := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := center hb y) trivial
  rw [modelIdealNorm_eq_affine I hb y ⟨U, hU⟩ hy,
    modelIdealNorm_eq_affine J hb y ⟨U, hU⟩ hy]
  exact Spectrum.idealNorm_mono (hIJ ⟨U, hU⟩) _

/-- Actual extended-real ideal logarithms preserve whole original inclusion. -/
theorem modelIdealLog_mono {I J : X.IdealSheafData} (hIJ : I ≤ J)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealLog I hb y ≤ modelIdealLog J hb y :=
  ENNReal.log_monotone (modelIdealNorm_mono hIJ hb y)

/-- The actual all-global-section base-ideal norms are supermultiplicative. -/
theorem powerBaseIdeal_norm_mul_le {M : X.Modules} (hM : IsInvertible M)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (m n : ℕ) :
    modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y *
      modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM n) hb y ≤
      modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM (m + n)) hb y := by
  rw [← modelIdealNorm_mul]
  exact modelIdealNorm_mono
    (TensorPowerBaseIdealGrading.powerBaseIdeal_mul_le hM m n) hb y

/-- Real negative logarithm of the entire actual base ideal; early zero values
use the real logarithm convention and do not affect the eventual limit. -/
def powerBaseIdealNegativeLog {M : X.Modules} (hM : IsInvertible M)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (m : ℕ) : ℝ :=
  -Real.log (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y).toReal

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules) (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L)

include L hAmp α e₁

/-- Original source ampleness derives ONE tail and the genuine finite Fekete
limit at EVERY actual point, without any supplied positivity or limit input. -/
theorem exists_powerBaseIdeal_fekete_limit {v : Valuation (Polynomial k) ℝ≥0}
    (hb : ∀ r, v r ≤ 1) (ht : v Polynomial.X ≠ 0) :
    have : IsProper C.projection := C.projection_isProper
    ∃ N : ℕ, ∀ y : RelativeSchemeValuedPoint v C.projection,
      0 ≤ TailSubadditive.limit (powerBaseIdealNegativeLog hM hb y) N ∧
      Tendsto (fun m : ℕ => powerBaseIdealNegativeLog hM hb y m / m) atTop
        (𝓝 (TailSubadditive.limit (powerBaseIdealNegativeLog hM hb y) N)) := by
  let : IsProper C.projection := C.projection_isProper
  obtain ⟨N, hN⟩ := C.exists_eventual_powerBaseIdeal_norm_pos M hM L hAmp α e₁ hb ht
  refine ⟨N, fun y => ?_⟩
  have hfinite (m : ℕ) :
      modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (modelIdealNorm_le_one _ hb y)
  have hpos (m : ℕ) (hm : N ≤ m) :
      0 < (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y).toReal :=
    ENNReal.toReal_pos (hN m hm y).ne' (hfinite m)
  apply TailSubadditive.tendsto_limit
  · intro m n hm hn
    have hnorm := ENNReal.toReal_mono (hfinite (m + n))
      (powerBaseIdeal_norm_mul_le hM hb y m n)
    rw [ENNReal.toReal_mul] at hnorm
    have hlog := Real.log_le_log (mul_pos (hpos m hm) (hpos n hn)) hnorm
    rw [Real.log_mul (hpos m hm).ne' (hpos n hn).ne'] at hlog
    dsimp [powerBaseIdealNegativeLog]
    linarith
  · intro m _
    apply neg_nonneg.mpr
    apply Real.log_nonpos ENNReal.toReal_nonneg
    exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top
      (modelIdealNorm_le_one (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y)

/-- The original ideal norms have an actual positive finite normalized-root
limit, derived from original geometry and exponential continuity. -/
theorem exists_powerBaseIdeal_root_limit {v : Valuation (Polynomial k) ℝ≥0}
    (hb : ∀ r, v r ≤ 1) (ht : v Polynomial.X ≠ 0) :
    have : IsProper C.projection := C.projection_isProper
    ∀ y : RelativeSchemeValuedPoint v C.projection, ∃ b : ℝ,
      0 < b ∧ b ≤ 1 ∧ Tendsto (fun m : ℕ =>
        (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y).toReal ^
          (1 / (m : ℝ))) atTop (𝓝 b) := by
  let : IsProper C.projection := C.projection_isProper
  dsimp only
  obtain ⟨N, hN⟩ := C.exists_powerBaseIdeal_fekete_limit M hM L hAmp α e₁ hb ht
  obtain ⟨P, hP⟩ := C.exists_eventual_powerBaseIdeal_norm_pos M hM L hAmp α e₁ hb ht
  intro y
  let a := TailSubadditive.limit (powerBaseIdealNegativeLog hM hb y) N
  refine ⟨Real.exp (-a), Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hN y).1)
  · have he : Tendsto (fun m : ℕ => Real.exp (-(powerBaseIdealNegativeLog hM hb y m / m)))
        atTop (𝓝 (Real.exp (-a))) :=
      (Real.continuous_exp.tendsto (-a)).comp ((hN y).2.neg)
    apply he.congr'
    refine (eventually_atTop.2 ⟨P, fun m hm => ?_⟩)
    have hpos : 0 <
        (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y).toReal :=
      ENNReal.toReal_pos (hP m hm y).ne'
        (ne_top_of_le_ne_top ENNReal.one_ne_top (modelIdealNorm_le_one _ hb y))
    dsimp only
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    dsimp [powerBaseIdealNegativeLog]
    ring

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
