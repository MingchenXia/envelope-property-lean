import EnvelopeProperty.Global.NativeTestConfigurationFekete

/-! # All positive exponents in the actual normalized base-ideal norm supremum -/
open AlgebraicGeometry CategoryTheory Scheme.Modules Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
universe u

namespace EnvelopeProperty.TensorPowerBaseIdealGrading

/-- The ENTIRE original base ideal at one degree has every positive power
contained in the actual all-section base ideal at the corresponding multiple. -/
theorem powerBaseIdeal_pow_succ_le {X : Scheme.{u}} {M : X.Modules}
    (hM : IsInvertible M) (m k : ℕ) :
    powerBaseIdeal hM m ^ (k + 1) ≤ powerBaseIdeal hM ((k + 1) * m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      powerBaseIdeal hM m ^ (k + 1 + 1) =
          powerBaseIdeal hM m ^ (k + 1) * powerBaseIdeal hM m := pow_succ _ _
      _ ≤ powerBaseIdeal hM ((k + 1) * m) * powerBaseIdeal hM m :=
        mul_le_mul' ih le_rfl
      _ ≤ powerBaseIdeal hM ((k + 1) * m + m) := powerBaseIdeal_mul_le _ _ _
      _ = powerBaseIdeal hM ((k + 1 + 1) * m) := by congr 1; ring

end EnvelopeProperty.TensorPowerBaseIdealGrading

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]

/-- The normalized root of the actual ENTIRE all-global-section base ideal. -/
def powerBaseIdealNormalizedRoot {M : X.Modules} (hM : IsInvertible M)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (m : ℕ) : ℝ :=
  (modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y).toReal ^
    (1 / (m : ℝ))

/-- Each actual original positive-degree root is below every root at its
positive multiples, including the case where the original ideal norm is zero. -/
theorem powerBaseIdealNormalizedRoot_le_multiple {M : X.Modules} (hM : IsInvertible M)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (m : ℕ) (hm : 0 < m) (k : ℕ) :
    powerBaseIdealNormalizedRoot hM hb y m ≤
      powerBaseIdealNormalizedRoot hM hb y ((k + 1) * m) := by
  have hnorm := modelIdealNorm_mono
    (TensorPowerBaseIdealGrading.powerBaseIdeal_pow_succ_le hM m k) hb y
  rw [modelIdealNorm_pow] at hnorm
  have hreal := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (modelIdealNorm_le_one _ hb y)) hnorm
  rw [ENNReal.toReal_pow] at hreal
  have hroot := Real.rpow_le_rpow (pow_nonneg ENNReal.toReal_nonneg (k + 1)) hreal
    (show 0 ≤ 1 / (((k + 1) * m : ℕ) : ℝ) by positivity)
  rw [← Real.rpow_natCast_mul ENNReal.toReal_nonneg] at hroot
  have he : ((k + 1 : ℕ) : ℝ) * (1 / (((k + 1) * m : ℕ) : ℝ)) = 1 / (m : ℝ) := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  simpa only [he, powerBaseIdealNormalizedRoot] using hroot

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules) (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L)

include L hAmp α e₁

/-- Original source ampleness yields the actual least upper bound of EVERY
positive exponent, together with full genuine normalized-root convergence. -/
theorem exists_powerBaseIdeal_normalized_supremum {v : Valuation (Polynomial k) ℝ≥0}
    (hb : ∀ r, v r ≤ 1) (ht : v Polynomial.X ≠ 0) :
    have : IsProper C.projection := C.projection_isProper
    ∀ y : RelativeSchemeValuedPoint v C.projection, ∃ b : ℝ,
      0 < b ∧ b ≤ 1 ∧
      Tendsto (powerBaseIdealNormalizedRoot hM hb y) atTop (𝓝 b) ∧
      IsLUB {q : ℝ | ∃ m : ℕ, 0 < m ∧ q = powerBaseIdealNormalizedRoot hM hb y m} b := by
  let : IsProper C.projection := C.projection_isProper
  dsimp only
  intro y
  obtain ⟨b, hbpos, hbone, hlim⟩ := C.exists_powerBaseIdeal_root_limit M hM L hAmp α e₁ hb ht y
  change Tendsto (powerBaseIdealNormalizedRoot hM hb y) atTop (𝓝 b) at hlim
  refine ⟨b, hbpos, hbone, hlim, ?_, ?_⟩
  · rintro q ⟨m, hm, rfl⟩
    have hcofinal : Tendsto (fun a : ℕ => (a + 1) * m) atTop atTop :=
      tendsto_atTop_mono (fun a =>
        (Nat.le_succ a).trans (Nat.le_mul_of_pos_right (a + 1) hm)) tendsto_id
    exact ge_of_tendsto' (hlim.comp hcofinal)
      (fun a => powerBaseIdealNormalizedRoot_le_multiple hM hb y m hm a)
  · intro c hc
    apply le_of_tendsto hlim
    refine eventually_atTop.2 ⟨1, fun m hm => ?_⟩
    exact hc ⟨m, hm, rfl⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
