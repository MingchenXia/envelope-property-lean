/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.MultiplierPowerRescaling
import EnvelopeProperty.TestIdeal.PBasisTest

/-!
# Genuine asymptotic multiplier ideals of the original graded ideal sequence

The original sequence and every full all-divisorial-DVR contribution are
retained. Divisibility-directed stabilization is derived from actual
Noetherianity, not supplied as an asymptotic-ideal property.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable (C : Subalgebra k K) [IsFractionRing C K]

/-- The genuine full asymptotic multiplier ideal of the original nonzero sequence. -/
def asymptoticMultiplierIdeal (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) : Ideal C :=
  ⨆ (q : ℕ) (hq : 0 < q), valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q)

/-- Every genuine constituent ideal belongs to the full asymptotic ideal. -/
theorem valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) {q : ℕ} (hq : 0 < q) :
    valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q) ≤ asymptoticMultiplierIdeal C J hne m :=
  le_iSup₂ (f := fun (q : ℕ) (hq : 0 < q) =>
    valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q)) q hq

/-- The actual full multiplier ideals of an original graded ideal sequence
increase under divisibility of the original sequence index. -/
theorem valuativeMultiplierIdeal_le_of_dvd
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hdvd : q ∣ q') :
    valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q) ≤
      valuativeMultiplierIdeal C (J q') (hne q' hq') ((m : ℚ) / q') := by
  obtain ⟨r, rfl⟩ := hdvd
  have hr : 0 < r := Nat.pos_of_mul_pos_left hq'
  have hc : (0 : ℚ) ≤ (m : ℚ) / (q * r : ℕ) := by positivity
  have heq : (m : ℚ) / q = (r : ℚ) * ((m : ℚ) / (q * r : ℕ)) := by
    push_cast
    field_simp
  rw [heq, ← valuativeMultiplierIdeal_pow C (J q) (hne q hq) r ((m : ℚ) / (q * r : ℕ))]
  apply valuativeMultiplierIdeal_mono_ideal C _ _ _ _ _ _ hc
  simpa only [mul_comm q r] using EnvelopeProperty.Cartier.pow_le_of_mul_le_add hJ q hr

/-- Actual Noetherianity and actual gradedness derive attainment at every
sufficiently divisible original index, not just existence of an abstract maximum. -/
theorem exists_asymptoticMultiplierIdeal_eq [IsNoetherianRing C]
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ q₀, 0 < q₀ ∧ ∀ q (hq : 0 < q), q₀ ∣ q →
      asymptoticMultiplierIdeal C J hne m =
        valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q) := by
  let F : ℕ → Ideal C := fun q =>
    ⨆ hq : 0 < q, valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q)
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2
    (inferInstance : IsNoetherianRing C) {I | ∃ q, 0 < q ∧ F q = I} ⟨F 1, 1, one_pos, rfl⟩
  have hF (q : ℕ) (hq : 0 < q) : F q =
      valuativeMultiplierIdeal C (J q) (hne q hq) ((m : ℚ) / q) := by
    simp only [F, iSup_pos hq]
  have hle : ∀ q, 0 < q → F q ≤ F q₀ := by
    intro q hq
    have hqq : 0 < q * q₀ := Nat.mul_pos hq hq₀
    have h1 : F q ≤ F (q * q₀) := by
      rw [hF q hq, hF (q * q₀) hqq]
      exact valuativeMultiplierIdeal_le_of_dvd C hJ hne m hq hqq (dvd_mul_right q q₀)
    have h2 : F q₀ ≤ F (q * q₀) := by
      rw [hF q₀ hq₀, hF (q * q₀) hqq]
      exact valuativeMultiplierIdeal_le_of_dvd C hJ hne m hq₀ hqq (dvd_mul_left q₀ q)
    have h3 : F q₀ = F (q * q₀) := by
      by_contra hne'
      exact hmax _ ⟨q * q₀, hqq, rfl⟩ (lt_of_le_of_ne h2 hne')
    rw [h3]
    exact h1
  have hB : asymptoticMultiplierIdeal C J hne m = F q₀ := by
    apply le_antisymm
    · apply iSup₂_le
      intro q hq
      rw [← hF q hq]
      exact hle q hq
    · rw [hF q₀ hq₀]
      exact valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal C J hne m hq₀
  refine ⟨q₀, hq₀, fun q hq hdvd => le_antisymm ?_ ?_⟩
  · rw [hB, hF q₀ hq₀]
    exact valuativeMultiplierIdeal_le_of_dvd C hJ hne m hq₀ hq hdvd
  · exact valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal C J hne m hq

/-- The original positive-degree ideal lies in its actual asymptotic multiplier ideal. -/
theorem le_asymptoticMultiplierIdeal
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) {m : ℕ} (hm : 0 < m) :
    J m ≤ asymptoticMultiplierIdeal C J hne m := by
  refine le_trans ?_ (valuativeMultiplierIdeal_le_asymptoticMultiplierIdeal C J hne m hm)
  rw [div_self (Nat.cast_ne_zero.mpr hm.ne')]
  exact le_valuativeMultiplierIdeal_one C (J m) (hne m hm)

/-- The genuine asymptotic multiplier ideal remains nonzero at every positive degree. -/
theorem asymptoticMultiplierIdeal_ne_bot
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) {m : ℕ} (hm : 0 < m) :
    asymptoticMultiplierIdeal C J hne m ≠ ⊥ := by
  intro hbot
  apply hne m hm
  exact le_bot_iff.mp (hbot ▸ le_asymptoticMultiplierIdeal C J hne hm)

end EnvelopeProperty.Char0
