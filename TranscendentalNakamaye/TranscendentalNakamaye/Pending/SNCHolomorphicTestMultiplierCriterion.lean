import TranscendentalNakamaye.Pending.SNCHolomorphicTestNecessity
import TranscendentalNakamaye.Pending.MultiplierHaarLinearTransport

set_option autoImplicit false

/-! # Exact SNC thresholds for arbitrary holomorphic tests

The actual coordinate isometry, Haar measure transport and local-germ ring
isomorphism extend the last-coordinate necessity to every coordinate.
Internally extracted orders are fixed before all multiplier levels; extra test
zeros and a residual factor vanishing at the center are allowed.
Reference: Demailly, *Analytic Methods in Algebraic Geometry*, multiplier
integrability, and *Complex Analytic and Differential Geometry*, local germs.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace TranscendentalNakamaye.Pending.SNCHolomorphicTestMultiplierCriterion

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

/-- Every coordinate threshold follows from the literal finite multiplier germ;
the residual factor need not be a unit at zero. -/
theorem thresholds_of_multiplier_integrable {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ)
    {F H : ComplexModel n → ℂ} {ρ : ComplexModel n → ℝ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (hnot : ∀ j : Fin n, ¬HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin n, z j ^ a j)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z)
    {c : ℝ}
    (hint : MultiplierIntegrableAt (fun z : ComplexModel n =>
      (∑ j, ((2 * b j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal))
      c F 0 volume) :
    ∀ j : Fin n, c * b j < (a j : ℝ) + 1 := by
  classical
  cases n with
  | zero => exact fun j => Fin.elim0 j
  | succ m =>
    intro j
    let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
    let L : ComplexModel (m + 1) ≃L[ℂ] ComplexModel (m + 1) :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv
    have hL (z : ComplexModel (m + 1)) (i : Fin (m + 1)) : (L z) i = z (e.symm i) := rfl
    have hLj (z : ComplexModel (m + 1)) : (L z) j = z (Fin.last m) := by
      rw [hL]
      simp [e]
    have hT : Tendsto L (𝓝 (0 : ComplexModel (m + 1))) (𝓝 0) :=
      HolGerm.tendsto_clm_nhds_zero (L : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1))
    have hH' : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (H ∘ L) z :=
      eventually_differentiableAt_comp_clm (L : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1)) hH
    have hnot' : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk (H ∘ L) hH' := by
      have hcoord : HolGerm.comapEquiv L
          (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
            (eventually_differentiableAt_coordinate j)) =
          HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
            (eventually_differentiableAt_coordinate (Fin.last m)) := by
        rw [HolGerm.comapEquiv_mk]
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Eventually.of_forall fun z => hLj z
      intro hdiv
      apply hnot j
      apply (map_dvd_iff (HolGerm.comapEquiv L)).mp
      rw [hcoord, HolGerm.comapEquiv_mk]
      exact hdiv
    let a' : Fin (m + 1) → ℕ := fun i => a (e i)
    let b' : Fin (m + 1) → ℝ := fun i => b (e i)
    have hprod (z : ComplexModel (m + 1)) :
        (∏ i : Fin (m + 1), (L z) i ^ a i) = ∏ i : Fin (m + 1), z i ^ a' i := by
      simp only [hL, a']
      exact Fintype.prod_equiv e.symm _ _ fun i => by simp only [e.apply_symm_apply]
    have heq' : (F ∘ L) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
        fun z => (H ∘ L) z * ∏ i : Fin (m + 1), z i ^ a' i := by
      filter_upwards [hT.eventually heq] with z hz
      exact hz.trans (congrArg (fun w : ℂ => H (L z) * w) (hprod z))
    have hρ' : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ContinuousAt (ρ ∘ L) z := by
      filter_upwards [hT.eventually hρ] with z hz
      exact hz.comp L.continuous.continuousAt
    have hweight : (fun z : ComplexModel (m + 1) =>
        (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal)) ∘ L =
        (fun z : ComplexModel (m + 1) =>
          (∑ i, ((2 * b' i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + ((ρ ∘ L) z : EReal)) := by
      funext z
      simp only [Function.comp_apply, hL, b']
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun i => by simp only [e.apply_symm_apply]
    have hint' := (MultiplierHaarLinearTransport.multiplierIntegrableAt_continuousLinearEquiv_iff
      volume volume L (x := (0 : ComplexModel (m + 1)))).mpr
        (by simpa only [L.map_zero] using hint)
    rw [hweight] at hint'
    have hlast := SNCHolomorphicTestNecessity.last_threshold_of_multiplier_integrable
      a' b' hH' hnot' heq' hρ' hint'
    simpa only [a', b', e, Equiv.swap_apply_right] using hlast

/-- All actual orders and the nonzero holomorphic residual are internally
chosen before every positive multiplier level, with no test zero-locus premise. -/
theorem exists_coordinate_orders_multiplier_iff {n : ℕ}
    (b : Fin n → ℝ) {F : ComplexModel n → ℂ} {ρ : ComplexModel n → ℝ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z) :
    ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ)
      (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z),
      (∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0) ∧
      F =ᶠ[𝓝 0] (fun z => H z * ∏ j : Fin n, z j ^ a j) ∧
      (∀ j : Fin n, ¬HolGerm.mk (fun z : ComplexModel n => z j)
        (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) ∧
      ∀ c : ℝ, 0 < c →
        (MultiplierIntegrableAt (fun z : ComplexModel n =>
          (∑ j, ((2 * b j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal))
          c F 0 volume ↔ ∀ j : Fin n, c * b j < (a j : ℝ) + 1) := by
  obtain ⟨a, H, hH, hHnon, heq, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
  refine ⟨a, H, hH, hHnon, heq, hnot, ?_⟩
  intro c hc
  exact ⟨thresholds_of_multiplier_integrable a b hH hnot heq hρ,
    HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
      a b hc hH heq hρ⟩

end
end TranscendentalNakamaye.Pending.SNCHolomorphicTestMultiplierCriterion
