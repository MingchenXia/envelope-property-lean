import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicIdealPowerGeneratorBound
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.MonicRelationWeightedIntegrability

set_option autoImplicit false

/-! # Genuine monic germ integrality produces actual weighted membership -/

open Set Filter MeasureTheory
open scoped Topology

namespace ComplexGeometry.AnalyticGeometry.MonicGermMultiplierIntegrability

open Pluripotential

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Genuine ideal powers in a monic germ relation internally supply coefficient
bounds and a common actual neighborhood for the root's weighted membership. -/
theorem multiplierIntegrableAt_of_monic_germ_relation {φ : E → EReal} {c : ℝ}
    (hc : 0 < c) (hφ : QuasiPlurisubharmonicAt φ 0) {N d : ℕ} (hd : 0 < d)
    (G : Fin N → E → ℂ) (hG : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G j) z)
    (hGint : ∀ j, MultiplierIntegrableAt φ c (G j) 0 μ)
    (F : E → ℂ) (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (b : Fin d → HolGerm E)
    (hb : ∀ i, b i ∈ (Ideal.span (range fun j => HolGerm.mk (G j) (hG j))) ^ (d - i.val))
    (hrel : HolGerm.mk F hF ^ d + ∑ i, b i * HolGerm.mk F hF ^ i.val = 0) :
    MultiplierIntegrableAt φ c F 0 μ := by
  classical
  choose B hB heqB using fun i => HolGerm.exists_eq_mk (b i)
  have hbounds : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 0,
      ‖B i z‖ ≤ C * (∑ j, ‖G j z‖) ^ (d - i.val) := by
    intro i
    apply HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow G hG
      (B i) (hB i) (d - i.val)
    simpa only [← heqB i] using hb i
  choose C hC hbound using hbounds
  let Ctotal : ℝ := ∑ i, C i
  have hCtotal : 0 ≤ Ctotal := Finset.sum_nonneg fun i _ => hC i
  have hCsum : ∀ i, C i ≤ Ctotal := fun i =>
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  let P : E → ℂ := fun z => F z ^ d + ∑ i, B i z * F z ^ i.val
  have hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ P z :=
    eventually_differentiableAt_add (eventually_differentiableAt_pow hF d)
      (eventually_differentiableAt_sum Finset.univ fun i =>
        eventually_differentiableAt_mul (hB i) (eventually_differentiableAt_pow hF i.val))
  have hmk : HolGerm.mk P hP = 0 := by
    calc
      HolGerm.mk P hP = HolGerm.mk F hF ^ d +
          ∑ i, HolGerm.mk (B i) (hB i) * HolGerm.mk F hF ^ i.val := by
        rw [show HolGerm.mk P hP =
            HolGerm.mk (fun z => F z ^ d) (eventually_differentiableAt_pow hF d) +
              HolGerm.mk (fun z => ∑ i, B i z * F z ^ i.val)
                (eventually_differentiableAt_sum Finset.univ fun i =>
                  eventually_differentiableAt_mul (hB i)
                    (eventually_differentiableAt_pow hF i.val)) from
          HolGerm.mk_add _ _ _ _]
        rw [HolGerm.mk_pow F hF d]
        congr 1
        calc
          HolGerm.mk (fun z => ∑ i, B i z * F z ^ i.val) _ =
              ∑ i, HolGerm.mk (fun z => B i z * F z ^ i.val)
                (eventually_differentiableAt_mul (hB i)
                  (eventually_differentiableAt_pow hF i.val)) := by
            simpa using HolGerm.mk_sum Finset.univ (fun i z => B i z * F z ^ i.val)
              (fun i => eventually_differentiableAt_mul (hB i)
                (eventually_differentiableAt_pow hF i.val))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [HolGerm.mk_mul _ _ (hB i) (eventually_differentiableAt_pow hF i.val),
              HolGerm.mk_pow F hF i.val]
      _ = 0 := by simpa only [← heqB] using hrel
  have hrelPoint : ∀ᶠ z in 𝓝 0, P z = 0 :=
    HolGerm.mk_eq_mk_iff.mp (hmk.trans HolGerm.mk_zero.symm)
  obtain ⟨Q, hQ, h0Q, hφQ⟩ := IEquivalentMax.exists_open_quasiPlurisubharmonicOn_of_at hφ
  choose U hU h0U hholU hintU using fun j => (hGint j).2
  have hallU : ∀ᶠ z in 𝓝 0, ∀ j, z ∈ U j :=
    Filter.eventually_all.mpr fun j => (hU j).mem_nhds (h0U j)
  have hallBounds : ∀ᶠ z in 𝓝 0, ∀ i,
      ‖B i z‖ ≤ Ctotal * (∑ j, ‖G j z‖) ^ (d - i.val) := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [hbound i] with z hz
    exact hz.trans (mul_le_mul_of_nonneg_right (hCsum i) (by positivity))
  have hQevent : ∀ᶠ z in 𝓝 0, z ∈ Q := hQ.mem_nhds h0Q
  obtain ⟨O, hOsub, hO, h0O⟩ := mem_nhds_iff.mp
    (hF.and (hQevent.and (hallU.and (hallBounds.and hrelPoint))))
  have hFOn : DifferentiableOn ℂ F O :=
    fun z hz => (hOsub hz).1.differentiableWithinAt
  refine ⟨hc, O, hO, h0O, hFOn, ?_⟩
  exact MonicRelationWeightedIntegrability.weightedL2On_of_monic_relation hc hO
    (hφQ.mono fun _ hz => (hOsub hz).2.1) hFOn hd G B hCtotal
    (fun j => (hintU j).mono fun _ hz => (hOsub hz).2.2.1 j)
    (fun z hz => (hOsub hz).2.2.2.1)
    (fun z hz => (hOsub hz).2.2.2.2)

end
end ComplexGeometry.AnalyticGeometry.MonicGermMultiplierIntegrability
