import TranscendentalNakamaye.Pending.HolomorphicGermRing
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false

/-! # Natural ideal powers produce actual finite-generator growth bounds -/

open Filter Topology

namespace TranscendentalNakamaye.Pending.HolomorphicIdealPowerGeneratorBound

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def growthIdeal (S : E → ℝ) (k : ℕ) : Ideal (HolGerm E) where
  carrier := {g | ∃ (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (C : ℝ), 0 ≤ C ∧ HolGerm.mk f hf = g ∧ ∀ᶠ z in 𝓝 0, ‖f z‖ ≤ C * S z ^ k}
  zero_mem' := by
    refine ⟨0, eventually_differentiableAt_zero, 0, le_rfl, HolGerm.mk_zero, ?_⟩
    exact Eventually.of_forall fun _ => by simp
  add_mem' := by
    rintro _ _ ⟨f, hf, C, hC, rfl, hb⟩ ⟨g, hg, D, hD, rfl, hd⟩
    refine ⟨fun z => f z + g z, eventually_differentiableAt_add hf hg, C + D,
      add_nonneg hC hD, HolGerm.mk_add _ _ _ _, ?_⟩
    filter_upwards [hb, hd] with z hz hz'
    calc
      ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
      _ ≤ C * S z ^ k + D * S z ^ k := add_le_add hz hz'
      _ = (C + D) * S z ^ k := (add_mul _ _ _).symm
  smul_mem' := by
    intro a g hg
    obtain ⟨f, hf, C, hC, rfl, hb⟩ := hg
    obtain ⟨u, hu, rfl⟩ := HolGerm.exists_eq_mk a
    let A : ℝ := ‖u 0‖ + 1
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have huB : ∀ᶠ z in 𝓝 0, ‖u z‖ ≤ A :=
      ((continuousAt_zero_of_eventually_differentiableAt hu).norm.eventually_lt
        continuousAt_const (by dsimp [A]; linarith)).mono fun _ h => h.le
    refine ⟨fun z => u z * f z, eventually_differentiableAt_mul hu hf, A * C,
      mul_nonneg hA hC, ?_, ?_⟩
    · simpa only [smul_eq_mul] using HolGerm.mk_mul u f hu hf
    · filter_upwards [huB, hb] with z hz hfz
      calc
        ‖u z * f z‖ = ‖u z‖ * ‖f z‖ := norm_mul _ _
        _ ≤ A * (C * S z ^ k) := mul_le_mul hz hfz (norm_nonneg _) hA
        _ = (A * C) * S z ^ k := (mul_assoc _ _ _).symm

private theorem growthIdeal_zero (S : E → ℝ) :
    growthIdeal S 0 = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  have hB : ∀ᶠ z in 𝓝 0, ‖f z‖ ≤ ‖f 0‖ + 1 :=
    ((continuousAt_zero_of_eventually_differentiableAt hf).norm.eventually_lt
      continuousAt_const (by linarith)).mono fun _ h => h.le
  refine ⟨f, hf, ‖f 0‖ + 1, by positivity, rfl, ?_⟩
  simpa using hB

private theorem growthIdeal_mul_le (S : E → ℝ) (hs : ∀ z, 0 ≤ S z) (k l : ℕ) :
    growthIdeal S k * growthIdeal S l ≤ growthIdeal S (k + l) := by
  rw [Ideal.mul_le]
  rintro _ ⟨f, hf, C, hC, rfl, hb⟩ _ ⟨g, hg, D, hD, rfl, hd⟩
  refine ⟨fun z => f z * g z, eventually_differentiableAt_mul hf hg, C * D,
    mul_nonneg hC hD, HolGerm.mk_mul _ _ _ _, ?_⟩
  filter_upwards [hb, hd] with z hz hz'
  calc
    ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C * S z ^ k) * (D * S z ^ l) :=
      mul_le_mul hz hz' (norm_nonneg _) (mul_nonneg hC (pow_nonneg (hs z) _))
    _ = (C * D) * S z ^ (k + l) := by rw [pow_add]; ring

/-- Actual ideal-power membership internally supplies a neighborhood bound in
terms of the literal original finite generator family. -/
theorem exists_norm_bound_of_mem_span_pow {N : ℕ} (G : Fin N → E → ℂ)
    (hG : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G j) z) (F : E → ℂ)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (k : ℕ)
    (hmem : HolGerm.mk F hF ∈ (Ideal.span (Set.range fun j => HolGerm.mk (G j) (hG j))) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 0, ‖F z‖ ≤ C * (∑ j, ‖G j z‖) ^ k := by
  classical
  let S : E → ℝ := fun z => ∑ j, ‖G j z‖
  have hs : ∀ z, 0 ≤ S z := fun z => Finset.sum_nonneg fun _ _ => norm_nonneg _
  let I : Ideal (HolGerm E) := Ideal.span (Set.range fun j => HolGerm.mk (G j) (hG j))
  have hI : I ≤ growthIdeal S 1 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨G j, hG j, 1, by positivity, rfl, Eventually.of_forall fun z => ?_⟩
    simpa [S] using Finset.single_le_sum (fun i _ => norm_nonneg (G i z))
      (Finset.mem_univ j)
  have hp : ∀ t : ℕ, I ^ t ≤ growthIdeal S t := by
    intro t
    induction t with
    | zero => simp [growthIdeal_zero]
    | succ t ht =>
      calc
        I ^ (t + 1) = I ^ t * I := pow_succ _ _
        _ ≤ growthIdeal S t * growthIdeal S 1 := Ideal.mul_mono ht hI
        _ ≤ growthIdeal S (t + 1) := growthIdeal_mul_le S hs t 1
  obtain ⟨f, hf, C, hC, heq, hb⟩ := hp k hmem
  have hevent : f =ᶠ[𝓝 0] F := HolGerm.mk_eq_mk_iff.mp heq
  refine ⟨C, hC, ?_⟩
  filter_upwards [hevent, hb] with z hz hbound
  simpa only [← hz] using hbound

end
end TranscendentalNakamaye.Pending.HolomorphicIdealPowerGeneratorBound
