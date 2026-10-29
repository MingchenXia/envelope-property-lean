/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Linarith

open scoped Topology
open Filter Topology
noncomputable section
namespace EnvelopeProperty.FiniteAffineMax
variable {ι δ : Type*}

/-- The actual original indices attaining the true finite maximum of the original intercepts. -/
def active (I : Finset ι) (hI : I.Nonempty) (b : ι → ℝ) : Finset ι := by
  classical
  exact I.filter (fun i => b i = I.sup' hI b)

/-- Actual attainment of the original finite intercept maximum makes its active set nonempty. -/
theorem active_nonempty (I : Finset ι) (hI : I.Nonempty) (b : ι → ℝ) :
    (active I hI b).Nonempty := by
  classical
  obtain ⟨i, hi, hb⟩ := Finset.exists_mem_eq_sup' hI b
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hb.symm⟩⟩

/-- The true finite maximum of the original directional slopes among the actual active indices. -/
def activeSlope (I : Finset ι) (hI : I.Nonempty) (b : ι → ℝ) (s : ι → δ → ℝ) (d : δ) : ℝ :=
  (active I hI b).sup' (active_nonempty I hI b) (fun i => s i d)

/-- A genuine common positive neighborhood has the exact original active affine-max profile. -/
theorem exists_pos_eventual_max (I : Finset ι) (hI : I.Nonempty) (D : Finset δ)
    (b : ι → ℝ) (s : ι → δ → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ D, ∀ t : ℝ, 0 ≤ t → t < ε →
      I.sup' hI (fun i => b i + s i d * t) = I.sup' hI b + activeSlope I hI b s d * t := by
  classical
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_eq_sup' hI b
  have hkA : k ∈ active I hI b := Finset.mem_filter.mpr ⟨hk, hkb.symm⟩
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i ∈ I, ∀ d ∈ D,
      b i ≠ I.sup' hI b → b i + s i d * t < b k + s k d * t := by
    apply (eventually_all_finset I).mpr
    intro i hi
    apply (eventually_all_finset D).mpr
    intro d hd
    by_cases hb : b i = I.sup' hI b
    · exact Eventually.of_forall (fun _ h => (h hb).elim)
    · have hib : b i < I.sup' hI b := lt_of_le_of_ne (Finset.le_sup' b hi) hb
      have hl : Continuous (fun t : ℝ => b i + s i d * t) :=
        continuous_const.add (continuous_const.mul continuous_id)
      have hr : Continuous (fun t : ℝ => b k + s k d * t) :=
        continuous_const.add (continuous_const.mul continuous_id)
      have h0 : b i + s i d * (0 : ℝ) < b k + s k d * (0 : ℝ) := by
        simpa only [mul_zero, add_zero, ← hkb] using hib
      exact (hl.continuousAt.eventually_lt hr.continuousAt h0).mono (fun _ h _ => h)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε, hε, ?_⟩
  intro d hd t ht htε
  have hlocal := hball (show t ∈ Metric.ball 0 ε by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht] using htε)
  have hkSlope : s k d ≤ activeSlope I hI b s d := Finset.le_sup' (fun i => s i d) hkA
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    by_cases hb : b i = I.sup' hI b
    · have hiA : i ∈ active I hI b := Finset.mem_filter.mpr ⟨hi, hb⟩
      have his : s i d ≤ activeSlope I hI b s d := Finset.le_sup' (fun i => s i d) hiA
      rw [hb]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right his ht)
    · exact (hlocal i hi d hd hb).le.trans (by
        rw [← hkb]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hkSlope ht))
  · obtain ⟨j, hj, hjs⟩ := Finset.exists_mem_eq_sup' (active_nonempty I hI b) (fun i => s i d)
    have hjI := (Finset.mem_filter.mp hj).1
    have hjb := (Finset.mem_filter.mp hj).2
    change activeSlope I hI b s d = s j d at hjs
    calc
      _ = b j + s j d * t := by rw [hjs, hjb]
      _ ≤ _ := Finset.le_sup' (fun i => b i + s i d * t) hjI

/-- Genuine individual zero sums imply the nonnegative sum of actual active directional maxima. -/
theorem sum_activeSlope_nonneg (I : Finset ι) (hI : I.Nonempty) (D : Finset δ)
    (b : ι → ℝ) (s : ι → δ → ℝ) (hs : ∀ i ∈ I, ∑ d ∈ D, s i d = 0) :
    0 ≤ ∑ d ∈ D, activeSlope I hI b s d := by
  classical
  obtain ⟨i, hi⟩ := active_nonempty I hI b
  have hiI := (Finset.mem_filter.mp hi).1
  have hle : (∑ d ∈ D, s i d) ≤ ∑ d ∈ D, activeSlope I hI b s d :=
    Finset.sum_le_sum (fun d _ => Finset.le_sup' (fun j => s j d) hi)
  rwa [hs i hiI] at hle
end EnvelopeProperty.FiniteAffineMax
