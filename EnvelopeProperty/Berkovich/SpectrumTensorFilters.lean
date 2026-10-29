/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFilters
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Genuine tensor coordinate ultrafilter limits

Separate eventual bounds on both tensor inclusions bound every tensor
coordinate. A genuine surjective tensor presentation and the actual closed
evaluation embedding then produce a seminorm ultrafilter limit.
-/


open scoped NNReal Topology TensorProduct
open Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B]

/-- Individual eventual bounds on the two actual tensor inclusions bound every tensor coordinate. -/
theorem eventual_tensor_bound (φ : A ⊗[R] B →+* C) (U : Ultrafilter (Spectrum C))
    (hA : ∀ a : A, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum C)),
      z.val (φ (a ⊗ₜ[R] (1 : B))) ≤ M)
    (hB : ∀ b : B, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum C)),
      z.val (φ ((1 : A) ⊗ₜ[R] b)) ≤ M) (t : A ⊗[R] B) :
    ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum C)), z.val (φ t) ≤ M := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Eventually.of_forall fun z => by simp⟩
  | tmul a b =>
    obtain ⟨M, hM⟩ := hA a
    obtain ⟨N, hN⟩ := hB b
    refine ⟨M * N, (hM.and hN).mono fun z hz => ?_⟩
    have ht : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [ht, map_mul, map_mul]
    exact mul_le_mul' hz.1 hz.2
  | add t s ht hs =>
    obtain ⟨M, hM⟩ := ht
    obtain ⟨N, hN⟩ := hs
    refine ⟨max M N, (hM.and hN).mono fun z hz => ?_⟩
    rw [map_add]
    exact (z.val.map_add _ _).trans (max_le_max hz.1 hz.2)

/-- A genuine surjective tensor presentation and separate inclusion bounds produce an actual spectrum limit. -/
theorem exists_ultrafilter_limit_of_tensor_bounds (φ : A ⊗[R] B →+* C)
    (hφ : Function.Surjective φ) (U : Ultrafilter (Spectrum C))
    (hA : ∀ a : A, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum C)),
      z.val (φ (a ⊗ₜ[R] (1 : B))) ≤ M)
    (hB : ∀ b : B, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum C)),
      z.val (φ ((1 : A) ⊗ₜ[R] b)) ≤ M) :
    ∃ z : Spectrum C, (U : Filter (Spectrum C)) ≤ 𝓝 z := by
  apply exists_ultrafilter_limit_of_bounded_evaluations U
  intro c
  obtain ⟨t, rfl⟩ := hφ c
  exact eventual_tensor_bound φ U hA hB t
end EnvelopeProperty.Berkovich.Spectrum
