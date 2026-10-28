/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.PowerSeminormValuation
import EnvelopeProperty.NormedIdealQuotientUnit
import EnvelopeProperty.Berkovich.SpectrumNormedCompletion
import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

/-! # Actual bounded spectral points and Banach units -/
open scoped NNReal Topology
open Topology
noncomputable section
namespace EnvelopeProperty.Berkovich

/-- Actual smoothing and the genuine minimal-seminorm valuation construct a bounded point. -/
theorem exists_normBoundedSpectrum (E : Type*) [SeminormedCommRing E]
    [IsUltrametricDist E] [NormOneClass E] : Nonempty (NormBoundedSpectrum E) := by
  let μ := SeminormedRing.toRingSeminorm E
  have hμ1 : μ 1 = 1 := norm_one
  have hμna : IsNonarchimedean μ := IsUltrametricDist.isNonarchimedean_norm
  let ν := smoothingSeminorm μ hμ1.le hμna
  have hν1 : ν 1 = 1 := by
    change smoothingFun μ 1 = 1
    rw [smoothingFun_of_powMul μ hμ1.le (fun n _ => by simp [μ])]
    exact hμ1
  have hνna : IsNonarchimedean ν := isNonarchimedean_smoothingFun μ hμ1.le hμna
  have hνpow : IsPowMul ν := isPowMul_smoothingFun μ hμ1.le
  obtain ⟨v, hv, _⟩ := exists_valuation_le_preserving_mul ν hν1 hνna hνpow ∅ (by simp)
  refine ⟨⟨Spectrum.ofValuation v, fun a => ?_⟩⟩
  exact_mod_cast (hv a).trans (smoothingFun_le_self μ a)

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E]
  [CompleteSpace E] [NormOneClass E]

/-- Every original proper ideal has a genuine whole bounded point killing all its elements. -/
theorem exists_normBoundedSpectrum_zero_on_ideal (I : Ideal E) (hI : I ≠ ⊤) :
    ∃ x : NormBoundedSpectrum E, ∀ a ∈ I, x.1.val a = 0 := by
  let : Nontrivial (E ⧸ I.closure) :=
    Ideal.Quotient.nontrivial_iff.mpr (I.closure_ne_top hI)
  obtain ⟨x⟩ := exists_normBoundedSpectrum (E ⧸ I.closure)
  let y : NormBoundedSpectrum E :=
    ⟨Spectrum.comap (Ideal.Quotient.mk I.closure) x.1, fun a =>
      (x.2 _).trans (Ideal.Quotient.norm_mk_le I.closure a)⟩
  refine ⟨y, fun a ha => ?_⟩
  change x.1.val (Ideal.Quotient.mk I.closure a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show a ∈ I.closure from subset_closure ha), map_zero]

/-- Actual units are precisely elements with no zero on the genuine entire bounded spectrum. -/
theorem isUnit_iff_forall_normBoundedSpectrum_ne_zero (b : E) :
    IsUnit b ↔ ∀ x : NormBoundedSpectrum E, x.1.val b ≠ 0 := by
  constructor
  · intro hb x
    exact (hb.map x.1.val).ne_zero
  · intro hb
    by_contra hn
    obtain ⟨x, hx⟩ := exists_normBoundedSpectrum_zero_on_ideal
      (Ideal.span ({b} : Set E)) (Ideal.span_singleton_ne_top hn)
    exact hb x (hx b (Ideal.subset_span (Set.mem_singleton b)))

/-- The same genuine unit criterion expressed by strictly positive values. -/
theorem isUnit_iff_forall_normBoundedSpectrum_pos (b : E) :
    IsUnit b ↔ ∀ x : NormBoundedSpectrum E, 0 < x.1.val b := by
  simpa only [pos_iff_ne_zero] using isUnit_iff_forall_normBoundedSpectrum_ne_zero b

end EnvelopeProperty.Berkovich
