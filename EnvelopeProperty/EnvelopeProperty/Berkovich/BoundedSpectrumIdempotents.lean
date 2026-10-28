/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.UnnormalizedSmoothingMaximum
import EnvelopeProperty.Berkovich.SpectrumIdempotentSummand

/-! # Whole original idempotents are detected by their genuine bounded points -/

open scoped NNReal Topology
open Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.NormBoundedSpectrum

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E]

/-- EVERY actual bounded point detects a whole original idempotent, without completeness
or a normalized unit norm. -/
theorem idempotent_eq_zero_iff {e : E} (he : IsIdempotentElem e) :
    e = 0 ↔ ∀ x : NormBoundedSpectrum E, x.1.val e = 0 := by
  constructor
  · rintro rfl x
    exact map_zero _
  · intro hz
    have hp := (forall_bounded_value_lt_one_iff_tendsto_pow_zero e).mp
      (fun x => by rw [hz x]; exact zero_lt_one)
    have hs := hp.comp (tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, he.pow_succ_eq] at hs
    exact tendsto_nhds_unique tendsto_const_nhds hs

private theorem idempotent_complement_product_zero {e f : E}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : ∀ x : NormBoundedSpectrum E, x.1.val e = 1 → x.1.val f = 1) :
    e * (1 - f) = 0 := by
  apply (idempotent_eq_zero_iff (he.mul hf.one_sub)).mpr
  intro x
  by_cases hz : x.1.val e = 0
  · rw [map_mul, hz, zero_mul]
  · have he1 := (Spectrum.val_idempotent_ne_zero_iff he x.1).mp hz
    have hf1 := h x he1
    have hc := congrArg x.1.val hf.mul_one_sub_self
    rw [map_mul, hf1, one_mul, map_zero] at hc
    rw [map_mul, hc, mul_zero]

/-- Equality of the literal value-one loci at ALL original bounded points determines the
WHOLE original idempotent, including rings with nilpotents and the zero ring. -/
theorem idempotent_eq_iff_valueOne_locus_eq {e f : E}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    e = f ↔ {x : NormBoundedSpectrum E | x.1.val e = 1} =
      {x : NormBoundedSpectrum E | x.1.val f = 1} := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have ha := idempotent_complement_product_zero he hf
      (fun x hx => (Set.ext_iff.mp h x).mp hx)
    have hb := idempotent_complement_product_zero hf he
      (fun x hx => (Set.ext_iff.mp h x).mpr hx)
    rw [mul_sub, mul_one] at ha hb
    exact (sub_eq_zero.mp ha).trans ((mul_comm e f).trans (sub_eq_zero.mp hb).symm)

end EnvelopeProperty.Berkovich.NormBoundedSpectrum
