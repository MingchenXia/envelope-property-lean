import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Ring.Idempotent

/-! # Genuine nearby idempotents coincide in the whole original normed ring -/

namespace EnvelopeProperty

/-- The actual ring norm separates distinct idempotents by at least one, including all
nilpotent directions and without completeness or characteristic assumptions. -/
theorem eq_of_isIdempotent_of_norm_sub_lt_one {A : Type*} [NormedCommRing A]
    (e f : A) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hlt : ‖e-f‖ < 1) : e = f := by
  have he2 : e^2 = e := by rw [pow_two,he.eq]
  have hf2 : f^2 = f := by rw [pow_two,hf.eq]
  have he3 : e^3 = e := by rw [pow_succ,he2,he.eq]
  have hf3 : f^3 = f := by rw [pow_succ,hf2,hf.eq]
  have ht : (e-f)^3 = e-f := calc
    _ = e^3-3*e^2*f+3*e*f^2-f^3 := by ring
    _ = _ := by rw [he2,hf2,he3,hf3]; ring
  have hn : ‖e-f‖ ≤ ‖e-f‖^3 := by
    calc
      _ = ‖(e-f)^3‖ := congrArg norm ht.symm
      _ = ‖((e-f)*(e-f))*(e-f)‖ := by rw [pow_succ,pow_two]
      _ ≤ ‖(e-f)*(e-f)‖*‖e-f‖ := norm_mul_le _ _
      _ ≤ (‖e-f‖*‖e-f‖)*‖e-f‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = _ := by ring
  have hz : ‖e-f‖ = 0 := by
    by_contra hne
    have hp : 0 < ‖e-f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hs : ‖e-f‖^2 < 1 := by nlinarith [sq_nonneg (‖e-f‖-1)]
    have hc : ‖e-f‖^3 < ‖e-f‖ := by
      have hmul := mul_lt_mul_of_pos_left hs hp
      nlinarith
    exact (not_lt_of_ge hn) hc
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end EnvelopeProperty
