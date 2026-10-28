import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-! # A homogeneous root norm bound from a genuine finite monic relation -/

namespace TranscendentalNakamaye.Pending.MonicRelationWeightedNormBound

open Finset

/-- A genuine monic relation with homogeneous coefficient bounds produces a
root norm bound without dividing by the possible zero scale. -/
theorem norm_le_of_monic_relation {d : ℕ} (hd : 0 < d) (a : ℂ)
    (b : Fin d → ℂ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hcoeff : ∀ i, ‖b i‖ ≤ C * s ^ (d - i.val))
    (hrel : a ^ d + ∑ i, b i * a ^ i.val = 0) :
    ‖a‖ ≤ ((d : ℝ) * C + 1) * s := by
  rcases d with _ | k
  · omega
  · by_cases hrs : ‖a‖ ≤ s
    · have hnonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * C * s :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hs
      nlinarith
    · have hsr : s < ‖a‖ := lt_of_not_ge hrs
      have hrpos : 0 < ‖a‖ := hs.trans_lt hsr
      have hterm (i : Fin (k + 1)) :
          ‖b i * a ^ i.val‖ ≤ C * s * ‖a‖ ^ k := by
        have hi : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
        have hexp : k + 1 - i.val = (k - i.val) + 1 := by omega
        calc
          ‖b i * a ^ i.val‖ = ‖b i‖ * ‖a‖ ^ i.val := by rw [norm_mul, norm_pow]
          _ ≤ (C * s ^ (k + 1 - i.val)) * ‖a‖ ^ i.val :=
            mul_le_mul_of_nonneg_right (hcoeff i) (pow_nonneg (norm_nonneg _) _)
          _ = C * s * (s ^ (k - i.val) * ‖a‖ ^ i.val) := by rw [hexp, pow_succ]; ring
          _ ≤ C * s * (‖a‖ ^ (k - i.val) * ‖a‖ ^ i.val) := by
            gcongr
          _ = C * s * ‖a‖ ^ k := by rw [← pow_add, Nat.sub_add_cancel hi]
      have heq : a ^ (k + 1) = -∑ i, b i * a ^ i.val :=
        eq_neg_of_add_eq_zero_left hrel
      have hbound : ‖a‖ ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) * C * s * ‖a‖ ^ k := by
        calc
          ‖a‖ ^ (k + 1) = ‖∑ i, b i * a ^ i.val‖ := by rw [← norm_pow, heq, norm_neg]
          _ ≤ ∑ i, ‖b i * a ^ i.val‖ := norm_sum_le _ _
          _ ≤ ∑ _i : Fin (k + 1), C * s * ‖a‖ ^ k := sum_le_sum fun i _ => hterm i
          _ = ((k + 1 : ℕ) : ℝ) * C * s * ‖a‖ ^ k := by simp [mul_assoc]
      have hcancel : ‖a‖ ≤ ((k + 1 : ℕ) : ℝ) * C * s := by
        apply (mul_le_mul_iff_right₀ (pow_pos hrpos k)).mp
        simpa only [pow_succ, mul_comm (‖a‖ ^ k)] using hbound
      nlinarith

end TranscendentalNakamaye.Pending.MonicRelationWeightedNormBound
