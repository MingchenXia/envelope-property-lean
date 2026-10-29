import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import EnvelopeProperty.DI.CechAlexanderWhitneyFactors

/-! # The shared-vertex cancellation in the ordinary Čech cup differential

This file contains only the finite alternating-sum identity used by the
original ordered prefix/suffix product.  It supplies no Čech product or
geometric differential identity as data.
-/

namespace EnvelopeProperty.DI.CechCupSigns

variable {G : Type*} [AddCommGroup G]

/-- The two shared-vertex terms of the prefix/suffix Čech boundary cancel.
The left sum omits the last prefix face; the right sum omits the first
suffix face. All other signs are their actual deletion positions. -/
theorem alternating_join (j j' : ℕ) (a : Fin (j+2) → G) (b : Fin (j'+2) → G)
    (hshared : a (Fin.last (j+1)) = b 0) :
    (∑ k : Fin (j+1), (-1 : ℤ)^k.val • a k.castSucc) +
        (∑ k : Fin (j'+1), (-1 : ℤ)^(j+1+k.val) • b k.succ) =
      (∑ k : Fin (j+2), (-1 : ℤ)^k.val • a k) +
        (-1 : ℤ)^j • (∑ k : Fin (j'+2), (-1 : ℤ)^k.val • b k) := by
  have htail :
      (-1 : ℤ)^j • (∑ k : Fin (j'+1), (-1 : ℤ)^(k.val+1) • b k.succ) =
        ∑ k : Fin (j'+1), (-1 : ℤ)^(j+1+k.val) • b k.succ := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_zsmul, ← pow_add]
    congr 2
    omega
  have hcancel : (-1 : ℤ)^(j+1) • a (Fin.last (j+1)) =
      -((-1 : ℤ)^j • b 0) := by
    rw [hshared, pow_succ]
    simp only [mul_neg, mul_one, neg_zsmul]
  rw [Fin.sum_univ_castSucc (fun k : Fin (j+2) => (-1 : ℤ)^k.val • a k),
    Fin.sum_univ_succ (fun k : Fin (j'+2) => (-1 : ℤ)^k.val • b k)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
    pow_zero, one_zsmul, zsmul_add]
  rw [htail, hcancel, add_assoc, ← add_assoc (-((-1 : ℤ)^j • b 0)),
    neg_add_cancel, zero_add]

/-- The original deleted-face sum obeys the product rule once its two
actual prefix/suffix deletion regimes and shared face have been identified. -/
theorem alternating_join_of_faces (j j' : ℕ)
    (a : Fin (j+2) → G) (b : Fin (j'+2) → G)
    (c : Fin ((j+1)+(j'+1)) → G)
    (hleft : ∀ k : Fin (j+1), c (Fin.castAdd (j'+1) k) = a k.castSucc)
    (hright : ∀ k : Fin (j'+1), c (Fin.natAdd (j+1) k) = b k.succ)
    (hshared : a (Fin.last (j+1)) = b 0) :
    (∑ k : Fin ((j+1)+(j'+1)), (-1 : ℤ)^k.val • c k) =
      (∑ k : Fin (j+2), (-1 : ℤ)^k.val • a k) +
        (-1 : ℤ)^j • (∑ k : Fin (j'+2), (-1 : ℤ)^k.val • b k) := by
  rw [Fin.sum_univ_add]
  simp only [hleft, hright, Fin.val_castAdd, Fin.val_natAdd]
  exact alternating_join j j' a b hshared

open CechAlexanderWhitneyProduct

/-- Deleting a prefix vertex gives the same actual prefix deletion. -/
theorem prefix_delete_left (j j' : ℕ) (k a : Fin (j+1)) :
    ((⟨k.val, by omega⟩ : Fin (j+j'+2)).succAbove (tuplePrefix j j' a)).val =
      (k.castSucc.succAbove a).val := by
  by_cases h : a.val < k.val <;>
    simp [Fin.succAbove, tuplePrefix, Fin.lt_def, h]

/-- Deleting a prefix vertex shifts the actual suffix starting vertex. -/
theorem suffix_delete_left (j j' : ℕ) (k : Fin (j+1)) (a : Fin (j'+1)) :
    ((⟨k.val, by omega⟩ : Fin (j+j'+2)).succAbove (tupleSuffix j j' a)).val =
      (tupleSuffix (j+1) j' a).val := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by
    change k.val ≤ j+a.val
    omega)]
  simp only [Fin.val_succ, tupleSuffix]
  omega

/-- Deleting a suffix vertex leaves the actual prefix unchanged. -/
theorem prefix_delete_right (j j' : ℕ) (k : Fin (j'+1)) (a : Fin (j+1)) :
    ((⟨j+1+k.val, by omega⟩ : Fin (j+j'+2)).succAbove (tuplePrefix j j' a)).val =
      (tuplePrefix j (j'+1) a).val := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    change a.val < j+1+k.val
    omega)]
  rfl

/-- A suffix deletion has its actual position shifted by one in the suffix. -/
theorem suffix_delete_right (j j' : ℕ) (k a : Fin (j'+1)) :
    ((⟨j+1+k.val, by omega⟩ : Fin (j+j'+2)).succAbove (tupleSuffix j j' a)).val =
      (tupleSuffix j (j'+1) (k.succ.succAbove a)).val := by
  by_cases h : a.val ≤ k.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change j+a.val < j+1+k.val
      omega), Fin.succAbove_succ_of_le _ _ (by exact h)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by
      change j+1+k.val ≤ j+a.val
      omega), Fin.succAbove_succ_of_lt _ _ (by exact Nat.lt_of_not_ge h)]
    simp only [Fin.val_succ, tupleSuffix]
    omega

end EnvelopeProperty.DI.CechCupSigns
