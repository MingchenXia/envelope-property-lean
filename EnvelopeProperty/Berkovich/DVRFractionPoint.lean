/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.DVRPolynomialRestriction
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# The actual fraction-field seminorm of an arbitrary original DVR

The original ring is exactly the integer ring of the actual extended original norm.
No containment of an unrelated affine coordinate algebra is assumed.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty.Berk

open IsDiscreteValuationRing

variable {k V K : Type*} [Field k] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Algebra k V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra k K]
  [IsScalarTower k V K]

private theorem dvrPoint_nonZeroDivisors {c : ℝ} (hc : 0 < c) :
    nonZeroDivisors V ≤ (dvrPoint (AlgHom.id k V) (expNeg c)
      (ProjBerk.expNeg_le_one hc.le)).val.supp.primeCompl := by
  intro a ha
  change expOrd (expNeg c) (addVal V a) ≠ 0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    ((addVal_eq_top_iff (R := V)).not.mpr (nonZeroDivisors.ne_zero ha))
  rw [← hn, expOrd_coe]
  have hq : 0 < expNeg c := by
    change (0 : ℝ) < Real.exp (-c)
    exact Real.exp_pos _
  exact pow_ne_zero n hq.ne'

/-- The actual original DVR norm, extended to its actual fraction field. -/
def dvrFractionPoint {c : ℝ} (hc : 0 < c) : Berk k K where
  val := (dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val.extendToLocalization
    (dvrPoint_nonZeroDivisors (k := k) (V := V) hc) K
  val_algebraMap a ha := by
    rw [IsScalarTower.algebraMap_eq k V K, RingHom.comp_apply,
      Valuation.extendToLocalization_apply_map_apply]
    exact (dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val_algebraMap a ha

/-- Every entire original DVR element retains its exact original norm. -/
theorem dvrFractionPoint_val_algebraMap {c : ℝ} (hc : 0 < c) (a : V) :
    (dvrFractionPoint (k := k) (V := V) (K := K) hc).val (algebraMap V K a) =
      expOrd (expNeg c) (addVal V a) :=
  Valuation.extendToLocalization_apply_map_apply _
    (dvrPoint_nonZeroDivisors (k := k) (V := V) hc) K a

/-- Every original DVR element has extended norm at most one. -/
theorem dvrFractionPoint_val_algebraMap_le_one {c : ℝ} (hc : 0 < c) (a : V) :
    (dvrFractionPoint (k := k) (V := V) (K := K) hc).val (algebraMap V K a) ≤ 1 := by
  rw [dvrFractionPoint_val_algebraMap]
  exact expOrd_le_one (ProjBerk.expNeg_le_one hc.le) _

/-- The original DVR is EXACTLY the integer ring of its actual extended fraction-field norm. -/
theorem dvrFractionPoint_integers {c : ℝ} (hc : 0 < c) :
    (dvrFractionPoint (k := k) (V := V) (K := K) hc).val.Integers V where
  hom_inj := IsFractionRing.injective V K
  map_le_one := dvrFractionPoint_val_algebraMap_le_one hc
  exists_of_le_one := by
    intro x hx
    by_cases hex : ∃ a : V, algebraMap V K a = x
    · exact hex
    obtain hex | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger V x
    · exact hex
    have haunit : ¬ IsUnit a := by
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      apply hex
      refine ⟨b, ?_⟩
      have hx0 : x ≠ 0 := by
        intro hz
        subst x
        exact hex ⟨0, by simp⟩
      have h := congrArg (algebraMap V K) hb
      rw [map_mul, map_one, ha] at h
      calc
        algebraMap V K b = x * (x⁻¹ * algebraMap V K b) := by
          rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
        _ = x := by rw [h, mul_one]
    have hapos : (1 : ℕ∞) ≤ addVal V a := by
      apply Order.one_le_iff_ne_zero.mpr
      exact (addVal_eq_zero_iff).not.mpr haunit
    have hsmall : (dvrFractionPoint (k := k) (V := V) (K := K) hc).val (algebraMap V K a) < 1 := by
      rw [dvrFractionPoint_val_algebraMap]
      have h := expOrd_antitone (ProjBerk.expNeg_le_one hc.le) hapos
      have h1 : expOrd (expNeg c) (1 : ℕ∞) = expNeg c := by
        simpa only [Nat.cast_one, pow_one] using expOrd_coe (q := expNeg c) 1
      rw [h1] at h
      exact h.trans_lt (expNeg_lt_one_of_pos hc)
    rw [ha, map_inv₀] at hsmall
    have hx0 : (dvrFractionPoint (k := k) (V := V) (K := K) hc).val x ≠ 0 := by
      intro hz
      have hxzero : x = 0 := by
        exact (map_eq_zero _).mp hz
      subst x
      exact hex ⟨0, by simp⟩
    exact False.elim ((not_lt_of_ge ((one_le_inv₀ (pos_iff_ne_zero.mpr hx0)).mpr hx)) hsmall)

end EnvelopeProperty.Berk
