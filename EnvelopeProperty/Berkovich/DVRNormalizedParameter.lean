import EnvelopeProperty.Berkovich.DVRFractionPoint
import EnvelopeProperty.Berkovich.GaussValuation

/-! # Actual normalization of an original DVR parameter gives the whole Gauss base -/
open scoped NNReal Polynomial
open Polynomial IsDiscreteValuationRing Classical
noncomputable section
namespace EnvelopeProperty.Berk
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- Every original polynomial evaluated at a strictly small nonzero parameter
has its TRUE Gauss value; the entire polynomial comparison is proved. -/
theorem valuation_aeval_eq_gauss_of_lt_one (y : Berk k A) (t : A)
    (ht0 : 0 < y.val t) (ht1 : y.val t < 1) (F : k[X]) :
    y.val (aeval t F) = gaussValuation (1 : Valuation k ℝ≥0) (y.val t) F := by
  classical
  by_cases hF : F = 0
  · subst F
    simp only [map_zero]
  have hs : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro h
    exact hF (Polynomial.support_eq_empty.mp h))
  let j := F.support.min' hs
  have hj : j ∈ F.support := Finset.min'_mem _ hs
  have hterm (i : ℕ) (hi : i ∈ F.support) :
      y.val (algebraMap k A (F.coeff i) * t ^ i) = y.val t ^ i := by
    rw [y.val.map_mul,y.val.map_pow,y.val_algebraMap _ (Polynomial.mem_support_iff.mp hi),one_mul]
  have hmin (i : ℕ) (hi : i ∈ F.support) : j ≤ i := Finset.min'_le _ _ hi
  have heval : y.val (aeval t F) = y.val t ^ j := by
    rw [Polynomial.aeval_def,Polynomial.eval₂_eq_sum,Polynomial.sum_def,
      y.val.map_sum_eq_of_lt hj,hterm j hj]
    intro i hi
    have hi' := Finset.mem_sdiff.mp hi
    have hij : j < i := lt_of_le_of_ne (hmin i hi'.1)
      (Ne.symm (Finset.notMem_singleton.mp hi'.2))
    rw [hterm i hi'.1,hterm j hj]
    exact (pow_lt_pow_iff_right_of_lt_one₀ ht0 ht1).mpr hij
  rw [heval,gaussValuation_apply]
  apply le_antisymm
  · have h := Finset.le_sup (f := fun i => (1 : Valuation k ℝ≥0) (F.coeff i) * y.val t ^ i) hj
    simpa only [Valuation.one_apply_of_ne_zero (Polynomial.mem_support_iff.mp hj),one_mul] using h
  · apply Finset.sup_le
    intro i hi
    rw [Valuation.one_apply_of_ne_zero (Polynomial.mem_support_iff.mp hi),one_mul]
    exact (pow_le_pow_iff_right_of_lt_one₀ ht0 ht1).mpr (hmin i hi)

variable {V K : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Algebra k V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra k K]
  [IsScalarTower k V K]

/-- The ORIGINAL nonzero DVR parameter derives a positive actual normalization
and the value of EVERY original coefficient polynomial at the SAME element. -/
theorem dvrFractionPoint_exists_normalized_parameter (t : V) (ht : t ≠ 0)
    (hm : t ∈ IsLocalRing.maximalIdeal V) :
    ∃ (c : ℝ) (hc : 0 < c),
      (dvrFractionPoint (k := k) (V := V) (K := K) hc).val (algebraMap V K t) = ProjBerk.gaussRadius ∧
      ∀ F : k[X], (dvrFractionPoint (k := k) (V := V) (K := K) hc).val
        (aeval (algebraMap V K t) F) = gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius F := by
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := V)).not.mpr ht)
  have hn0 : n ≠ 0 := by
    intro h
    have hzero : addVal V t = 0 := by rw [← hn,h,Nat.cast_zero]
    exact (IsLocalRing.mem_maximalIdeal _).mp hm (addVal_eq_zero_iff.mp hzero)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  let c : ℝ := (n : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr hnR
  have htval : (dvrFractionPoint (k := k) (V := V) (K := K) hc).val
      (algebraMap V K t) = ProjBerk.gaussRadius := by
    rw [dvrFractionPoint_val_algebraMap,← hn,expOrd_coe]
    apply NNReal.eq
    change Real.exp (-((n : ℝ)⁻¹)) ^ n = Real.exp (-1)
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  refine ⟨c,hc,htval,fun F => ?_⟩
  have hr0 : (0 : ℝ≥0) < ProjBerk.gaussRadius := by
    change (0 : ℝ) < Real.exp (-1)
    exact Real.exp_pos _
  have hr1 : ProjBerk.gaussRadius < 1 := by
    change Real.exp (-1) < (1 : ℝ)
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  simpa only [htval] using valuation_aeval_eq_gauss_of_lt_one
    (dvrFractionPoint (k := k) (V := V) (K := K) hc) (algebraMap V K t)
    (htval.symm ▸ hr0) (htval.symm ▸ hr1) F

end EnvelopeProperty.Berk
