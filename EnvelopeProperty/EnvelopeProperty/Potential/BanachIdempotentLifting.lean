import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.Idempotent

/-! # Genuine integral-polynomial Newton lifting in complete ultrametric normed rings -/

open scoped Topology
open Topology Filter
noncomputable section

namespace EnvelopeProperty

variable {A : Type*} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]

omit [NormOneClass A] in
private theorem fc_norm_add_le_one {a b : A} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a+b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

omit [NormOneClass A] in
private theorem fc_norm_sub_le_one {a b : A} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a-b‖ ≤ 1 := by
  simpa only [sub_eq_add_neg,norm_neg] using fc_norm_add_le_one ha (show ‖-b‖ ≤ 1 by simpa)

omit [NormOneClass A] [IsUltrametricDist A] in
private theorem fc_norm_mul_le_one {a b : A} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a*b‖ ≤ 1 := (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg _) hb)

private theorem fc_norm_natCast_le_one (n : ℕ) : ‖(n : A)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Nat.cast_add,Nat.cast_one] using fc_norm_add_le_one ih (by simp : ‖(1 : A)‖ ≤ 1)

omit [IsUltrametricDist A] in
private theorem fc_norm_pow_le_one {a : A} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a^n‖ ≤ 1 :=
  (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) ha)

private def fcIdempotentNewton (a : A) : A := 3*a^2-2*a^3

private theorem fcIdempotentNewton_norm_le_one {a : A} (ha : ‖a‖ ≤ 1) :
    ‖fcIdempotentNewton a‖ ≤ 1 :=
  fc_norm_sub_le_one
    (fc_norm_mul_le_one (fc_norm_natCast_le_one 3) (fc_norm_pow_le_one ha 2))
    (fc_norm_mul_le_one (fc_norm_natCast_le_one 2) (fc_norm_pow_le_one ha 3))

private theorem fcIdempotentNewton_sub_bound {a : A} (ha : ‖a‖ ≤ 1) :
    ‖fcIdempotentNewton a-a‖ ≤ ‖a*a-a‖ := by
  have he : fcIdempotentNewton a-a = (1-2*a)*(a*a-a) := by unfold fcIdempotentNewton; ring
  have hc : ‖(1 : A)-2*a‖ ≤ 1 := fc_norm_sub_le_one (by simp)
    (fc_norm_mul_le_one (fc_norm_natCast_le_one 2) ha)
  rw [he]
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _))

private theorem fcIdempotentNewton_defect_bound {a : A} (ha : ‖a‖ ≤ 1) :
    ‖fcIdempotentNewton a*fcIdempotentNewton a-fcIdempotentNewton a‖ ≤ ‖a*a-a‖^2 := by
  have he : fcIdempotentNewton a*fcIdempotentNewton a-fcIdempotentNewton a =
      (a*a-a)^2*(4*a^2-4*a-3) := by unfold fcIdempotentNewton; ring
  have hc : ‖(4 : A)*a^2-4*a-3‖ ≤ 1 :=
    fc_norm_sub_le_one
      (fc_norm_sub_le_one
        (fc_norm_mul_le_one (fc_norm_natCast_le_one 4) (fc_norm_pow_le_one ha 2))
        (fc_norm_mul_le_one (fc_norm_natCast_le_one 4) ha)) (fc_norm_natCast_le_one 3)
  rw [he]
  calc
    _ ≤ ‖(a*a-a)^2‖*‖(4 : A)*a^2-4*a-3‖ := norm_mul_le _ _
    _ ≤ ‖a*a-a‖^2*1 := mul_le_mul (norm_pow_le _ _) hc (norm_nonneg _) (sq_nonneg _)
    _ = _ := mul_one _

/-- Actual idempotent lifting by an integral polynomial; the coefficient 2 is never inverted. -/
theorem exists_idempotent_close_of_norm_defect_lt_one [CompleteSpace A]
    (b : A) (hb : ‖b‖ ≤ 1) (herr : ‖b*b-b‖ < 1) :
    ∃ e : A, IsIdempotentElem e ∧ ‖e-b‖ ≤ ‖b*b-b‖ ∧ ‖e‖ ≤ 1 := by
  let q : ℝ := ‖b*b-b‖
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q ≤ 1 := herr.le
  let u : ℕ → A := fun n => fcIdempotentNewton^[n] b
  have hu0 : u 0 = b := rfl
  have hus (n : ℕ) : u (n+1) = fcIdempotentNewton (u n) := Function.iterate_succ_apply' _ _ _
  have hbounds : ∀ n, ‖u n‖ ≤ 1 ∧ ‖u n*u n-u n‖ ≤ q ∧ ‖u n*u n-u n‖ ≤ q*q^n := by
    intro n
    induction n with
    | zero => simpa only [hu0,pow_zero,mul_one] using And.intro hb (And.intro le_rfl le_rfl)
    | succ n ih =>
      have he := fcIdempotentNewton_defect_bound ih.1
      have hquad : ‖u n*u n-u n‖^2 ≤ q*‖u n*u n-u n‖ := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right ih.2.1 (norm_nonneg _)
      have hsmall : q*‖u n*u n-u n‖ ≤ ‖u n*u n-u n‖ :=
        (mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)).trans_eq (one_mul _)
      have hgeo : q*‖u n*u n-u n‖ ≤ q*q^(n+1) := by
        calc
          _ ≤ q*(q*q^n) := mul_le_mul_of_nonneg_left ih.2.2 hq0
          _ = _ := by rw [pow_succ]; ring
      rw [hus]
      exact ⟨fcIdempotentNewton_norm_le_one ih.1,
        (he.trans hquad).trans (hsmall.trans ih.2.1),he.trans (hquad.trans hgeo)⟩
  have hincrement (n : ℕ) : ‖u (n+1)-u n‖ ≤ q*q^n := by
    rw [hus]
    exact (fcIdempotentNewton_sub_bound (hbounds n).1).trans (hbounds n).2.2
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric q q herr (by
    intro n
    simpa only [dist_eq_norm,norm_sub_rev] using hincrement n)
  obtain ⟨e,he⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hdefect : Tendsto (fun n => ‖u n*u n-u n‖) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun n : ℕ => q*q^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 herr)
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hbounds n).2.2) hgeo
  have hdefectLimit : Tendsto (fun n => ‖u n*u n-u n‖) atTop (𝓝 ‖e*e-e‖) :=
    (he.mul he |>.sub he).norm
  have heid : IsIdempotentElem e := sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hdefectLimit hdefect))
  have hclose : ∀ n, ‖u n-b‖ ≤ q := by
    intro n
    induction n with
    | zero => simpa only [hu0,sub_self,norm_zero] using hq0
    | succ n ih =>
      have heq : u (n+1)-b = (u (n+1)-u n)+(u n-b) := by abel
      rw [heq]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (by rw [hus]; exact (fcIdempotentNewton_sub_bound (hbounds n).1).trans (hbounds n).2.1) ih)
  refine ⟨e,heid,?_,?_⟩
  · exact le_of_tendsto (he.sub_const b |>.norm) (Filter.Eventually.of_forall hclose)
  · exact le_of_tendsto he.norm (Filter.Eventually.of_forall fun n => (hbounds n).1)

end EnvelopeProperty
