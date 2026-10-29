import EnvelopeProperty.Potential.BanachIdempotentLifting

/-! # Actual Newton idempotent lifting beyond the unit ball -/

open scoped Topology
open Topology Filter
noncomputable section

namespace EnvelopeProperty

variable {A : Type*} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]

private theorem fc_bounded_norm_natCast (n : ℕ) : ‖(n : A)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

private def fcBoundedIdempotentNewton (a : A) : A := 3*a^2-2*a^3

private theorem fcBoundedIdempotentNewton_sub_bound {a : A} {C : ℝ}
    (hC : 1 ≤ C) (ha : ‖a‖ ≤ C) :
    ‖fcBoundedIdempotentNewton a-a‖ ≤ C*‖a*a-a‖ := by
  have he : fcBoundedIdempotentNewton a-a = (1-2*a)*(a*a-a) := by
    unfold fcBoundedIdempotentNewton
    ring
  have htwo : ‖(2 : A)*a‖ ≤ C := (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (fc_bounded_norm_natCast 2) (norm_nonneg _)).trans
      (by simpa only [one_mul] using ha))
  have hc : ‖(1 : A)-2*a‖ ≤ C := by
    simpa only [sub_eq_add_neg,norm_neg] using
      (IsUltrametricDist.norm_add_le_max (1 : A) (-(2*a))).trans (max_le (by simpa using hC) (by simpa using htwo))
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

private theorem fcBoundedIdempotentNewton_defect_bound {a : A} {C : ℝ}
    (hC : 1 ≤ C) (ha : ‖a‖ ≤ C) :
    ‖fcBoundedIdempotentNewton a*fcBoundedIdempotentNewton a-fcBoundedIdempotentNewton a‖ ≤
      C^2*‖a*a-a‖^2 := by
  have he : fcBoundedIdempotentNewton a*fcBoundedIdempotentNewton a-fcBoundedIdempotentNewton a =
      (a*a-a)^2*(4*a^2-4*a-3) := by unfold fcBoundedIdempotentNewton; ring
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCsq : C ≤ C^2 := by nlinarith
  have hnormpow : ‖a^2‖ ≤ C^2 :=
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
  have hfourpow : ‖(4 : A)*a^2‖ ≤ C^2 := (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (fc_bounded_norm_natCast 4) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hnormpow))
  have hfour : ‖(4 : A)*a‖ ≤ C^2 := (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (fc_bounded_norm_natCast 4) (norm_nonneg _)).trans
      (by simpa only [one_mul] using ha.trans hCsq))
  have hsub : ‖(4 : A)*a^2-4*a‖ ≤ C^2 := by
    simpa only [sub_eq_add_neg,norm_neg] using
      (IsUltrametricDist.norm_add_le_max ((4 : A)*a^2) (-(4*a))).trans
        (max_le hfourpow (by simpa only [norm_neg] using hfour))
  have hc : ‖(4 : A)*a^2-4*a-3‖ ≤ C^2 := by
    simpa only [sub_eq_add_neg,norm_neg] using
      (IsUltrametricDist.norm_add_le_max ((4 : A)*a^2-4*a) (-(3 : A))).trans
        (max_le hsub (by simpa only [norm_neg,Nat.cast_ofNat] using
          (fc_bounded_norm_natCast (A := A) 3).trans (hC.trans hCsq)))
  rw [he]
  calc
    _ ≤ ‖(a*a-a)^2‖*‖(4 : A)*a^2-4*a-3‖ := norm_mul_le _ _
    _ ≤ ‖a*a-a‖^2*C^2 := mul_le_mul (norm_pow_le _ _) hc (norm_nonneg _) (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- An actual bounded initial element lifts to an actual idempotent when its scaled defect is small. -/
theorem exists_idempotent_close_of_scaled_norm_defect_lt_one [CompleteSpace A]
    (b : A) (C : ℝ) (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (herr : C^2*‖b*b-b‖ < 1) :
    ∃ e : A, IsIdempotentElem e ∧ ‖e-b‖ ≤ C*‖b*b-b‖ ∧ ‖e‖ ≤ C := by
  let q : ℝ := ‖b*b-b‖
  let ρ : ℝ := C^2*q
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCsq : 1 ≤ C^2 := by nlinarith
  have hqρ : q ≤ ρ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hCsq hq0
  have hq1 : q ≤ 1 := hqρ.trans herr.le
  have hρ0 : 0 ≤ ρ := mul_nonneg (sq_nonneg _) hq0
  have hρ1 : ρ ≤ 1 := herr.le
  let u : ℕ → A := fun n => fcBoundedIdempotentNewton^[n] b
  have hu0 : u 0 = b := rfl
  have hus (n : ℕ) : u (n+1) = fcBoundedIdempotentNewton (u n) := Function.iterate_succ_apply' _ _ _
  have hbounds : ∀ n, ‖u n‖ ≤ C ∧ ‖u n*u n-u n‖ ≤ q ∧ ‖u n*u n-u n‖ ≤ q*ρ^n := by
    intro n
    induction n with
    | zero => simpa only [hu0,pow_zero,mul_one] using And.intro hb (And.intro le_rfl le_rfl)
    | succ n ih =>
      have he := fcBoundedIdempotentNewton_defect_bound hC ih.1
      have hquad : C^2*‖u n*u n-u n‖^2 ≤ ρ*‖u n*u n-u n‖ := by
        calc
          _ = C^2*‖u n*u n-u n‖*‖u n*u n-u n‖ := by ring
          _ ≤ (C^2*q)*‖u n*u n-u n‖ := by gcongr; exact ih.2.1
          _ = _ := rfl
      have hsmall : ρ*‖u n*u n-u n‖ ≤ ‖u n*u n-u n‖ :=
        (mul_le_mul_of_nonneg_right hρ1 (norm_nonneg _)).trans_eq (one_mul _)
      have hgeo : ρ*‖u n*u n-u n‖ ≤ q*ρ^(n+1) := by
        calc
          _ ≤ ρ*(q*ρ^n) := mul_le_mul_of_nonneg_left ih.2.2 hρ0
          _ = _ := by rw [pow_succ]; ring
      have hnorm : ‖u (n+1)‖ ≤ C := by
        have heq : u (n+1) = u n+(u (n+1)-u n) := by abel
        rw [heq]
        apply (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih.1 ?_)
        rw [hus]
        exact (fcBoundedIdempotentNewton_sub_bound hC ih.1).trans
          ((mul_le_mul_of_nonneg_left (ih.2.1.trans hq1) hC0).trans_eq (mul_one _))
      exact ⟨hnorm,by rw [hus]; exact (he.trans hquad).trans (hsmall.trans ih.2.1),
        by rw [hus]; exact he.trans (hquad.trans hgeo)⟩
  have hincrement (n : ℕ) : ‖u (n+1)-u n‖ ≤ (C*q)*ρ^n := by
    rw [hus]
    exact (fcBoundedIdempotentNewton_sub_bound hC (hbounds n).1).trans
      ((mul_le_mul_of_nonneg_left (hbounds n).2.2 hC0).trans_eq (mul_assoc _ _ _).symm)
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric ρ (C*q) herr (by
    intro n
    simpa only [dist_eq_norm,norm_sub_rev] using hincrement n)
  obtain ⟨e,he⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hdefect : Tendsto (fun n => ‖u n*u n-u n‖) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun n : ℕ => q*ρ^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 herr)
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hbounds n).2.2) hgeo
  have hdefectLimit : Tendsto (fun n => ‖u n*u n-u n‖) atTop (𝓝 ‖e*e-e‖) :=
    (he.mul he |>.sub he).norm
  have heid : IsIdempotentElem e := sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hdefectLimit hdefect))
  have hclose : ∀ n, ‖u n-b‖ ≤ C*q := by
    intro n
    induction n with
    | zero => simpa only [hu0,sub_self,norm_zero] using mul_nonneg hC0 hq0
    | succ n ih =>
      have heq : u (n+1)-b = (u (n+1)-u n)+(u n-b) := by abel
      rw [heq]
      apply (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      rw [hus]
      exact (fcBoundedIdempotentNewton_sub_bound hC (hbounds n).1).trans
        (mul_le_mul_of_nonneg_left (hbounds n).2.1 hC0)
  refine ⟨e,heid,?_,?_⟩
  · exact le_of_tendsto (he.sub_const b |>.norm) (Filter.Eventually.of_forall hclose)
  · exact le_of_tendsto he.norm (Filter.Eventually.of_forall fun n => (hbounds n).1)

end EnvelopeProperty
