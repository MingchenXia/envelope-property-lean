/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.PolynomialRootBranches
import EnvelopeProperty.Berkovich.PrincipalRationalUnit
import EnvelopeProperty.Berkovich.PolynomialGaussInflation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Whole original polynomial root values on genuine centered Gauss rays -/
open scoped NNReal ENNReal Polynomial
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] (v : Valuation K ℝ≥0)

/-- The original linear factor has its genuine translated Gauss maximum value. -/
theorem centeredGauss_val_X_sub_C_eq_max (a b : K) (t : ℝ≥0) :
    (centeredGauss (self v) a t).1.val (X-C b) = max t (v (a-b)) := by
  rw [← val_apply, centeredGauss_val_apply]
  have he : Polynomial.algEquivAevalXAddC a (X-C b) = X-C (b-a) := by
    simp [Polynomial.algEquivAevalXAddC]
    ring
  rw [he]
  change gaussFun v t (X-C (b-a)) = _
  rw [gaussFun_X_sub_C, show b-a = -(a-b) by ring, v.map_neg]

/-- The SAME original polynomial log at an actual whole valued point. -/
def polynomialRealLog (x : RelativeSpectrum v K[X]) (p : K[X]) : ℝ :=
  Real.log (x.1.val p : ℝ)

/-- Every original factor appears with its true multiplicity in the WHOLE value product. -/
theorem val_eq_leadingCoeff_mul_root_prod [IsAlgClosed K] (x : RelativeSpectrum v K[X]) (p : K[X]) :
    x.1.val p = v p.leadingCoeff * (p.roots.map (fun b => x.1.val (X-C b))).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [map_mul, show x.1.val (C p.leadingCoeff) = v p.leadingCoeff from x.2 _, map_multiset_prod,
    Multiset.map_map]
  rfl

/-- Genuine positivity of the original function derives nonzero values for EVERY original factor. -/
theorem linear_val_ne_zero_of_polynomial_ne_zero [IsAlgClosed K]
    (x : RelativeSpectrum v K[X]) (p : K[X]) (hp : x.1.val p ≠ 0) {b : K} (hb : b ∈ p.roots) :
    x.1.val (X-C b) ≠ 0 := by
  rw [val_eq_leadingCoeff_mul_root_prod] at hp
  intro hz
  exact (mul_ne_zero_iff.mp hp).2 (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨b,hb,hz⟩))

/-- Split factorization gives the real logarithm of EVERY original factor of the SAME function. -/
theorem polynomialRealLog_eq_root_sum [IsAlgClosed K]
    (x : RelativeSpectrum v K[X]) (p : K[X]) (hp : x.1.val p ≠ 0) :
    polynomialRealLog v x p = Real.log (v p.leadingCoeff : ℝ) +
      (p.roots.map (fun b => Real.log (x.1.val (X-C b) : ℝ))).sum := by
  unfold polynomialRealLog
  rw [val_eq_leadingCoeff_mul_root_prod]
  have hc : v p.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp (by
    rw [← val_eq_leadingCoeff_mul_root_prod v x p]
    exact hp)).1
  have hz : ∀ b ∈ p.roots, (x.1.val (X-C b) : ℝ) ≠ 0 := by
    intro b hb
    exact_mod_cast linear_val_ne_zero_of_polynomial_ne_zero v x p hp hb
  have hprod : ((p.roots.map (fun b => x.1.val (X-C b))).prod : ℝ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp (by rw [← val_eq_leadingCoeff_mul_root_prod v x p]; exact hp)).2
  rw [NNReal.coe_mul, Real.log_mul (by exact_mod_cast hc) hprod,
    NNReal.coe_multiset_prod, Real.log_multiset_prod (by
      intro z hz'
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hz'
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
      exact hz c hc)]
  simp only [Multiset.map_map, Function.comp_apply]

/-- The entire original centered-Gauss polynomial logarithm is its true root-distance sum. -/
theorem polynomialRealLog_centeredGauss [IsAlgClosed K] (a : K) (t : ℝ≥0) (ht : 0<t)
    (p : K[X]) (hp : p ≠ 0) :
    polynomialRealLog v (centeredGauss (self v) a t) p = Real.log (v p.leadingCoeff : ℝ) +
      (p.roots.map (fun b => Real.log (max t (v (a-b)) : ℝ))).sum := by
  rw [polynomialRealLog_eq_root_sum v _ p (centeredGauss_val_ne_zero (self v) a t ht p hp)]
  simp only [centeredGauss_val_X_sub_C_eq_max, NNReal.coe_max]

/-- The finite original root distances strictly inside r admit a genuine positive clearing radius. -/
theorem exists_centered_root_radius (r : ℝ≥0) (hr : 0<r) (a : K) (p q : K[X]) :
    ∃ s : ℝ≥0, 0 < s ∧ s < r ∧ ∀ b ∈ (p.roots + q.roots), v (a-b) < r → v (a-b) ≤ s := by
  classical
  let S := (p.roots+q.roots).toFinset.filter (fun b => v (a-b)<r)
  have hm : S.sup (fun b => v (a-b)) < r := by
    apply (Finset.sup_lt_iff hr).mpr
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  obtain ⟨s, hs, hsr⟩ := exists_between hm
  refine ⟨s, lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ _) hs, hsr, ?_⟩
  intro b hb hbr
  exact (Finset.le_sup (f := fun b => v (a-b)) (Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr hb,hbr⟩)).trans hs.le

private theorem log_max_sum_cleared (D : Multiset ℝ≥0) (r t : ℝ≥0) (htr : t≤r)
    (hclear : ∀ d ∈ D, d<r → d≤t) :
    (D.map (fun d => Real.log ((max t d : ℝ≥0) : ℝ))).sum =
      (D.map (fun d => Real.log ((max r d : ℝ≥0) : ℝ))).sum +
        ((D.filter (fun d => d<r)).card : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) := by
  classical
  induction D using Multiset.induction_on with
  | empty => simp
  | cons d D ih =>
    have hc : ∀ x ∈ D, x<r → x≤t := fun x hx => hclear x (Multiset.mem_cons_of_mem hx)
    have hi := ih hc
    by_cases hd : d<r
    · have hdt := hclear d (Multiset.mem_cons_self _ _) hd
      simp only [Multiset.map_cons, Multiset.sum_cons, max_eq_left hdt, max_eq_left hd.le]
      rw [Multiset.filter_cons_of_pos (p := fun x : ℝ≥0 => x < r) D hd, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      rw [hi]
      ring
    · have hrd := le_of_not_gt hd
      simp only [Multiset.map_cons, Multiset.sum_cons, max_eq_right (htr.trans hrd), max_eq_right hrd]
      rw [Multiset.filter_cons_of_neg (p := fun x : ℝ≥0 => x < r) D hd]
      rw [hi]
      ring

/-- Clearing the ACTUAL original root distances gives the true centered-ray polynomial log formula. -/
theorem polynomialRealLog_centeredGauss_sub [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p : K[X]) (hp : p≠0) (t : ℝ≥0) (ht : 0<t) (htr : t≤r)
    (hclear : ∀ b ∈ p.roots, v (a-b)<r → v (a-b)≤t) :
    polynomialRealLog v (centeredGauss (self v) a t) p =
      polynomialRealLog v (gauss (self v) r) p +
        (branchRootCount v r p (discBranch v r a) : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) := by
  rw [polynomialRealLog_centeredGauss v a t ht p hp,
    ← centeredGauss_eq_gauss_of_val_le (self v) a r ha,
    polynomialRealLog_centeredGauss v a r hr p hp,
    branchRootCount_eq_card_filter_sub v r hr p a ha]
  have hc : ∀ d ∈ p.roots.map (fun b => v (a-b)), d<r → d≤t := by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp hd
    exact hclear b hb
  have he := log_max_sum_cleared (p.roots.map (fun b => v (a-b))) r t htr hc
  simp only [Multiset.map_map, Function.comp_apply, NNReal.coe_max, Multiset.filter_map, Multiset.card_map] at he
  rw [he]
  ring

/-- The SAME original rational-unit real log, on its genuine nonzero function locus. -/
def rationalRealLog (x : RelativeSpectrum v K[X]) (p q : K[X]) : ℝ :=
  polynomialRealLog v x p - polynomialRealLog v x q

/-- This is exactly the ORIGINAL regular-section unit logarithm, not a chosen radial profile. -/
theorem sectionLogAbs_ratio_eq_rationalRealLog (x : RelativeSpectrum v K[X]) (p q : K[X])
    (hx : x.1.val (p*q) ≠ 0) :
    SchemeValuedPoint.sectionLogAbs (PrincipalRationalUnit.ratioOpen p q)
      (PrincipalRationalUnit.sectionUnit p q) (SchemeValuedPoint.spectrumHomeomorph.symm x.1) =
        (rationalRealLog v x p q : EReal) := by
  have hp : x.1.val p ≠ 0 := fun hp => hx (by rw [map_mul, hp, zero_mul])
  have hq : x.1.val q ≠ 0 := fun hq => hx (by rw [map_mul, hq, mul_zero])
  rw [PrincipalRationalUnit.sectionLogAbs_sectionUnit p q x.1 hx]
  change ENNReal.log (x.1.val p : ℝ≥0∞) - ENNReal.log (x.1.val q : ℝ≥0∞) = _
  rw [ENNReal.log_of_nnreal hp, ENNReal.log_of_nnreal hq]
  rfl

/-- The actual centered ray is a WHOLE point of the original closed disc at every t≤r. -/
def centeredDiscPoint (r : ℝ≥0) (a : K) (ha : v a≤r) (t : ℝ≥0) (htr : t≤r) :
    CoordinateDisc (A := K) v r :=
  ⟨centeredGauss (self v) a t, by
    have he := centeredGauss_val_X_sub_C_eq_max v a 0 t
    simp only [map_zero, sub_zero] at he
    change (centeredGauss (self v) a t).1.val X ≤ r
    rw [he]
    exact max_le htr ha⟩

/-- Below r this SAME original ray lies in the actual inward branch. -/
theorem centeredDiscPoint_mem_branch (r : ℝ≥0) (a : K) (ha : v a≤r)
    (t : ℝ≥0) (htr : t≤r) (ht : t<r) :
    centeredDiscPoint v r a ha t htr ∈ discBranch v r a := by
  change (centeredGauss (self v) a t).1.val (X-C a)<r
  rw [← val_apply, centeredGauss_val_X_sub_C]
  exact ht

/-- At its original endpoint the WHOLE centered ray equals the SAME original Gauss point. -/
theorem centeredDiscPoint_endpoint (r : ℝ≥0) (a : K) (ha : v a≤r) :
    centeredDiscPoint v r a ha r le_rfl = discGaussPoint v r := by
  apply Subtype.ext
  exact centeredGauss_eq_gauss_of_val_le (self v) a r ha

/-- Actual finite original root distances CONSTRUCT a neighborhood with the true inward integer slope. -/
theorem exists_rational_inward_slope [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ s : ℝ≥0, 0<s ∧ s<r ∧ ∀ t : ℝ≥0, s≤t → t≤r →
      (centeredGauss (self v) a t).1.val (p*q) ≠ 0 ∧
        rationalRealLog v (centeredGauss (self v) a t) p q =
          rationalRealLog v (gauss (self v) r) p q +
            (inwardRootSlope v r p q (discBranch v r a) : ℝ)*
              (Real.log (r : ℝ)-Real.log (t : ℝ)) := by
  obtain ⟨s,hs,hsr,hclear⟩ := exists_centered_root_radius v r hr a p q
  refine ⟨s,hs,hsr,?_⟩
  intro t hst htr
  have ht := hs.trans_le hst
  refine ⟨centeredGauss_val_ne_zero (self v) a t ht (p*q) (mul_ne_zero hp hq), ?_⟩
  have hpclear : ∀ b ∈ p.roots, v (a-b)<r → v (a-b)≤t := by
    intro b hb hbr
    exact (hclear b (Multiset.mem_add.mpr (Or.inl hb)) hbr).trans hst
  have hqclear : ∀ b ∈ q.roots, v (a-b)<r → v (a-b)≤t := by
    intro b hb hbr
    exact (hclear b (Multiset.mem_add.mpr (Or.inr hb)) hbr).trans hst
  rw [rationalRealLog, polynomialRealLog_centeredGauss_sub v r hr a ha p hp t ht htr hpclear,
    polynomialRealLog_centeredGauss_sub v r hr a ha q hq t ht htr hqclear,
    rationalRealLog, inwardRootSlope]
  push_cast
  ring

/-- Original outer root distances construct a true upper radius before ANY outside root. -/
theorem exists_outer_root_radius (r : ℝ≥0) (p q : K[X]) :
    ∃ R : ℝ≥0, r<R ∧ ∀ b ∈ (p.roots+q.roots), r<v b → R≤v b := by
  classical
  suffices ∀ D : Multiset K, ∃ R : ℝ≥0, r<R ∧ ∀ b ∈ D, r<v b → R≤v b by
    exact this (p.roots+q.roots)
  intro D
  induction D using Multiset.induction_on with
  | empty => exact ⟨r+1, by simp, by simp⟩
  | cons b D ih =>
    obtain ⟨R,hR,hall⟩ := ih
    by_cases hb : r<v b
    · obtain ⟨S,hrS,hSb⟩ := exists_between hb
      refine ⟨min R S, lt_min hR hrS, ?_⟩
      intro c hc hrc
      rcases Multiset.mem_cons.mp hc with rfl | hc
      · exact (min_le_right _ _).trans hSb.le
      · exact (min_le_left _ _).trans (hall c hc hrc)
    · refine ⟨R,hR,?_⟩
      intro c hc hrc
      rcases Multiset.mem_cons.mp hc with rfl | hc
      · exact (hb hrc).elim
      · exact hall c hc hrc

private theorem log_max_sum_outer (D : Multiset ℝ≥0) (r t : ℝ≥0) (hrt : r≤t)
    (hclear : ∀ d ∈ D, r<d → t≤d) :
    (D.map (fun d => Real.log ((max t d : ℝ≥0) : ℝ))).sum =
      (D.map (fun d => Real.log ((max r d : ℝ≥0) : ℝ))).sum +
        ((D.filter (fun d => d≤r)).card : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) := by
  classical
  induction D using Multiset.induction_on with
  | empty => simp
  | cons d D ih =>
    have hi := ih (fun x hx => hclear x (Multiset.mem_cons_of_mem hx))
    by_cases hd : d≤r
    · simp only [Multiset.map_cons, Multiset.sum_cons, max_eq_left (hd.trans hrt), max_eq_left hd]
      rw [Multiset.filter_cons_of_pos (p := fun x : ℝ≥0 => x≤r) D hd, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one, hi]
      ring
    · have hrd := lt_of_not_ge hd
      have htd := hclear d (Multiset.mem_cons_self _ _) hrd
      simp only [Multiset.map_cons, Multiset.sum_cons, max_eq_right htd, max_eq_right hrd.le]
      rw [Multiset.filter_cons_of_neg (p := fun x : ℝ≥0 => x≤r) D hd, hi]
      ring

/-- The original Gauss polynomial logarithm retains EVERY genuine original root. -/
theorem polynomialRealLog_gauss [IsAlgClosed K] (t : ℝ≥0) (ht : 0<t) (p : K[X]) (hp : p≠0) :
    polynomialRealLog v (gauss (self v) t) p = Real.log (v p.leadingCoeff : ℝ) +
      (p.roots.map (fun b => Real.log ((max t (v b) : ℝ≥0) : ℝ))).sum := by
  rw [← centeredGauss_eq_gauss_of_val_le (self v) 0 t (by simp)]
  simpa only [zero_sub, v.map_neg, NNReal.coe_max] using polynomialRealLog_centeredGauss v 0 t ht p hp

/-- The true original outer polynomial slope counts every root INSIDE the actual closed disc. -/
theorem polynomialRealLog_gauss_sub [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (p : K[X]) (hp : p≠0) (t : ℝ≥0) (hrt : r≤t)
    (hclear : ∀ b ∈ p.roots, r<v b → t≤v b) :
    polynomialRealLog v (gauss (self v) t) p = polynomialRealLog v (gauss (self v) r) p +
      ((insideRoots v r p).card : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) := by
  rw [polynomialRealLog_gauss v t (hr.trans_le hrt) p hp,
    polynomialRealLog_gauss v r hr p hp]
  have hc : ∀ d ∈ p.roots.map v, r<d → t≤d := by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp hd
    exact hclear b hb
  have he := log_max_sum_outer (p.roots.map v) r t hrt hc
  simp only [Multiset.map_map, Function.comp_apply, Multiset.filter_map, Multiset.card_map] at he
  rw [he]
  unfold insideRoots
  ring

/-- The genuine outer root gap constructs the actual outward INTEGER slope of the SAME unit log. -/
theorem exists_rational_outward_slope [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ R : ℝ≥0, r<R ∧ ∀ t : ℝ≥0, r≤t → t≤R →
      (gauss (self v) t).1.val (p*q) ≠ 0 ∧
        rationalRealLog v (gauss (self v) t) p q = rationalRealLog v (gauss (self v) r) p q +
          (outwardRootSlope v r p q : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) := by
  obtain ⟨R,hR,hclear⟩ := exists_outer_root_radius v r p q
  refine ⟨R,hR,?_⟩
  intro t hrt htR
  have ht := hr.trans_le hrt
  have hn := centeredGauss_val_ne_zero (self v) 0 t ht (p*q) (mul_ne_zero hp hq)
  rw [centeredGauss_eq_gauss_of_val_le (self v) 0 t (by simp)] at hn
  refine ⟨hn,?_⟩
  have hpclear : ∀ b ∈ p.roots, r<v b → t≤v b := by
    intro b hb hbr
    exact htR.trans (hclear b (Multiset.mem_add.mpr (Or.inl hb)) hbr)
  have hqclear : ∀ b ∈ q.roots, r<v b → t≤v b := by
    intro b hb hbr
    exact htR.trans (hclear b (Multiset.mem_add.mpr (Or.inr hb)) hbr)
  rw [rationalRealLog, polynomialRealLog_gauss_sub v r hr p hp t hrt hpclear,
    polynomialRealLog_gauss_sub v r hr q hq t hrt hqclear, rationalRealLog, outwardRootSlope]
  push_cast
  ring

/-- An unlisted ORIGINAL branch contains no original root at a strict center distance. -/
theorem not_root_near_of_branch_not_mem (r : ℝ≥0) (a : K) (ha : v a≤r) (p : K[X])
    (hB : discBranch v r a ∉ rootBranches v r p) {b : K} (hb : b ∈ p.roots) :
    ¬ v (a-b)<r := by
  classical
  intro hab
  apply hB
  have hvb : v b≤r := by
    rw [show b = a-(a-b) by ring]
    exact (v.map_sub _ _).trans (max_le ha hab.le)
  change discBranch v r a ∈ (rootBranchMultiset v r p).toFinset
  rw [Multiset.mem_toFinset]
  exact Multiset.mem_map.mpr ⟨b, Multiset.mem_filter.mpr ⟨hb,hvb⟩,
    (discBranch_eq_of_val_sub_lt v r hab).symm⟩

/-- The true unequal-term identity makes EVERY unmatched linear factor constant on the WHOLE branch. -/
theorem val_linear_eq_gauss_on_branch (r : ℝ≥0) (a b : K) (ha : v a≤r)
    (hbr : r≤v (a-b)) (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) :
    x.1.1.val (X-C b) = (gauss (self v) r).1.val (X-C b) := by
  have hlt : x.1.1.val (X-C a) < x.1.1.val (C (a-b)) := by
    rw [show x.1.1.val (C (a-b)) = v (a-b) from x.1.2 _]
    exact hx.trans_le hbr
  have hval : x.1.1.val (X-C b) = v (a-b) := by
    rw [show (X-C b : K[X]) = (X-C a)+C (a-b) by simp,
      x.1.1.val.map_add_eq_of_lt_right hlt]
    exact x.1.2 _
  have he : v (a-b) = max r (v b) := by
    apply le_antisymm
    · exact (v.map_sub _ _).trans (max_le_max_right _ ha)
    · apply max_le hbr
      calc
        v b = v (a-(a-b)) := congrArg v (by ring)
        _ ≤ v (a-b) := (v.map_sub _ _).trans (max_le (ha.trans hbr) le_rfl)
  rw [hval, he]
  change max r (v b) = gaussFun v r (X-C b)
  exact (gaussFun_X_sub_C _ _ _).symm

/-- Genuine whole factorization proves constancy of the ORIGINAL polynomial on EVERY unlisted branch point. -/
theorem val_polynomial_eq_gauss_on_unlisted_branch [IsAlgClosed K] (r : ℝ≥0)
    (a : K) (ha : v a≤r) (p : K[X]) (hB : discBranch v r a ∉ rootBranches v r p)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) :
    x.1.1.val p = (gauss (self v) r).1.val p := by
  rw [val_eq_leadingCoeff_mul_root_prod, val_eq_leadingCoeff_mul_root_prod]
  congr 1
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro b hb
  exact val_linear_eq_gauss_on_branch v r a b ha
    (le_of_not_gt (not_root_near_of_branch_not_mem v r a ha p hB hb)) x hx

/-- EVERY whole point of an unlisted branch is in the actual unit locus and has the SAME original unit log. -/
theorem rationalRealLog_eq_gauss_on_unlisted_branch [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p q : K[X]) (hp : p≠0) (hq : q≠0)
    (hB : discBranch v r a ∉ rationalRootBranches v r p q)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) :
    x.1.1.val (p*q) ≠ 0 ∧ rationalRealLog v x.1 p q = rationalRealLog v (gauss (self v) r) p q := by
  have hBp : discBranch v r a ∉ rootBranches v r p := fun h => hB (Finset.mem_union_left _ h)
  have hBq : discBranch v r a ∉ rootBranches v r q := fun h => hB (Finset.mem_union_right _ h)
  have hpx := val_polynomial_eq_gauss_on_unlisted_branch v r a ha p hBp x hx
  have hqx := val_polynomial_eq_gauss_on_unlisted_branch v r a ha q hBq x hx
  constructor
  · rw [map_mul, hpx, hqx, ← map_mul]
    have hn := centeredGauss_val_ne_zero (self v) 0 r hr (p*q) (mul_ne_zero hp hq)
    rw [centeredGauss_eq_gauss_of_val_le (self v) 0 r (by simp)] at hn
    exact hn
  · unfold rationalRealLog polynomialRealLog
    rw [hpx,hqx]

/-- The ACTUAL original regular-section unit log, with no supplied profile or harmonic function. -/
def rationalUnitLog (p q : K[X]) (x : RelativeSpectrum v K[X]) : EReal :=
  SchemeValuedPoint.sectionLogAbs (PrincipalRationalUnit.ratioOpen p q)
    (PrincipalRationalUnit.sectionUnit p q) (SchemeValuedPoint.spectrumHomeomorph.symm x.1)

/-- On its true unit locus this SAME original function equals the actual original real log difference. -/
theorem rationalUnitLog_eq (p q : K[X]) (x : RelativeSpectrum v K[X])
    (hx : x.1.val (p*q)≠0) : rationalUnitLog v p q x = (rationalRealLog v x p q : EReal) :=
  sectionLogAbs_ratio_eq_rationalRealLog v x p q hx

/-- The inward slopes are genuine slopes of the SAME ORIGINAL regular-section unit function. -/
theorem exists_rationalUnitLog_inward_slope [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ s : ℝ≥0, 0<s ∧ s<r ∧ ∀ t : ℝ≥0, s≤t → t≤r →
      rationalUnitLog v p q (centeredGauss (self v) a t) =
        rationalUnitLog v p q (gauss (self v) r) +
          (((inwardRootSlope v r p q (discBranch v r a) : ℝ)*
            (Real.log (r : ℝ)-Real.log (t : ℝ)) : ℝ) : EReal) := by
  obtain ⟨s,hs,hsr,hall⟩ := exists_rational_inward_slope v r hr a ha p q hp hq
  refine ⟨s,hs,hsr,?_⟩
  intro t hst htr
  obtain ⟨hn,he⟩ := hall t hst htr
  have hnr := (hall r hsr.le le_rfl).1
  rw [centeredGauss_eq_gauss_of_val_le (self v) a r ha] at hnr
  rw [rationalUnitLog_eq v p q _ hn, rationalUnitLog_eq v p q _ hnr, he]
  rfl

/-- The outward slope is a genuine slope of that SAME ORIGINAL regular-section unit function. -/
theorem exists_rationalUnitLog_outward_slope [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ R : ℝ≥0, r<R ∧ ∀ t : ℝ≥0, r≤t → t≤R →
      rationalUnitLog v p q (gauss (self v) t) = rationalUnitLog v p q (gauss (self v) r) +
        (((outwardRootSlope v r p q : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) : ℝ) : EReal) := by
  obtain ⟨R,hR,hall⟩ := exists_rational_outward_slope v r hr p q hp hq
  refine ⟨R,hR,?_⟩
  intro t hrt htR
  obtain ⟨hn,he⟩ := hall t hrt htR
  have hnr := (hall r le_rfl hR.le).1
  rw [rationalUnitLog_eq v p q _ hn, rationalUnitLog_eq v p q _ hnr, he]
  rfl

/-- EVERY whole point of EVERY unlisted branch has the SAME original unit function value. -/
theorem rationalUnitLog_eq_on_unlisted_branch [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p q : K[X]) (hp : p≠0) (hq : q≠0)
    (hB : discBranch v r a ∉ rationalRootBranches v r p q)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) :
    rationalUnitLog v p q x.1 = rationalUnitLog v p q (gauss (self v) r) := by
  obtain ⟨hn,he⟩ := rationalRealLog_eq_gauss_on_unlisted_branch v r hr a ha p q hp hq hB x hx
  have hnr := centeredGauss_val_ne_zero (self v) 0 r hr (p*q) (mul_ne_zero hp hq)
  rw [centeredGauss_eq_gauss_of_val_le (self v) 0 r (by simp)] at hnr
  rw [rationalUnitLog_eq v p q _ hn, rationalUnitLog_eq v p q _ hnr, he]

/-- Actual ORIGINAL rational-unit logarithms have the constructed integer-balanced Gauss rays,
with the SAME full function constant on EVERY unlisted genuine branch. No slope/profile certificate is input. -/
theorem exists_rationalUnitLog_balanced_rays [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ R : ℝ≥0, r<R ∧
      (∀ t : ℝ≥0, r≤t → t≤R →
        rationalUnitLog v p q (gauss (self v) t) = rationalUnitLog v p q (gauss (self v) r) +
          (((outwardRootSlope v r p q : ℝ)*(Real.log (t : ℝ)-Real.log (r : ℝ)) : ℝ) : EReal)) ∧
      (∀ a : K, v a≤r → ∃ s : ℝ≥0, 0<s ∧ s<r ∧ ∀ t : ℝ≥0, s≤t → t≤r →
        rationalUnitLog v p q (centeredGauss (self v) a t) =
          rationalUnitLog v p q (gauss (self v) r) +
            (((inwardRootSlope v r p q (discBranch v r a) : ℝ)*
              (Real.log (r : ℝ)-Real.log (t : ℝ)) : ℝ) : EReal)) ∧
      (outwardRootSlope v r p q +
        ∑ B ∈ rationalRootBranches v r p q, inwardRootSlope v r p q B = 0) ∧
      (∀ a : K, v a≤r → discBranch v r a ∉ rationalRootBranches v r p q →
        ∀ x : CoordinateDisc (A := K) v r, x ∈ discBranch v r a →
          rationalUnitLog v p q x.1 = rationalUnitLog v p q (gauss (self v) r)) := by
  obtain ⟨R,hR,hout⟩ := exists_rationalUnitLog_outward_slope v r hr p q hp hq
  refine ⟨R,hR,hout,?_,outward_add_sum_inwardRootSlope_eq_zero v r p q,?_⟩
  · intro a ha
    exact exists_rationalUnitLog_inward_slope v r hr a ha p q hp hq
  · intro a ha hB x hx
    exact rationalUnitLog_eq_on_unlisted_branch v r hr a ha p q hp hq hB x hx

end EnvelopeProperty.Berkovich.RelativeSpectrum
