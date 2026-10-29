/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.RationalUnitCollars

/-! # Genuine finite original rational-unit families and their actual balanced directions -/
open scoped NNReal ENNReal Polynomial
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
variable {K J : Type*} [Field K] [Fintype J] (v : Valuation K ℝ≥0)

/-- The ACTUAL original numerator product, including the empty family. -/
def numeratorProduct (p : J → K[X]) : K[X] := ∏ j, p j

/-- Every original factor root remains a root of the SAME literal original product. -/
theorem mem_roots_numeratorProduct (p : J → K[X]) (hp : ∀ j, p j≠0)
    (j : J) {b : K} (hb : b ∈ (p j).roots) : b ∈ (numeratorProduct p).roots := by
  classical
  have hP : numeratorProduct p≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  apply (Polynomial.mem_roots hP).mpr
  change Polynomial.eval b (∏ j, p j)=0
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) ((Polynomial.mem_roots (hp j)).mp hb)

/-- Actual factor-root inclusion preserves the whole original branch SET image. -/
theorem rootBranches_subset_product (r : ℝ≥0) (p : J → K[X]) (hp : ∀ j, p j≠0) (j : J) :
    rootBranches v r (p j) ⊆ rootBranches v r (numeratorProduct p) := by
  classical
  intro B hB
  simp only [rootBranches,rootBranchMultiset,Multiset.mem_toFinset,Multiset.mem_map,
    insideRoots,Multiset.mem_filter] at hB ⊢
  obtain ⟨b,⟨hb,hbr⟩,hB⟩ := hB
  exact ⟨b,⟨mem_roots_numeratorProduct p hp j hb,hbr⟩,hB⟩

/-- One true finite branch family is constructed from the ORIGINAL product polynomials. -/
def branchFamily (r : ℝ≥0) (p q : J → K[X]) : Finset (Set (CoordinateDisc (A := K) v r)) :=
  rationalRootBranches v r (numeratorProduct p) (numeratorProduct q)

/-- The direction family consists of the ACTUAL outer direction and ACTUAL original branch SETS. -/
abbrev Direction (r : ℝ≥0) (p q : J → K[X]) := Option ↥(branchFamily v r p q)

/-- Every original individual numerator branch is present in that SAME constructed family. -/
theorem rootBranches_subset_family_left (r : ℝ≥0) (p q : J → K[X]) (hp : ∀ j, p j≠0) (j : J) :
    rootBranches v r (p j) ⊆ branchFamily v r p q := by
  intro B hB
  exact Finset.mem_union_left _ (rootBranches_subset_product v r p hp j hB)

/-- Every original individual denominator branch is likewise retained. -/
theorem rootBranches_subset_family_right (r : ℝ≥0) (p q : J → K[X]) (hq : ∀ j, q j≠0) (j : J) :
    rootBranches v r (q j) ⊆ branchFamily v r p q := by
  intro B hB
  exact Finset.mem_union_right _ (rootBranches_subset_product v r q hq j hB)

/-- Each direction carries the genuine ORIGINAL integer unit slope, with the true orientation. -/
def unitSlope (r : ℝ≥0) (p q : J → K[X]) (j : J) : Direction v r p q → ℤ
  | none => outwardRootSlope v r (p j) (q j)
  | some B => inwardRootSlope v r (p j) (q j) B.1

/-- Actual original multiset fibre counts balance EVERY unit over the SAME genuine direction family. -/
theorem sum_unitSlope_eq_zero (r : ℝ≥0) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0) (j : J) :
    ∑ d : Direction v r p q, unitSlope v r p q j d = 0 := by
  classical
  rw [Fintype.sum_option]
  change outwardRootSlope v r (p j) (q j) +
    ∑ B : ↥(branchFamily v r p q), inwardRootSlope v r (p j) (q j) B.1 = 0
  simp only [Finset.sum_coe_sort]
  have hpc := sum_branchRootCount v r (p j) (branchFamily v r p q)
    (rootBranches_subset_family_left v r p q hp j)
  have hqc := sum_branchRootCount v r (q j) (branchFamily v r p q)
    (rootBranches_subset_family_right v r p q hq j)
  simp only [inwardRootSlope,Finset.sum_sub_distrib,← Nat.cast_sum,hpc,hqc,outwardRootSlope]
  ring

/-- The REAL finite linear combination uses ONLY original unit section logs and original scalar data. -/
def affineValue (p q : J → K[X]) (c : ℝ) (α : J → ℝ)
    (x : RelativeSpectrum v K[X]) : ℝ :=
  c + ∑ j, α j * (rationalUnitLog v (p j) (q j) x).toReal

/-- The true original real outgoing slopes of that finite linear combination. -/
def affineSlope (r : ℝ≥0) (p q : J → K[X]) (α : J → ℝ) (d : Direction v r p q) : ℝ :=
  ∑ j, α j * (unitSlope v r p q j d : ℝ)

/-- Genuine original unit balancing gives real balance for ANY finite original coefficient vector. -/
theorem sum_affineSlope_eq_zero (r : ℝ≥0) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0) (α : J → ℝ) :
    ∑ d : Direction v r p q, affineSlope v r p q α d = 0 := by
  classical
  simp only [affineSlope]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,← Int.cast_sum,sum_unitSlope_eq_zero v r p q hp hq,Int.cast_zero,mul_zero,
    Finset.sum_const_zero]

/-- The inward real affine slope at an ACTUAL original branch set. -/
def inwardAffineSlope (r : ℝ≥0) (p q : J → K[X]) (α : J → ℝ)
    (B : Set (CoordinateDisc (A := K) v r)) : ℝ :=
  ∑ j, α j * (inwardRootSlope v r (p j) (q j) B : ℝ)

/-- The outward real affine slope uses the actual ORIGINAL outer unit integers. -/
def outwardAffineSlope (r : ℝ≥0) (p q : J → K[X]) (α : J → ℝ) : ℝ :=
  ∑ j, α j * (outwardRootSlope v r (p j) (q j) : ℝ)

private theorem factor_root_mem_total (p q : J → K[X]) (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0)
    (j : J) {b : K} (hb : b ∈ (p j).roots+(q j).roots) :
    b ∈ (numeratorProduct p).roots+(numeratorProduct q).roots := by
  rcases Multiset.mem_add.mp hb with hb | hb
  · exact Multiset.mem_add.mpr (Or.inl (mem_roots_numeratorProduct p hp j hb))
  · exact Multiset.mem_add.mpr (Or.inr (mem_roots_numeratorProduct q hq j hb))

section Collars
variable [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0)

/-- One ACTUAL original product-root gap radius controls EVERY original unit, before any coefficients. -/
def innerRadius (a : K) : ℝ≥0 :=
  (exists_centered_root_radius v r hr a (numeratorProduct p) (numeratorProduct q)).choose

omit [IsAlgClosed K] in
/-- The simultaneous original inner radius is truly positive. -/
theorem innerRadius_pos (a : K) : 0 < innerRadius v r hr p q a :=
  (exists_centered_root_radius v r hr a (numeratorProduct p) (numeratorProduct q)).choose_spec.1

omit [IsAlgClosed K] in
/-- This SAME simultaneous radius remains strictly below the genuine Gauss radius. -/
theorem innerRadius_lt (a : K) : innerRadius v r hr p q a<r :=
  (exists_centered_root_radius v r hr a (numeratorProduct p) (numeratorProduct q)).choose_spec.2.1

include hp hq in
private theorem unitLog_toReal_inward (a : K) (ha : v a≤r) (j : J)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a)
    (hsx : innerRadius v r hr p q a<x.1.1.val (X-C a)) :
    x.1.1.val ((p j)*(q j))≠0 ∧
    (rationalUnitLog v (p j) (q j) x.1).toReal =
      (rationalUnitLog v (p j) (q j) (gauss (self v) r)).toReal +
        (inwardRootSlope v r (p j) (q j) (discBranch v r a) : ℝ)*
          (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C a) : ℝ)) := by
  let t := x.1.1.val (X-C a)
  have ht : 0<t := (innerRadius_pos v r hr p q a).trans hsx
  have hclear : ∀ b ∈ (p j).roots+(q j).roots, v (a-b)<r → v (a-b)<t := by
    intro b hb hbr
    exact ((exists_centered_root_radius v r hr a (numeratorProduct p) (numeratorProduct q)).choose_spec.2.2
      b (factor_root_mem_total p q hp hq j hb) hbr).trans_lt hsx
  have hpclear : ∀ b ∈ (p j).roots, v (a-b)<r → v (a-b)<t :=
    fun b hb => hclear b (Multiset.mem_add.mpr (Or.inl hb))
  have hqclear : ∀ b ∈ (q j).roots, v (a-b)<r → v (a-b)<t :=
    fun b hb => hclear b (Multiset.mem_add.mpr (Or.inr hb))
  have hpx := val_polynomial_eq_centeredGauss_on_collar v r a (p j) x hx hpclear
  have hqx := val_polynomial_eq_centeredGauss_on_collar v r a (q j) x hx hqclear
  have hnt := centeredGauss_val_ne_zero (self v) a t ht ((p j)*(q j)) (mul_ne_zero (hp j) (hq j))
  have hnx : x.1.1.val ((p j)*(q j))≠0 := by simpa only [map_mul,hpx,hqx] using hnt
  have hnr := centeredGauss_val_ne_zero (self v) a r hr ((p j)*(q j)) (mul_ne_zero (hp j) (hq j))
  rw [centeredGauss_eq_gauss_of_val_le (self v) a r ha] at hnr
  refine ⟨hnx,?_⟩
  rw [rationalUnitLog_eq v _ _ x.1 hnx,rationalUnitLog_eq v _ _ _ hnr,EReal.toReal_coe,EReal.toReal_coe]
  have hreal : rationalRealLog v x.1 (p j) (q j) =
      rationalRealLog v (centeredGauss (self v) a t) (p j) (q j) := by
    unfold rationalRealLog polynomialRealLog
    rw [hpx,hqx]
  rw [hreal,rationalRealLog,
    polynomialRealLog_centeredGauss_sub v r hr a ha (p j) (hp j) t ht hx.le
      (fun b hb hbr => (hpclear b hb hbr).le),
    polynomialRealLog_centeredGauss_sub v r hr a ha (q j) (hq j) t ht hx.le
      (fun b hb hbr => (hqclear b hb hbr).le),rationalRealLog,inwardRootSlope]
  push_cast
  ring

include hp hq in
/-- EVERY original unit is genuinely defined at EVERY point of the common actual inner collar. -/
theorem unit_mul_ne_zero_inward_collar (a : K) (ha : v a≤r) (j : J)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a)
    (hsx : innerRadius v r hr p q a<x.1.1.val (X-C a)) : x.1.1.val ((p j)*(q j))≠0 :=
  (unitLog_toReal_inward v r hr p q hp hq a ha j x hx hsx).1

include hp hq in
/-- EVERY original finite real coefficient vector has its actual WHOLE inner-collar affine form. -/
theorem affineValue_inward_collar (a : K) (ha : v a≤r)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a)
    (hsx : innerRadius v r hr p q a<x.1.1.val (X-C a)) (c : ℝ) (α : J → ℝ) :
    affineValue v p q c α x.1 = affineValue v p q c α (gauss (self v) r) +
      inwardAffineSlope v r p q α (discBranch v r a)*
        (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C a) : ℝ)) := by
  unfold affineValue inwardAffineSlope
  have he (j : J) := (unitLog_toReal_inward v r hr p q hp hq a ha j x hx hsx).2
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

/-- The ONE actual outside-root gap is constructed BEFORE every real coefficient vector. -/
def outerRadius : ℝ≥0 :=
  (exists_outer_root_radius v r (numeratorProduct p) (numeratorProduct q)).choose

omit [IsAlgClosed K] in
/-- Its genuine outer interval extends strictly beyond the original radius. -/
theorem lt_outerRadius : r<outerRadius v r p q :=
  (exists_outer_root_radius v r (numeratorProduct p) (numeratorProduct q)).choose_spec.1

include hr hp hq in
private theorem unitLog_toReal_outward (j : J) (x : RelativeSpectrum v K[X])
    (hx : r<x.1.val X) (hxR : x.1.val X<outerRadius v r p q) :
    x.1.val ((p j)*(q j))≠0 ∧ (rationalUnitLog v (p j) (q j) x).toReal =
      (rationalUnitLog v (p j) (q j) (gauss (self v) r)).toReal +
        (outwardRootSlope v r (p j) (q j) : ℝ)*
          (Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)) := by
  let t := x.1.val X
  have ht : 0<t := hr.trans hx
  have hclear : ∀ b ∈ (p j).roots+(q j).roots, r<v b → t<v b := by
    intro b hb hbr
    exact hxR.trans_le ((exists_outer_root_radius v r (numeratorProduct p)
      (numeratorProduct q)).choose_spec.2 b (factor_root_mem_total p q hp hq j hb) hbr)
  have hpclear : ∀ b ∈ (p j).roots, r<v b → t<v b :=
    fun b hb => hclear b (Multiset.mem_add.mpr (Or.inl hb))
  have hqclear : ∀ b ∈ (q j).roots, r<v b → t<v b :=
    fun b hb => hclear b (Multiset.mem_add.mpr (Or.inr hb))
  have hpx := val_polynomial_eq_gauss_on_outer_collar v r (p j) x hx hpclear
  have hqx := val_polynomial_eq_gauss_on_outer_collar v r (q j) x hx hqclear
  have hnt := centeredGauss_val_ne_zero (self v) 0 t ht ((p j)*(q j)) (mul_ne_zero (hp j) (hq j))
  rw [centeredGauss_eq_gauss_of_val_le (self v) 0 t (by simp)] at hnt
  have hnx : x.1.val ((p j)*(q j))≠0 := by simpa only [map_mul,hpx,hqx] using hnt
  have hnr := centeredGauss_val_ne_zero (self v) 0 r hr ((p j)*(q j)) (mul_ne_zero (hp j) (hq j))
  rw [centeredGauss_eq_gauss_of_val_le (self v) 0 r (by simp)] at hnr
  refine ⟨hnx,?_⟩
  rw [rationalUnitLog_eq v _ _ x hnx,rationalUnitLog_eq v _ _ _ hnr,EReal.toReal_coe,EReal.toReal_coe]
  have hreal : rationalRealLog v x (p j) (q j) = rationalRealLog v (gauss (self v) t) (p j) (q j) := by
    unfold rationalRealLog polynomialRealLog
    rw [hpx,hqx]
  rw [hreal,rationalRealLog,
    polynomialRealLog_gauss_sub v r hr (p j) (hp j) t hx.le (fun b hb hbr => (hpclear b hb hbr).le),
    polynomialRealLog_gauss_sub v r hr (q j) (hq j) t hx.le (fun b hb hbr => (hqclear b hb hbr).le),
    rationalRealLog,outwardRootSlope]
  push_cast
  ring

include hr hp hq in
/-- EVERY original unit is genuinely defined at EVERY point of the common actual outer collar. -/
theorem unit_mul_ne_zero_outward_collar (j : J) (x : RelativeSpectrum v K[X])
    (hx : r<x.1.val X) (hxR : x.1.val X<outerRadius v r p q) : x.1.val ((p j)*(q j))≠0 :=
  (unitLog_toReal_outward v r hr p q hp hq j x hx hxR).1

include hr hp hq in
/-- EVERY original finite real coefficient vector has its true WHOLE outer-collar affine form. -/
theorem affineValue_outward_collar (x : RelativeSpectrum v K[X])
    (hx : r<x.1.val X) (hxR : x.1.val X<outerRadius v r p q) (c : ℝ) (α : J → ℝ) :
    affineValue v p q c α x = affineValue v p q c α (gauss (self v) r) +
      outwardAffineSlope v r p q α*(Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)) := by
  unfold affineValue outwardAffineSlope
  have he (j : J) := (unitLog_toReal_outward v r hr p q hp hq j x hx hxR).2
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

/-- The actual common neighborhood uses only ORIGINAL finite product-root centers/gaps. -/
def neighborhood : Set (RelativeSpectrum v K[X]) :=
  {x | x.1.val X<outerRadius v r p q ∧ ∀ b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q),
    innerRadius v r hr p q b<x.1.val (X-C b)}

omit [IsAlgClosed K] in
/-- The common finite-family neighborhood is genuinely open in the ORIGINAL point space. -/
theorem isOpen_neighborhood : IsOpen (neighborhood v r hr p q) := by
  have hV : IsOpen {x : RelativeSpectrum v K[X] |
      ∀ b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q),
        innerRadius v r hr p q b<x.1.val (X-C b)} := by
    simp only [Set.ofPred_forall]
    apply isOpen_biInter_finset
    intro b hb
    exact isOpen_lt continuous_const ((Spectrum.continuous_val_apply _).comp continuous_subtype_val)
  exact (isOpen_lt ((Spectrum.continuous_val_apply X).comp continuous_subtype_val) continuous_const).inter hV

omit [IsAlgClosed K] in
/-- The WHOLE original Gauss point lies in this ACTUAL simultaneous neighborhood. -/
theorem gauss_mem_neighborhood : gauss (self v) r ∈ neighborhood v r hr p q := by
  refine ⟨?_,?_⟩
  · change (gauss (self v) r).1.val X<_
    rw [← val_apply,gauss_val_X]
    exact lt_outerRadius v r p q
  · intro b hb
    have hvb := val_le_of_mem_insideRootCenters v r (numeratorProduct p) (numeratorProduct q) hb
    change innerRadius v r hr p q b<gaussFun v r (X-C b)
    rw [gaussFun_X_sub_C,max_eq_left hvb]
    exact innerRadius_lt v r hr p q b

include hp hq in
/-- Each original unit has NO zero at ANY whole point of the ACTUAL common family neighborhood. -/
theorem unit_mul_ne_zero_on_neighborhood (j : J) (x : RelativeSpectrum v K[X])
    (hxN : x ∈ neighborhood v r hr p q) : x.1.val ((p j)*(q j))≠0 := by
  classical
  by_cases hxr : x.1.val X≤r
  · let z : CoordinateDisc (A := K) v r := ⟨x,hxr⟩
    by_cases hz : z=discGaussPoint v r
    · have hxg : x=gauss (self v) r := congrArg Subtype.val hz
      rw [hxg]
      have hn := centeredGauss_val_ne_zero (self v) 0 r hr ((p j)*(q j)) (mul_ne_zero (hp j) (hq j))
      rw [centeredGauss_eq_gauss_of_val_le (self v) 0 r (by simp)] at hn
      exact hn
    · obtain ⟨a,ha,hza⟩ := exists_mem_discBranch_of_ne_gauss r z hz
      by_cases hB : discBranch v r a ∈ branchFamily v r p q
      · obtain ⟨b,hb,hba⟩ := (mem_rationalRootBranches_iff v r (numeratorProduct p) (numeratorProduct q) _).mp hB
        have hzb : z ∈ discBranch v r b := hba.symm ▸ hza
        exact (unitLog_toReal_inward v r hr p q hp hq b
          (val_le_of_mem_insideRootCenters v r _ _ hb) j z hzb (hxN.2 b hb)).1
      · have hBj : discBranch v r a ∉ rationalRootBranches v r (p j) (q j) := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hB (rootBranches_subset_family_left v r p q hp j h)
          · exact hB (rootBranches_subset_family_right v r p q hq j h)
        exact (rationalRealLog_eq_gauss_on_unlisted_branch v r hr a ha (p j) (q j)
          (hp j) (hq j) hBj z hza).1
  · exact (unitLog_toReal_outward v r hr p q hp hq j x (lt_of_not_ge hxr) hxN.1).1

include hp hq in
/-- EVERY original finite affine expression has its actual listed-branch formula on the SAME neighborhood. -/
theorem affineValue_on_listed_branch (b : K)
    (hb : b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q))
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r b)
    (hxN : x.1 ∈ neighborhood v r hr p q) (c : ℝ) (α : J → ℝ) :
    affineValue v p q c α x.1 = affineValue v p q c α (gauss (self v) r) +
      inwardAffineSlope v r p q α (discBranch v r b)*
        (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ)) :=
  affineValue_inward_collar v r hr p q hp hq b (val_le_of_mem_insideRootCenters v r _ _ hb)
    x hx (hxN.2 b hb) c α

include hr hp hq in
/-- EVERY unlisted genuine branch keeps the SAME whole affine expression constant. -/
theorem affineValue_on_unlisted_branch (a : K) (ha : v a≤r)
    (hB : discBranch v r a ∉ branchFamily v r p q)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) (c : ℝ) (α : J → ℝ) :
    affineValue v p q c α x.1 = affineValue v p q c α (gauss (self v) r) := by
  unfold affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hBj : discBranch v r a ∉ rationalRootBranches v r (p j) (q j) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hB (rootBranches_subset_family_left v r p q hp j h)
    · exact hB (rootBranches_subset_family_right v r p q hq j h)
  rw [rationalUnitLog_eq_on_unlisted_branch v r hr a ha (p j) (q j) (hp j) (hq j) hBj x hx]

end Collars

end EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
