/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.RationalUnitGaussBalancing

/-! # Entire original rational-unit functions on genuine branch collars -/
open scoped NNReal ENNReal Polynomial
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] (v : Valuation K ℝ≥0)

/-- Genuine root gaps determine the original linear factor on EVERY actual inner-collar point. -/
theorem val_linear_eq_centeredGauss_on_collar (r : ℝ≥0) (a b : K)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a)
    (hgap : v (a-b)<r → v (a-b)<x.1.1.val (X-C a)) :
    x.1.1.val (X-C b) = (centeredGauss (self v) a (x.1.1.val (X-C a))).1.val (X-C b) := by
  rw [centeredGauss_val_X_sub_C_eq_max]
  have he : (X-C b : K[X]) = (X-C a)+C (a-b) := by simp
  by_cases hb : v (a-b)<r
  · have hlt : x.1.1.val (C (a-b)) < x.1.1.val (X-C a) := by
      rw [show x.1.1.val (C (a-b)) = v (a-b) from x.1.2 _]
      exact hgap hb
    rw [he,x.1.1.val.map_add_eq_of_lt_left hlt,max_eq_left (hgap hb).le]
  · have hlt : x.1.1.val (X-C a) < x.1.1.val (C (a-b)) := by
      rw [show x.1.1.val (C (a-b)) = v (a-b) from x.1.2 _]
      exact hx.trans_le (le_of_not_gt hb)
    rw [he,x.1.1.val.map_add_eq_of_lt_right hlt,
      show x.1.1.val (C (a-b)) = v (a-b) from x.1.2 _,
      max_eq_right (hx.le.trans (le_of_not_gt hb))]

/-- Actual split factorization retains EVERY original polynomial value throughout the whole inner collar. -/
theorem val_polynomial_eq_centeredGauss_on_collar [IsAlgClosed K] (r : ℝ≥0) (a : K)
    (p : K[X]) (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a)
    (hgap : ∀ b ∈ p.roots, v (a-b)<r → v (a-b)<x.1.1.val (X-C a)) :
    x.1.1.val p = (centeredGauss (self v) a (x.1.1.val (X-C a))).1.val p := by
  rw [val_eq_leadingCoeff_mul_root_prod,val_eq_leadingCoeff_mul_root_prod]
  congr 1
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro b hb
  exact val_linear_eq_centeredGauss_on_collar v r a b x hx (hgap b hb)

private theorem rationalUnitLog_eq_of_factors (p q : K[X]) (x y : RelativeSpectrum v K[X])
    (hpv : x.1.val p = y.1.val p) (hqv : x.1.val q = y.1.val q) (hy : y.1.val (p*q)≠0) :
    rationalUnitLog v p q x = rationalUnitLog v p q y := by
  have hx : x.1.val (p*q)≠0 := by simpa only [map_mul,hpv,hqv] using hy
  rw [rationalUnitLog_eq v p q x hx,rationalUnitLog_eq v p q y hy]
  unfold rationalRealLog polynomialRealLog
  rw [hpv,hqv]

/-- The SAME ORIGINAL section-unit log has its derived integer form at EVERY genuine inner-collar point. -/
theorem exists_rationalUnitLog_inward_collar [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (a : K) (ha : v a≤r) (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ s : ℝ≥0, 0<s ∧ s<r ∧ ∀ x : CoordinateDisc (A := K) v r,
      x ∈ discBranch v r a → s<x.1.1.val (X-C a) →
        x.1.1.val (p*q)≠0 ∧ rationalUnitLog v p q x.1 = rationalUnitLog v p q (gauss (self v) r) +
          (((inwardRootSlope v r p q (discBranch v r a) : ℝ)*
            (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C a) : ℝ)) : ℝ) : EReal) := by
  obtain ⟨s₁,hs₁,hs₁r,hclear⟩ := exists_centered_root_radius v r hr a p q
  obtain ⟨s₂,hs₂,hs₂r,hray⟩ := exists_rational_inward_slope v r hr a ha p q hp hq
  refine ⟨max s₁ s₂,hs₁.trans_le (le_max_left _ _),max_lt hs₁r hs₂r,?_⟩
  intro x hx hsx
  let t := x.1.1.val (X-C a)
  have ht : 0<t := hs₁.trans ((le_max_left _ _).trans_lt hsx)
  have hgap : ∀ b ∈ p.roots+q.roots, v (a-b)<r → v (a-b)<t := by
    intro b hb hbr
    exact (hclear b hb hbr).trans_lt ((le_max_left _ _).trans_lt hsx)
  have hpx := val_polynomial_eq_centeredGauss_on_collar v r a p x hx
    (fun b hb => hgap b (Multiset.mem_add.mpr (Or.inl hb)))
  have hqx := val_polynomial_eq_centeredGauss_on_collar v r a q x hx
    (fun b hb => hgap b (Multiset.mem_add.mpr (Or.inr hb)))
  have hy := centeredGauss_val_ne_zero (self v) a t ht (p*q) (mul_ne_zero hp hq)
  have hxy := rationalUnitLog_eq_of_factors v p q x.1 (centeredGauss (self v) a t) hpx hqx hy
  have hxn : x.1.1.val (p*q)≠0 := by simpa only [map_mul,hpx,hqx] using hy
  refine ⟨hxn,?_⟩
  rw [hxy,rationalUnitLog_eq v p q _ hy,
    (hray t ((le_max_right _ _).trans hsx.le) hx.le).2]
  have hyr := (hray r hs₂r.le le_rfl).1
  rw [centeredGauss_eq_gauss_of_val_le (self v) a r ha] at hyr
  rw [rationalUnitLog_eq v p q _ hyr]
  rfl

/-- Genuine outside-root gaps determine the original factor at EVERY actual outer-collar point. -/
theorem val_linear_eq_gauss_on_outer_collar (r : ℝ≥0) (b : K) (x : RelativeSpectrum v K[X])
    (hx : r<x.1.val X) (hgap : r<v b → x.1.val X<v b) :
    x.1.val (X-C b) = (gauss (self v) (x.1.val X)).1.val (X-C b) := by
  change x.1.val (X-C b) = gaussFun v (x.1.val X) (X-C b)
  rw [gaussFun_X_sub_C]
  by_cases hb : v b≤r
  · have hlt : x.1.val (C b)<x.1.val X := by
      rw [show x.1.val (C b) = v b from x.2 _]
      exact hb.trans_lt hx
    rw [x.1.val.map_sub_eq_of_lt_left hlt,max_eq_left (hb.trans hx.le)]
  · have hlt : x.1.val X<x.1.val (C b) := by
      rw [show x.1.val (C b) = v b from x.2 _]
      exact hgap (lt_of_not_ge hb)
    rw [x.1.val.map_sub_eq_of_lt_right hlt,show x.1.val (C b) = v b from x.2 _,
      max_eq_right (hgap (lt_of_not_ge hb)).le]

/-- Whole original split factorization extends the outer Gauss identity to EVERY collar point. -/
theorem val_polynomial_eq_gauss_on_outer_collar [IsAlgClosed K] (r : ℝ≥0) (p : K[X])
    (x : RelativeSpectrum v K[X]) (hx : r<x.1.val X)
    (hgap : ∀ b ∈ p.roots, r<v b → x.1.val X<v b) :
    x.1.val p = (gauss (self v) (x.1.val X)).1.val p := by
  rw [val_eq_leadingCoeff_mul_root_prod,val_eq_leadingCoeff_mul_root_prod]
  congr 1
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro b hb
  exact val_linear_eq_gauss_on_outer_collar v r b x hx (hgap b hb)

/-- The SAME ORIGINAL unit function has its derived integer form at EVERY genuine outer-collar point. -/
theorem exists_rationalUnitLog_outward_collar [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r)
    (p q : K[X]) (hp : p≠0) (hq : q≠0) :
    ∃ R : ℝ≥0, r<R ∧ ∀ x : RelativeSpectrum v K[X], r<x.1.val X → x.1.val X<R →
      x.1.val (p*q)≠0 ∧ rationalUnitLog v p q x = rationalUnitLog v p q (gauss (self v) r) +
        (((outwardRootSlope v r p q : ℝ)*(Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)) : ℝ) : EReal) := by
  obtain ⟨R₁,hR₁,hclear⟩ := exists_outer_root_radius v r p q
  obtain ⟨R₂,hR₂,hray⟩ := exists_rational_outward_slope v r hr p q hp hq
  refine ⟨min R₁ R₂,lt_min hR₁ hR₂,?_⟩
  intro x hrx hxR
  let t := x.1.val X
  have hgap : ∀ b ∈ p.roots+q.roots, r<v b → t<v b := by
    intro b hb hbr
    exact (hxR.trans_le (min_le_left _ _)).trans_le (hclear b hb hbr)
  have hpx := val_polynomial_eq_gauss_on_outer_collar v r p x hrx
    (fun b hb => hgap b (Multiset.mem_add.mpr (Or.inl hb)))
  have hqx := val_polynomial_eq_gauss_on_outer_collar v r q x hrx
    (fun b hb => hgap b (Multiset.mem_add.mpr (Or.inr hb)))
  obtain ⟨hy,he⟩ := hray t hrx.le (hxR.le.trans (min_le_right _ _))
  have hxy := rationalUnitLog_eq_of_factors v p q x (gauss (self v) t) hpx hqx hy
  have hxn : x.1.val (p*q)≠0 := by simpa only [map_mul,hpx,hqx] using hy
  refine ⟨hxn,?_⟩
  have hyr := (hray r le_rfl hR₂.le).1
  rw [hxy,rationalUnitLog_eq v p q _ hy,he,rationalUnitLog_eq v p q _ hyr]
  rfl

/-- The actual finite original root CENTERS behind the true finite branch-set family. -/
def insideRootCenters (r : ℝ≥0) (p q : K[X]) : Finset K := by
  classical
  exact (insideRoots v r p + insideRoots v r q).toFinset

/-- EVERY listed original center is genuinely inside the SAME closed disc. -/
theorem val_le_of_mem_insideRootCenters (r : ℝ≥0) (p q : K[X]) {b : K}
    (hb : b ∈ insideRootCenters v r p q) : v b≤r := by
  classical
  change b ∈ (insideRoots v r p+insideRoots v r q).toFinset at hb
  rw [Multiset.mem_toFinset,Multiset.mem_add] at hb
  rcases hb with hb | hb <;> exact (Multiset.mem_filter.mp hb).2

/-- The genuine finite branch family is EXACTLY the image of these original root centers. -/
theorem mem_rationalRootBranches_iff (r : ℝ≥0) (p q : K[X])
    (B : Set (CoordinateDisc (A := K) v r)) :
    B ∈ rationalRootBranches v r p q ↔ ∃ b ∈ insideRootCenters v r p q, discBranch v r b = B := by
  classical
  simp only [rationalRootBranches,rootBranches,rootBranchMultiset,insideRootCenters,
    Finset.mem_union,Multiset.mem_toFinset,Multiset.mem_add,Multiset.mem_map]
  constructor
  · rintro (⟨b,hb,hB⟩ | ⟨b,hb,hB⟩)
    · exact ⟨b,Or.inl hb,hB⟩
    · exact ⟨b,Or.inr hb,hB⟩
  · rintro ⟨b,hb,hB⟩
    rcases hb with hb | hb
    · exact Or.inl ⟨b,hb,hB⟩
    · exact Or.inr ⟨b,hb,hB⟩

namespace RationalUnitCollar
variable [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r) (p q : K[X]) (hp : p≠0) (hq : q≠0)

/-- The inner radius is CONSTRUCTED from original finite root gaps, never supplied as a profile. -/
def innerRadius (b : K) : ℝ≥0 :=
  if hb : v b≤r then (exists_rationalUnitLog_inward_collar v r hr b hb p q hp hq).choose else 0

/-- Every original in-disc center has a genuinely positive constructed collar radius. -/
theorem innerRadius_pos (b : K) (hb : v b≤r) : 0 < innerRadius v r hr p q hp hq b := by
  simp only [innerRadius,dif_pos hb]
  exact (exists_rationalUnitLog_inward_collar v r hr b hb p q hp hq).choose_spec.1

/-- The actual constructed inner radius lies STRICTLY below the original Gauss radius. -/
theorem innerRadius_lt (b : K) (hb : v b≤r) : innerRadius v r hr p q hp hq b<r := by
  simp only [innerRadius,dif_pos hb]
  exact (exists_rationalUnitLog_inward_collar v r hr b hb p q hp hq).choose_spec.2.1

/-- The actual outer radius is likewise CONSTRUCTED from original finite root gaps. -/
def outerRadius : ℝ≥0 := (exists_rationalUnitLog_outward_collar v r hr p q hp hq).choose

/-- The constructed outer collar extends genuinely beyond the original Gauss radius. -/
theorem lt_outerRadius : r<outerRadius v r hr p q hp hq :=
  (exists_rationalUnitLog_outward_collar v r hr p q hp hq).choose_spec.1

/-- The TRUE whole original point neighborhood is cut out by finitely many genuine strict section inequalities. -/
def neighborhood : Set (RelativeSpectrum v K[X]) :=
  {x | x.1.val X<outerRadius v r hr p q hp hq ∧
    ∀ b ∈ insideRootCenters v r p q, innerRadius v r hr p q hp hq b<x.1.val (X-C b)}

/-- The constructed collar neighborhood is actually OPEN in the original point space. -/
theorem isOpen_neighborhood : IsOpen (neighborhood v r hr p q hp hq) := by
  have hV : IsOpen {x : RelativeSpectrum v K[X] |
      ∀ b ∈ insideRootCenters v r p q, innerRadius v r hr p q hp hq b<x.1.val (X-C b)} := by
    simp only [Set.ofPred_forall]
    apply isOpen_biInter_finset
    intro b hb
    exact isOpen_lt continuous_const ((Spectrum.continuous_val_apply _).comp continuous_subtype_val)
  exact (isOpen_lt ((Spectrum.continuous_val_apply X).comp continuous_subtype_val) continuous_const).inter hV

/-- The ORIGINAL whole Gauss point belongs to the actual constructed open neighborhood. -/
theorem gauss_mem_neighborhood : gauss (self v) r ∈ neighborhood v r hr p q hp hq := by
  refine ⟨?_,?_⟩
  · change (gauss (self v) r).1.val X<_
    rw [← val_apply,gauss_val_X]
    exact lt_outerRadius v r hr p q hp hq
  · intro b hb
    have hvb := val_le_of_mem_insideRootCenters v r p q hb
    change innerRadius v r hr p q hp hq b<gaussFun v r (X-C b)
    rw [gaussFun_X_sub_C,max_eq_left hvb]
    exact innerRadius_lt v r hr p q hp hq b hvb

/-- At ANY actual in-disc center the CONSTRUCTED radius gives the whole original unit collar formula. -/
theorem unitLog_on_branch (b : K) (hb : v b≤r)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r b)
    (hxb : innerRadius v r hr p q hp hq b<x.1.1.val (X-C b)) :
    x.1.1.val (p*q)≠0 ∧ rationalUnitLog v p q x.1 = rationalUnitLog v p q (gauss (self v) r) +
      (((inwardRootSlope v r p q (discBranch v r b) : ℝ)*
        (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ)) : ℝ) : EReal) := by
  apply (exists_rationalUnitLog_inward_collar v r hr b hb p q hp hq).choose_spec.2.2 x hx
  simpa only [innerRadius,dif_pos hb] using hxb

/-- Every WHOLE listed-branch point in the genuine neighborhood has its actual original collar formula. -/
theorem unitLog_on_listed_branch (b : K) (hb : b ∈ insideRootCenters v r p q)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r b)
    (hxN : x.1 ∈ neighborhood v r hr p q hp hq) :
    x.1.1.val (p*q)≠0 ∧ rationalUnitLog v p q x.1 = rationalUnitLog v p q (gauss (self v) r) +
      (((inwardRootSlope v r p q (discBranch v r b) : ℝ)*
        (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ)) : ℝ) : EReal) := by
  have hvb := val_le_of_mem_insideRootCenters v r p q hb
  have he := (exists_rationalUnitLog_inward_collar v r hr b hvb p q hp hq).choose_spec.2.2
  apply he x hx
  have hN := hxN.2 b hb
  simpa only [innerRadius,dif_pos hvb] using hN

/-- Every WHOLE outer point of the genuine neighborhood has the actual original outer collar formula. -/
theorem unitLog_on_outer (x : RelativeSpectrum v K[X]) (hx : r<x.1.val X)
    (hxN : x ∈ neighborhood v r hr p q hp hq) :
    x.1.val (p*q)≠0 ∧ rationalUnitLog v p q x = rationalUnitLog v p q (gauss (self v) r) +
      (((outwardRootSlope v r p q : ℝ)*(Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)) : ℝ) : EReal) :=
  (exists_rationalUnitLog_outward_collar v r hr p q hp hq).choose_spec.2 x hx hxN.1

/-- ALL points of this ACTUAL open neighborhood lie in the ORIGINAL regular-section unit locus. -/
theorem val_mul_ne_zero_on_neighborhood (x : RelativeSpectrum v K[X])
    (hxN : x ∈ neighborhood v r hr p q hp hq) : x.1.val (p*q)≠0 := by
  classical
  by_cases hxr : x.1.val X≤r
  · let z : CoordinateDisc (A := K) v r := ⟨x,hxr⟩
    by_cases hz : z=discGaussPoint v r
    · have hxg : x=gauss (self v) r := congrArg Subtype.val hz
      rw [hxg]
      have hn := centeredGauss_val_ne_zero (self v) 0 r hr (p*q) (mul_ne_zero hp hq)
      rw [centeredGauss_eq_gauss_of_val_le (self v) 0 r (by simp)] at hn
      exact hn
    · obtain ⟨a,ha,hza⟩ := exists_mem_discBranch_of_ne_gauss r z hz
      by_cases hB : discBranch v r a ∈ rationalRootBranches v r p q
      · obtain ⟨b,hb,hba⟩ := (mem_rationalRootBranches_iff v r p q _).mp hB
        have hzb : z ∈ discBranch v r b := hba.symm ▸ hza
        exact (unitLog_on_listed_branch v r hr p q hp hq b hb z hzb hxN).1
      · exact (rationalRealLog_eq_gauss_on_unlisted_branch v r hr a ha p q hp hq hB z hza).1
  · exact (unitLog_on_outer v r hr p q hp hq x (lt_of_not_ge hxr) hxN).1

end RationalUnitCollar

end EnvelopeProperty.Berkovich.RelativeSpectrum
