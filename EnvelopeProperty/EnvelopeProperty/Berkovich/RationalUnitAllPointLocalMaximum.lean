/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.RationalUnitGaussLocalMaximum
import EnvelopeProperty.Berkovich.FiniteRootNeighborhoods

/-! # Actual all-point local constancy of original finite rational-unit maxima -/
open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
variable {K J ι : Type*} [Field K] [Fintype J] (v : Valuation K ℝ≥0)

omit [Fintype J] in
/-- The ORIGINAL family is translated by the genuine whole polynomial algebra equivalence. -/
def translatedFamily (a : K) (p : J → K[X]) : J → K[X] :=
  fun j => Polynomial.algEquivAevalXAddC a (p j)

omit [Fintype J] in
/-- Actual polynomial translation retains every ORIGINAL nonzero polynomial. -/
theorem translatedFamily_ne_zero (a : K) (p : J → K[X]) (hp : ∀ j, p j≠0) (j : J) :
    translatedFamily a p j≠0 := fun h => hp j ((Polynomial.algEquivAevalXAddC a).injective (h.trans (map_zero _).symm))

private theorem translation_value (a : K) (z : RelativeSpectrum v K[X]) (p : K[X]) :
    (polynomialTranslation a z).1.val p=z.1.val (Polynomial.algEquivAevalXAddC a p) := by
  rw [← val_apply,polynomialTranslation_val_apply]

/-- True nonvanishing is preserved on the SAME whole original translated point. -/
theorem unit_mul_ne_zero_translation (a : K) (p q : K[X]) (z : RelativeSpectrum v K[X])
    (hz : z.1.val (Polynomial.algEquivAevalXAddC a p*Polynomial.algEquivAevalXAddC a q)≠0) :
    (polynomialTranslation a z).1.val (p*q)≠0 := by
  rwa [translation_value,map_mul]

/-- On the PROVED actual unit locus, whole translation retains the SAME original section-unit logarithm. -/
theorem rationalUnitLog_translation (a : K) (p q : K[X]) (z : RelativeSpectrum v K[X])
    (hz : z.1.val (Polynomial.algEquivAevalXAddC a p*Polynomial.algEquivAevalXAddC a q)≠0) :
    rationalUnitLog v p q (polynomialTranslation a z)=
      rationalUnitLog v (Polynomial.algEquivAevalXAddC a p) (Polynomial.algEquivAevalXAddC a q) z := by
  rw [rationalUnitLog_eq v _ _ _ (unit_mul_ne_zero_translation v a p q z hz),
    rationalUnitLog_eq v _ _ _ hz]
  congr 1

/-- Every ORIGINAL finite maximum is transported on its genuine unit neighborhood, without an off-locus assertion. -/
theorem maxValue_translation (a : K) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) (z : RelativeSpectrum v K[X])
    (hz : ∀ j, z.1.val (translatedFamily a p j*translatedFamily a q j)≠0) :
    maxValue v p q I hI c α (polynomialTranslation a z)=
      maxValue v (translatedFamily a p) (translatedFamily a q) I hI c α z := by
  unfold maxValue affineValue
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [rationalUnitLog_translation v a (p j) (q j) z (hz j)]
  rfl

section AlgebraicallyClosed
variable [IsAlgClosed K]

private theorem polynomial_value_eq_of_root_values (x y : RelativeSpectrum v K[X]) (p : K[X])
    (h : ∀ b∈p.roots, y.1.val (X-C b)=x.1.val (X-C b)) : y.1.val p=x.1.val p := by
  rw [val_eq_leadingCoeff_mul_root_prod v y p,val_eq_leadingCoeff_mul_root_prod v x p]
  congr 1
  congr 1
  exact Multiset.map_congr rfl h

omit [IsAlgClosed K] in
private theorem exists_avoided_center (x : RelativeSpectrum v K[X]) :
    ∃ a : K, x.1.val (X-C a)≠0 := by
  by_cases h : x.1.val X=0
  · refine ⟨1,?_⟩
    have hc : x.1.val (C (1 : K))=1 := by simp
    have hlt : x.1.val X<x.1.val (C (1 : K)) := by rw [h,hc];exact zero_lt_one
    rw [x.1.val.map_sub_eq_of_lt_right hlt,hc]
    exact one_ne_zero
  · exact ⟨0,by simpa only [map_zero,sub_zero] using h⟩

/-- A genuine local maximum of the SAME original finite unit maximum is locally constant at EVERY whole original point of its unit locus. -/
theorem exists_open_maxValue_constant_of_isLocalMax_any_point
    (p q : J → K[X]) (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0)
    (I : Finset ι) (hI : I.Nonempty) (c : ι → ℝ) (α : ι → J → ℝ)
    (x : RelativeSpectrum v K[X]) (hx : ∀ j, x.1.val (p j*q j)≠0)
    (hmax : IsLocalMax (maxValue v p q I hI c α) x) :
    ∃ W : Set (RelativeSpectrum v K[X]), IsOpen W ∧ x∈W ∧
      (∀ y∈W, maxValue v p q I hI c α y=maxValue v p q I hI c α x) ∧
      ∀ y∈W, ∀ j, y.1.val (p j*q j)≠0 := by
  classical
  have hxP : x.1.val (numeratorProduct p)≠0 := by
    rw [numeratorProduct,map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (mul_ne_zero_iff.mp (by simpa only [map_mul] using hx j)).1
  have hxQ : x.1.val (numeratorProduct q)≠0 := by
    rw [numeratorProduct,map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (mul_ne_zero_iff.mp (by simpa only [map_mul] using hx j)).2
  obtain ⟨a₀,ha₀⟩ := exists_avoided_center v x
  let S := ((numeratorProduct p).roots+(numeratorProduct q).roots).toFinset ∪ {a₀}
  have hS : S.Nonempty := ⟨a₀,Finset.mem_union_right _ (Finset.mem_singleton_self a₀)⟩
  have hpos : ∀ b∈S, 0<x.1.val (X-C b) := by
    intro b hb
    apply pos_iff_ne_zero.mpr
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hb) with hb | hb
      · exact linear_val_ne_zero_of_polynomial_ne_zero v x _ hxP hb
      · exact linear_val_ne_zero_of_polynomial_ne_zero v x _ hxQ hb
    · exact (Finset.mem_singleton.mp hb) ▸ ha₀
  rcases exists_gauss_or_strictDisc_constant_linearValues v S hS x hpos with hGauss | hDisc
  · obtain ⟨a,_,t,ht,hxt⟩ := hGauss
    let p' := translatedFamily a p
    let q' := translatedFamily a q
    have hp' : ∀ j, p' j≠0 := translatedFamily_ne_zero a p hp
    have hq' : ∀ j, q' j≠0 := translatedFamily_ne_zero a q hq
    have hxt' : x=polynomialTranslation a (gauss (self v) t) := hxt
    have hmaxE : IsLocalMax (maxValue v p q I hI c α) (polynomialTranslation a (gauss (self v) t)) := by
      rwa [← hxt']
    have hEt := (polynomialTranslation a).continuous.continuousAt.eventually hmaxE
    have hN : ∀ᶠ z in 𝓝 (gauss (self v) t), z∈neighborhood v t ht p' q' :=
      (isOpen_neighborhood v t ht p' q').mem_nhds (gauss_mem_neighborhood v t ht p' q')
    have hunit₀ (j : J) := unit_mul_ne_zero_on_neighborhood v t ht p' q' hp' hq' j
      (gauss (self v) t) (gauss_mem_neighborhood v t ht p' q')
    have hvalue₀ := maxValue_translation v a p q I hI c α (gauss (self v) t) hunit₀
    have hmax' : IsLocalMax (maxValue v p' q' I hI c α) (gauss (self v) t) := by
      filter_upwards [hEt,hN] with z hz hzN
      calc
        _ = maxValue v p q I hI c α (polynomialTranslation a z) :=
          (maxValue_translation v a p q I hI c α z
            (fun j => unit_mul_ne_zero_on_neighborhood v t ht p' q' hp' hq' j z hzN)).symm
        _ ≤ _ := hz
        _ = _ := hvalue₀
    obtain ⟨W,hW,hη,hconst,hunits⟩ := exists_open_maxValue_constant_of_isLocalMax v t ht p' q' hp' hq' I hI c α hmax'
    refine ⟨(polynomialTranslation a) '' W,(polynomialTranslation a).isOpenMap W hW,
      ⟨gauss (self v) t,hη,hxt'.symm⟩,?_,?_⟩
    · rintro _ ⟨z,hz,rfl⟩
      calc
        _ = maxValue v p' q' I hI c α z := maxValue_translation v a p q I hI c α z (hunits z hz)
        _ = _ := hconst z hz
        _ = maxValue v p q I hI c α (polynomialTranslation a (gauss (self v) t)) := hvalue₀.symm
        _ = _ := congrArg (maxValue v p q I hI c α) hxt'.symm
    · rintro _ ⟨z,hz,rfl⟩ j
      exact unit_mul_ne_zero_translation v a (p j) (q j) z (hunits z hz j)
  · obtain ⟨a,t,_,ho,hxt,hroots⟩ := hDisc
    let W : Set (RelativeSpectrum v K[X]) := {y | y.1.val (X-C a)<t}
    have hvalues (y : RelativeSpectrum v K[X]) (hy : y∈W) (j : J) :
        y.1.val (p j)=x.1.val (p j) ∧ y.1.val (q j)=x.1.val (q j) := by
      constructor
      · apply polynomial_value_eq_of_root_values v x y (p j)
        intro b hb
        exact hroots y hy b (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
          (Multiset.mem_add.mpr (Or.inl (mem_roots_numeratorProduct p hp j hb)))))
      · apply polynomial_value_eq_of_root_values v x y (q j)
        intro b hb
        exact hroots y hy b (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
          (Multiset.mem_add.mpr (Or.inr (mem_roots_numeratorProduct q hq j hb)))))
    have hunits (y : RelativeSpectrum v K[X]) (hy : y∈W) (j : J) : y.1.val (p j*q j)≠0 := by
      simpa only [map_mul,(hvalues y hy j).1,(hvalues y hy j).2] using hx j
    refine ⟨W,ho,hxt,?_,hunits⟩
    intro y hy
    unfold maxValue affineValue
    congr 1
    funext i
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [rationalUnitLog_eq v _ _ y (hunits y hy j),rationalUnitLog_eq v _ _ x (hx j)]
    unfold rationalRealLog polynomialRealLog
    rw [(hvalues y hy j).1,(hvalues y hy j).2]

end AlgebraicallyClosed
end EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
