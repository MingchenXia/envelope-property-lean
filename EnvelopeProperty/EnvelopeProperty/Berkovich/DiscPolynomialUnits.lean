/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.GaussCompletion
import EnvelopeProperty.Berkovich.ValuationExtension
import Mathlib.Analysis.Normed.Ring.Units

/-! # Actual root exclusion and units in the original closed Gauss disc -/
open scoped NNReal Polynomial Topology
open Polynomial UniformSpace
noncomputable section
namespace EnvelopeProperty

section SplitGauss
variable {F : Type*} [Field F]

/-- The entire linear polynomial has its actual maximum coefficient value. -/
theorem gaussFun_X_sub_C (v : Valuation F ℝ≥0) (r : ℝ≥0) (a : F) :
    gaussFun v r (X - C a) = max r (v a) := by
  apply le_antisymm
  · exact (gaussValuation v r).map_sub X (C a) |>.trans_eq (by
      change max (gaussFun v r X) (gaussFun v r (C a)) = _
      rw [gaussFun_X, gaussFun_C])
  · apply max_le
    · have hb := le_gaussFun v r (X - C a) 1
      have he : (X - C a).coeff 1 = (1 : F) := by simp [Polynomial.coeff_sub]
      rw [he, v.map_one, one_mul, pow_one] at hb
      exact hb
    · have hb := le_gaussFun v r (X - C a) 0
      have he : (X - C a).coeff 0 = -a := by simp [Polynomial.coeff_sub]
      rw [he, v.map_neg, pow_zero, mul_one] at hb
      exact hb

/-- Whole split factorization computes the Gauss value from every actual root. -/
theorem gaussFun_eq_leadingCoeff_mul_prod_roots (v : Valuation F ℝ≥0) (r : ℝ≥0)
    (p : F[X]) (hp : p.Splits) :
    gaussFun v r p = v p.leadingCoeff * (p.roots.map (fun a => max r (v a))).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [gaussFun_mul, gaussFun_C]
  congr 1
  change (gaussValuation v r) _ = _
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  exact gaussFun_X_sub_C v r a

/-- Actual root bounds give the WHOLE constant-term Gauss value. -/
theorem gaussFun_eq_coeff_zero_of_splits (v : Valuation F ℝ≥0) (r : ℝ≥0)
    (p : F[X]) (hp : p.Splits) (hr : ∀ a ∈ p.roots, r ≤ v a) :
    gaussFun v r p = v (p.coeff 0) := by
  rw [gaussFun_eq_leadingCoeff_mul_prod_roots v r p hp, coeff_zero_eq_eval_zero,
    hp.eval_eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map]
  congr 1
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply, zero_sub, Valuation.map_neg]
  exact max_eq_right (hr a ha)


/-- Excluding the actual finite split roots gives strict whole constant dominance. -/
theorem gaussFun_tail_lt_coeff_zero_of_splits (v : Valuation F ℝ≥0) (r : ℝ≥0)
    (p : F[X]) (hp : p.Splits) (hp0 : p ≠ 0)
    (hroot : ∀ a ∈ p.roots, r < v a) :
    gaussFun v r (p - C (p.coeff 0)) < v (p.coeff 0) := by
  classical
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    have hm : (0 : F) ∈ p.roots := (Polynomial.mem_roots hp0).mpr (by
      simpa only [Polynomial.IsRoot, ← coeff_zero_eq_eval_zero] using hc)
    have hb := hroot 0 hm
    rw [v.map_zero] at hb
    exact (not_lt_of_ge zero_le) hb
  have hvc : 0 < v (p.coeff 0) := pos_iff_ne_zero.mpr ((v.ne_zero_iff).mpr hc)
  let upper : Finset ℝ≥0 := insert (r+1) (p.roots.toFinset.image v)
  have hupper : ∀ b ∈ upper, r < b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact lt_add_one r
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact hroot a (Multiset.mem_toFinset.mp ha)
  obtain ⟨s, hs, hb⟩ := Finset.exists_between (s := {r}) (t := upper)
    (by simp) (by simp [upper]) (by
      intro a ha b hb
      simpa only [Finset.mem_singleton.mp ha] using hupper b hb)
  have hrs : r < s := hs r (by simp)
  have hroots : ∀ a ∈ p.roots, s ≤ v a := by
    intro a ha
    exact (hb (v a) (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Multiset.mem_toFinset.mpr ha, rfl⟩))).le
  have hgauss := gaussFun_eq_coeff_zero_of_splits v s p hp hroots
  apply (Finset.sup_lt_iff hvc).mpr
  intro i hi
  have hin : i ≠ 0 := by
    intro hin
    subst i
    have he := Polynomial.mem_support_iff.mp hi
    simp [Polynomial.coeff_sub] at he
  have he : (p - C (p.coeff 0)).coeff i = p.coeff i := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_C, hin]
  rw [he]
  by_cases hpi : v (p.coeff i) = 0
  · simpa only [hpi, zero_mul] using hvc
  · exact (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hrs zero_le hin)
      (pos_iff_ne_zero.mpr hpi)).trans_le ((le_gaussFun v s p i).trans_eq hgauss)

end SplitGauss

namespace Berkovich.GaussCompletion
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

private theorem gaussFun_map_preserving (r : ℝ≥0) {F : Type*} [Field F]
    (φ : K →+* F) (v : Valuation F ℝ≥0) (hv : ∀ c, v (φ c) = ‖c‖₊) (p : K[X]) :
    gaussFun v r (p.map φ) = gaussFun (NormedField.valuation (K := K)) r p := by
  apply le_antisymm
  · apply (gaussFun_le_iff _ _ _ _).mpr
    intro i
    rw [Polynomial.coeff_map, hv]
    exact le_gaussFun (NormedField.valuation (K := K)) r p i
  · apply (gaussFun_le_iff _ _ _ _).mpr
    intro i
    have hb := le_gaussFun v r (p.map φ) i
    rw [Polynomial.coeff_map, hv] at hb
    exact hb

/-- Genuine roots in any actual norm-preserving split extension test the WHOLE original closed disc. -/
theorem polynomial_tail_lt_of_split_extension (r : ℝ≥0) (p : K[X])
    {F : Type*} [Field F] (φ : K →+* F) (v : Valuation F ℝ≥0)
    (hv : ∀ c, v (φ c) = ‖c‖₊) (hsplit : (p.map φ).Splits)
    (hnonzero : ∀ x : ClosedDisc (K := K) r, x.1.1.val p ≠ 0) :
    gaussFun (NormedField.valuation (K := K)) r (p - C (p.coeff 0)) < ‖p.coeff 0‖₊ := by
  have hp : p ≠ 0 := by
    intro hp
    have hb := hnonzero (gaussPoint (K := K) r)
    simp only [hp, map_zero, ne_eq, not_true_eq_false] at hb
  have hpf : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr hp
  have hroot : ∀ a ∈ (p.map φ).roots, r < v a := by
    intro a ha
    by_contra hra
    have hra : v a ≤ r := le_of_not_gt hra
    let x : RelativeSpectrum (NormedField.valuation (K := K)) K[X] :=
      ⟨⟨v.comap (Polynomial.eval₂RingHom φ a)⟩, by
        intro c
        change v (Polynomial.eval₂ φ a (C c)) = ‖c‖₊
        rw [Polynomial.eval₂_C, hv]⟩
    have hx : x.1.val X ≤ r := by
      change v (Polynomial.eval₂ φ a X) ≤ r
      simpa only [Polynomial.eval₂_X] using hra
    have hzero : x.1.val p = 0 := by
      change v (Polynomial.eval₂ φ a p) = 0
      have he := (Polynomial.mem_roots hpf).mp ha
      change (p.map φ).eval a = 0 at he
      rw [Polynomial.eval_map] at he
      rw [he, v.map_zero]
    exact hnonzero ⟨x, hx⟩ hzero
  have ht := gaussFun_tail_lt_coeff_zero_of_splits v r (p.map φ) hsplit hpf hroot
  have he : p.map φ - C ((p.map φ).coeff 0) = (p - C (p.coeff 0)).map φ := by
    simp only [Polynomial.map_sub, Polynomial.map_C, Polynomial.coeff_map]
  rw [he, gaussFun_map_preserving r φ v hv, Polynomial.coeff_map, hv] at ht
  exact ht

/-- The genuine finite splitting field of the completed original base derives strict constant dominance. -/
theorem polynomial_tail_lt_of_no_disc_zero (r : ℝ≥0) (p : K[X])
    (hnonzero : ∀ x : ClosedDisc (K := K) r, x.1.1.val p ≠ 0) :
    gaussFun (NormedField.valuation (K := K)) r (p - C (p.coeff 0)) < ‖p.coeff 0‖₊ := by
  let L := Completion K
  let q := p.map (algebraMap K L)
  let F := q.SplittingField
  obtain ⟨v, hv⟩ := Valuation.exists_extends_norm (K := L) (L := F)
  let φ : K →+* F := (algebraMap L F).comp (algebraMap K L)
  have hφ (c : K) : v (φ c) = ‖c‖₊ := by
    change v (algebraMap L F (algebraMap K L c)) = _
    rw [hv]
    change ‖(algebraMap K (Completion K)) c‖₊ = ‖c‖₊
    rw [Completion.algebraMap_def, Completion.nnnorm_coe]
    rfl
  apply polynomial_tail_lt_of_split_extension r p φ v hφ _ hnonzero
  change (p.map ((algebraMap L F).comp (algebraMap K L))).Splits
  rw [← Polynomial.map_map]
  exact Polynomial.SplittingField.splits q


/-- Actual spectral root exclusion constructs a genuine unit in the SAME completed disc ring. -/
theorem isUnit_polynomialMap_of_no_disc_zero (r : ℝ≥0) (hr : 0 < r) (p : K[X])
    (hnonzero : ∀ x : ClosedDisc (K := K) r, x.1.1.val p ≠ 0) :
    IsUnit (polynomialMap r hr p) := by
  have ht := polynomial_tail_lt_of_no_disc_zero r p hnonzero
  have hpc : 0 < ‖p.coeff 0‖₊ := lt_of_le_of_lt zero_le ht
  have hc : p.coeff 0 ≠ 0 := nnnorm_ne_zero_iff.mp hpc.ne'
  let q := polynomialMap r hr p
  let c := polynomialMap r hr (C (p.coeff 0))
  let d := polynomialMap r hr (C (p.coeff 0)⁻¹)
  let t := d * (q-c)
  have hte : t = polynomialMap r hr (C (p.coeff 0)⁻¹ * (p - C (p.coeff 0))) := by
    simp only [map_mul, map_sub]
    rfl
  have htn : ‖t‖₊ < 1 := by
    rw [hte, nnnorm_polynomialMap, gaussFun_mul, gaussFun_C,
      NormedField.valuation_apply, nnnorm_inv]
    calc
      ‖p.coeff 0‖₊⁻¹ * gaussFun (NormedField.valuation (K := K)) r (p-C (p.coeff 0))
          < ‖p.coeff 0‖₊⁻¹ * ‖p.coeff 0‖₊ := mul_lt_mul_of_pos_left ht (inv_pos.mpr hpc)
      _ = 1 := inv_mul_cancel₀ hpc.ne'
  have hunitc : IsUnit c :=
    (isUnit_iff_ne_zero.mpr hc).map ((polynomialMap r hr).comp C)
  have hunit : IsUnit (1+t) := by
    have hb : ‖-t‖ < 1 := by exact_mod_cast (by simpa only [nnnorm_neg] using htn : ‖-t‖₊ < 1)
    simpa only [Units.val_oneSub, sub_neg_eq_add] using (Units.oneSub (-t) hb).isUnit
  have hcd : c*d = 1 := by
    dsimp [c, d]
    rw [← map_mul, ← C_mul, mul_inv_cancel₀ hc, C_1, map_one]
  have he : c*(1+t) = q := by
    dsimp [t]
    rw [mul_add, mul_one, ← mul_assoc, hcd, one_mul]
    ring
  simpa only [he] using hunitc.mul hunit

/-- Actual polynomial spectral nonvanishing is exactly genuine invertibility in the original disc. -/
theorem isUnit_polynomialMap_iff_no_disc_zero (r : ℝ≥0) (hr : 0 < r) (p : K[X]) :
    IsUnit (polynomialMap r hr p) ↔ ∀ x : ClosedDisc (K := K) r, x.1.1.val p ≠ 0 := by
  constructor
  · intro hp x
    have hn := (hp.map ((discHomeomorph r hr).symm x).1.1.val).ne_zero
    change value r hr (polynomialMap r hr p) x ≠ 0 at hn
    rwa [value_polynomialMap] at hn
  · exact isUnit_polynomialMap_of_no_disc_zero r hr p

end Berkovich.GaussCompletion

end EnvelopeProperty
