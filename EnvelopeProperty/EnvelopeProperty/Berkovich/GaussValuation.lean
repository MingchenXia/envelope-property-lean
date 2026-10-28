/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Gauss valuations on polynomial rings

For an arbitrary commutative ring, an arbitrary real-valued ultrametric valuation,
and any nonnegative radius, the maximum of weighted coefficient values is again
a valuation. Multiplicativity uses the unique dominant term at the sum of the
least indices realizing the two maxima. No field or base valuation is required.

This primitive is shared by the general seminorm spectra and the paper's affine
analytification. Existing `EnvelopeProperty.gaussValuation` declarations retain
all their names and signatures.
-/

open scoped NNReal ENNReal Topology Polynomial
open Polynomial Set

noncomputable section

namespace EnvelopeProperty

/-! ### The Gauss valuation attached to a real valuation -/

section GaussValuation

variable {A : Type*} [CommRing A] (v : Valuation A ℝ≥0) (r : ℝ≥0)

/-- The underlying function of the Gauss valuation: `F ↦ max_ℓ v(F_ℓ) r^ℓ`. -/
def gaussFun (F : A[X]) : ℝ≥0 :=
  F.support.sup fun ℓ => v (F.coeff ℓ) * r ^ ℓ

theorem le_gaussFun (F : A[X]) (ℓ : ℕ) : v (F.coeff ℓ) * r ^ ℓ ≤ gaussFun v r F := by
  by_cases h : ℓ ∈ F.support
  · exact Finset.le_sup (f := fun ℓ => v (F.coeff ℓ) * r ^ ℓ) h
  · rw [notMem_support_iff.1 h, v.map_zero, zero_mul]
    exact zero_le

theorem gaussFun_le_iff (F : A[X]) (R : ℝ≥0) :
    gaussFun v r F ≤ R ↔ ∀ ℓ, v (F.coeff ℓ) * r ^ ℓ ≤ R :=
  ⟨fun h ℓ => (le_gaussFun v r F ℓ).trans h, fun h => Finset.sup_le fun ℓ _ => h ℓ⟩

theorem gaussFun_eq_sup_of_subset (F : A[X]) {s : Finset ℕ} (hs : F.support ⊆ s) :
    gaussFun v r F = s.sup fun ℓ => v (F.coeff ℓ) * r ^ ℓ :=
  le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun ℓ _ => le_gaussFun v r F ℓ)

theorem exists_eq_gaussFun (F : A[X]) : ∃ ℓ, gaussFun v r F = v (F.coeff ℓ) * r ^ ℓ := by
  rcases F.support.eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_⟩
    rw [support_eq_empty.1 h]
    simp [gaussFun]
  · obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_eq_sup _ h fun ℓ => v (F.coeff ℓ) * r ^ ℓ
    exact ⟨ℓ, hℓ⟩

theorem gaussFun_monomial (n : ℕ) (a : A) : gaussFun v r (monomial n a) = v a * r ^ n := by
  rw [gaussFun_eq_sup_of_subset v r _ (support_monomial_subset (n := n) (a := a)),
    Finset.sup_singleton, coeff_monomial_same]

theorem gaussFun_C (a : A) : gaussFun v r (C a) = v a := by
  rw [← monomial_zero_left, gaussFun_monomial, pow_zero, mul_one]

theorem gaussFun_X : gaussFun v r (X : A[X]) = r := by
  rw [← monomial_one_one_eq_X, gaussFun_monomial, v.map_one, one_mul, pow_one]

theorem gaussFun_add_le (F G : A[X]) :
    gaussFun v r (F + G) ≤ max (gaussFun v r F) (gaussFun v r G) := by
  rw [gaussFun_le_iff]
  intro ℓ
  rw [coeff_add]
  calc v (F.coeff ℓ + G.coeff ℓ) * r ^ ℓ ≤ max (v (F.coeff ℓ)) (v (G.coeff ℓ)) * r ^ ℓ := by
        gcongr
        exact v.map_add _ _
    _ = max (v (F.coeff ℓ) * r ^ ℓ) (v (G.coeff ℓ) * r ^ ℓ) := max_mul_of_nonneg _ _ zero_le
    _ ≤ max (gaussFun v r F) (gaussFun v r G) :=
        max_le_max (le_gaussFun v r F ℓ) (le_gaussFun v r G ℓ)

/-- In a nonempty finite sum, some term dominates the sum for an ultrametric valuation. -/
theorem exists_valuation_sum_le {R : Type*} [Ring R] (w : Valuation R ℝ≥0)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → R) :
    ∃ i ∈ s, w (∑ j ∈ s, f j) ≤ w (f i) := by
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => w (f j)) hs
  exact ⟨i, hi, w.map_sum_le hmax⟩

theorem gaussFun_mul_le (F G : A[X]) :
    gaussFun v r (F * G) ≤ gaussFun v r F * gaussFun v r G := by
  rw [gaussFun_le_iff]
  intro n
  rw [coeff_mul]
  obtain ⟨x, hx, hle⟩ := exists_valuation_sum_le v
    (s := Finset.HasAntidiagonal.antidiagonal n) ⟨(0, n), by simp⟩
    fun x => F.coeff x.1 * G.coeff x.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  calc v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, F.coeff x.1 * G.coeff x.2) * r ^ n
      ≤ v (F.coeff x.1 * G.coeff x.2) * r ^ n := by gcongr
    _ = (v (F.coeff x.1) * r ^ x.1) * (v (G.coeff x.2) * r ^ x.2) := by
        rw [v.map_mul, ← hx, pow_add]; ring
    _ ≤ gaussFun v r F * gaussFun v r G :=
        mul_le_mul' (le_gaussFun v r F _) (le_gaussFun v r G _)

/-- **Gauss's lemma** (lower bound): the coefficient of degree `i + j` of `F G`, for the minimal
indices `i`, `j` where the maxima for `F` and `G` are attained, has a unique dominant term. -/
theorem mul_le_gaussFun_mul (F G : A[X]) :
    gaussFun v r F * gaussFun v r G ≤ gaussFun v r (F * G) := by
  classical
  by_cases hF : gaussFun v r F = 0
  · rw [hF, zero_mul]; exact zero_le
  by_cases hG : gaussFun v r G = 0
  · rw [hG, mul_zero]; exact zero_le
  have hexF := exists_eq_gaussFun v r F
  have hexG := exists_eq_gaussFun v r G
  set i := Nat.find hexF
  set j := Nat.find hexG
  have hi : gaussFun v r F = v (F.coeff i) * r ^ i := Nat.find_spec hexF
  have hj : gaussFun v r G = v (G.coeff j) * r ^ j := Nat.find_spec hexG
  have hi' : ∀ a < i, v (F.coeff a) * r ^ a < gaussFun v r F := fun a ha =>
    lt_of_le_of_ne (le_gaussFun v r F a) fun h => Nat.find_min hexF ha h.symm
  have hj' : ∀ b < j, v (G.coeff b) * r ^ b < gaussFun v r G := fun b hb =>
    lt_of_le_of_ne (le_gaussFun v r G b) fun h => Nat.find_min hexG hb h.symm
  have hFpos : 0 < gaussFun v r F := pos_iff_ne_zero.2 hF
  have hGpos : 0 < gaussFun v r G := pos_iff_ne_zero.2 hG
  have hrpos : 0 < r ^ (i + j) := by
    rw [pow_add]
    refine mul_pos (pos_iff_ne_zero.2 fun h => hF ?_) (pos_iff_ne_zero.2 fun h => hG ?_)
    · rw [hi, h, mul_zero]
    · rw [hj, h, mul_zero]
  have key : v (F.coeff i * G.coeff j) * r ^ (i + j) = gaussFun v r F * gaussFun v r G := by
    rw [hi, hj, v.map_mul, pow_add]; ring
  refine le_trans ?_ (le_gaussFun v r (F * G) (i + j))
  rw [coeff_mul, v.map_sum_eq_of_lt (j := (i, j)) (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl), key]
  intro x hx
  rw [Finset.mem_sdiff, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton] at hx
  obtain ⟨hxsum, hxne⟩ := hx
  have hx1 : x.1 ≠ i := by
    intro h
    apply hxne
    ext
    · exact h
    · simp only; omega
  refine lt_of_mul_lt_mul_right (a := r ^ (i + j)) ?_ zero_le
  rw [key]
  calc v (F.coeff x.1 * G.coeff x.2) * r ^ (i + j)
      = (v (F.coeff x.1) * r ^ x.1) * (v (G.coeff x.2) * r ^ x.2) := by
        rw [v.map_mul, ← hxsum, pow_add]; ring
    _ < gaussFun v r F * gaussFun v r G := by
        rcases lt_or_gt_of_ne hx1 with h | h
        · calc (v (F.coeff x.1) * r ^ x.1) * (v (G.coeff x.2) * r ^ x.2)
              ≤ (v (F.coeff x.1) * r ^ x.1) * gaussFun v r G := by
                gcongr; exact le_gaussFun v r G _
            _ < gaussFun v r F * gaussFun v r G := by
                gcongr; exact hi' _ h
        · have h2 : x.2 < j := by omega
          calc (v (F.coeff x.1) * r ^ x.1) * (v (G.coeff x.2) * r ^ x.2)
              ≤ gaussFun v r F * (v (G.coeff x.2) * r ^ x.2) := by
                gcongr; exact le_gaussFun v r F _
            _ < gaussFun v r F * gaussFun v r G := by
                gcongr; exact hj' _ h2

theorem gaussFun_mul (F G : A[X]) :
    gaussFun v r (F * G) = gaussFun v r F * gaussFun v r G :=
  le_antisymm (gaussFun_mul_le v r F G) (mul_le_gaussFun_mul v r F G)

/-- The **Gauss valuation** on `A[X]` attached to a valuation `v : A → ℝ≥0` and a radius
`r ≥ 0`: `|∑_ℓ a_ℓ X^ℓ| = max_ℓ v(a_ℓ) r^ℓ`. -/
def gaussValuation : Valuation A[X] ℝ≥0 where
  toFun := gaussFun v r
  map_zero' := by simp [gaussFun]
  map_one' := by rw [← C_1, gaussFun_C, v.map_one]
  map_mul' := gaussFun_mul v r
  map_add_le_max' := gaussFun_add_le v r

theorem gaussValuation_apply (F : A[X]) :
    gaussValuation v r F = F.support.sup fun ℓ => v (F.coeff ℓ) * r ^ ℓ :=
  rfl

end GaussValuation

end EnvelopeProperty
