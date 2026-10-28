/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRMultiplierContribution
import EnvelopeProperty.Char0.DVRLeafLogBound

/-!
# Monomial leaf sections satisfy the actual DVR multiplier cutoff

The logarithmic Jacobian bound is used with the actual source ideal and
actual leaf divisor. No multiplier membership or discrepancy bound is
assumed for the conclusion.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

/-- The precise weighted floor cutoffs, together with the genuine logarithmic bound,
imply the strict rational discrepancy inequality. -/
theorem weighted_multiplier_cutoff_strict {τ : Type*} [Fintype τ]
    (r d a b : τ → ℕ) (F j : ℕ) (q : ℚ)
    (hb : ∀ l, ⌊q * (d l : ℚ)⌋₊ - a l ≤ b l)
    (hf : ∑ l, b l * r l ≤ F)
    (hj : (∑ l, r l) + ∑ l, a l * r l ≤ 1 + j) :
    q * ((∑ l, d l * r l : ℕ) : ℚ) < (F : ℚ) + 1 + j := by
  have hcut (l : τ) : q * (d l : ℚ) < (b l : ℚ) + (a l : ℚ) + 1 := by
    have h := (multiplier_cutoff_le_iff q (d l) (a l) (b l)).mp (hb l)
    linarith
  by_cases hz : ∀ l, r l = 0
  · simp only [hz, mul_zero, Finset.sum_const_zero, Nat.cast_zero]
    positivity
  · push Not at hz
    obtain ⟨l, hl⟩ := hz
    have hsum : (∑ l, q * (d l : ℚ) * (r l : ℚ)) <
        ∑ l, ((b l : ℚ) + (a l : ℚ) + 1) * (r l : ℚ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_le_mul_of_nonneg_right (hcut i).le (Nat.cast_nonneg _)
      · exact ⟨l, Finset.mem_univ l,
          mul_lt_mul_of_pos_right (hcut l) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl))⟩
    have hfr : (∑ l, (b l : ℚ) * (r l : ℚ)) ≤ (F : ℚ) := by exact_mod_cast hf
    have hjr : (∑ l, (r l : ℚ)) + ∑ l, (a l : ℚ) * (r l : ℚ) ≤ 1 + (j : ℚ) := by
      exact_mod_cast hj
    simp only [add_mul, one_mul, Finset.sum_add_distrib] at hsum
    have heq : q * ((∑ l, d l * r l : ℕ) : ℚ) = ∑ l, q * (d l : ℚ) * (r l : ℚ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, mul_assoc]
    rw [heq]
    linarith

/-- Finite actual normalized DVR orders of a monomial are the exact weighted sum. -/
theorem addVal_prod_pow_toNat {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {τ : Type*} [Fintype τ] (z : τ → V) (d : τ → ℕ)
    (hz : ∀ l, addVal V (z l) ≠ ⊤) :
    addVal V (∏ l, z l ^ d l) = ((∑ l, d l * (addVal V (z l)).toNat : ℕ) : ℕ∞) := by
  have h (s : Finset τ) :
      addVal V (∏ l ∈ s, z l ^ d l) = ((∑ l ∈ s, d l * (addVal V (z l)).toNat : ℕ) : ℕ∞) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert l s hl ih =>
      rw [Finset.prod_insert hl, Finset.sum_insert hl, addVal_mul, addVal_pow, ih,
        ← ENat.natCast_toNat (hz l)]
      simp [nsmul_eq_mul]
  exact h Finset.univ

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- An actual original element divisible by the rounded leaf monomial satisfies the
actual original-source strict DVR cutoff. The necessary logarithmic bound and
finite orders follow from the genuine source Jacobian, not from extra premises. -/
theorem mem_dvrMultiplierContribution_of_leaf_monomial
    (C E V : Subalgebra k K) [IsFractionRing C K]
    [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
    (hCE : C ≤ E) (hEV : E ≤ V) {ι : Type u} [Fintype ι]
    {π : V} {u : ι → V} {n : ℕ} (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι)
    (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a b : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) (hb : ∀ l, ⌊q * (d l : ℚ)⌋₊ - a l ≤ b l)
    (f : C) (hfE : Subalgebra.inclusion hCE f ∈ span {∏ l, v (c l) ^ b l}) :
    f ∈ dvrMultiplierContribution C V (hCE.trans hEV) hπ hu e I hI q := by
  rw [mem_dvrMultiplierContribution_iff_strict]
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  apply Or.inr
  let hCV : C ≤ V := hCE.trans hEV
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  have hjfinite := dvrOriginalSourceJacobianIdeal_order_ne_top V C hCV hπ hu e
  have hlog := dvr_original_source_leaf_logarithmic_bound E V hEV C hCE hCV hπ hu e v hv c a hJ
  have hupper : 1 + dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e) ≠ ⊤ := by
    simp only [ne_eq, ENat.add_eq_top, not_or]
    exact ⟨by simp, hjfinite⟩
  have hcoordfinite (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hupper
    calc
      addVal V (Subalgebra.inclusion hEV (v i)) ≤ ∑ j, addVal V (Subalgebra.inclusion hEV (v j)) :=
        Finset.single_le_sum
          (f := fun j => addVal V (Subalgebra.inclusion hEV (v j)))
          (fun _ _ => bot_le) (Finset.mem_univ i)
      _ ≤ (∑ j, addVal V (Subalgebra.inclusion hEV (v j))) +
          ∑ l, a l • addVal V (Subalgebra.inclusion hEV (v (c l))) := le_self_add
      _ ≤ _ := hlog
  let r : Fin n → ℕ := fun i => (addVal V (Subalgebra.inclusion hEV (v i))).toNat
  have hcoord (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) = (r i : ℕ∞) :=
    (ENat.natCast_toNat (hcoordfinite i)).symm
  have hlogNat : (∑ i, r i) + ∑ l, a l * r (c l) ≤
      1 + (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat := by
    simp_rw [hcoord] at hlog
    rw [← ENat.natCast_toNat hjfinite] at hlog
    simp_rw [nsmul_eq_mul] at hlog
    exact_mod_cast hlog
  have hselected : ∑ l, r (c l) ≤ ∑ i, r i := by
    calc
      ∑ l, r (c l) = ∑ i ∈ Finset.univ.image c, r i :=
        (Finset.sum_image (fun _ _ _ _ h => hc h)).symm
      _ ≤ ∑ i ∈ Finset.univ, r i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hbound : (∑ l, r (c l)) + ∑ l, a l * r (c l) ≤
      1 + (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat := by
    omega
  have hIV : I.map (Subalgebra.inclusion hCV).toRingHom =
      span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^ d l} := by
    have h := congrArg (fun J : Ideal E => J.map (Subalgebra.inclusion hEV).toRingHom) hIE
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at h
    have hcomp : (Subalgebra.inclusion hEV).toRingHom.comp
        (Subalgebra.inclusion hCE).toRingHom = (Subalgebra.inclusion hCV).toRingHom := rfl
    rw [hcomp] at h
    have hmap (z : E) : (Subalgebra.inclusion hEV).toRingHom z = Subalgebra.inclusion hEV z := rfl
    simpa only [map_prod, map_pow, hmap] using h
  have hordI : dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) =
      ((∑ l, d l * r (c l) : ℕ) : ℕ∞) := by
    rw [hIV, dvrIdealOrder_span_singleton,
      addVal_prod_pow_toNat _ d (fun l => hcoordfinite (c l))]
  have hfV : Subalgebra.inclusion hCV f ∈
      span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^ b l} := by
    have h := Ideal.mem_map_of_mem (Subalgebra.inclusion hEV).toRingHom hfE
    rw [Ideal.map_span, Set.image_singleton] at h
    have hmap (z : E) : (Subalgebra.inclusion hEV).toRingHom z = Subalgebra.inclusion hEV z := rfl
    have hcomp : Subalgebra.inclusion hEV (Subalgebra.inclusion hCE f) =
        Subalgebra.inclusion hCV f := rfl
    simpa only [map_prod, map_pow, hmap, hcomp] using h
  have hfv : addVal V (Subalgebra.inclusion hCV f) ≠ ⊤ := by
    rw [ne_eq, addVal_eq_top_iff]
    exact (map_ne_zero_iff _ (Subalgebra.inclusion_injective hCV)).mpr hf0
  have hval : addVal V (∏ l, Subalgebra.inclusion hEV (v (c l)) ^ b l) ≤
      addVal V (Subalgebra.inclusion hCV f) :=
    addVal_le_iff_dvd.mpr (Ideal.mem_span_singleton.mp hfV)
  rw [addVal_prod_pow_toNat _ b (fun l => hcoordfinite (c l))] at hval
  have hforder : ∑ l, b l * r (c l) ≤ (addVal V (Subalgebra.inclusion hCV f)).toNat := by
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hval hfv
  change q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ) < _
  rw [hordI]
  simpa only [ENat.toNat_natCast] using
    weighted_multiplier_cutoff_strict (fun l => r (c l)) d a b
      (addVal V (Subalgebra.inclusion hCV f)).toNat
      (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat q hb hforder hbound

end EnvelopeProperty.Char0
