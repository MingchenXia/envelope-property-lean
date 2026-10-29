/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVREtaleLeafLocalization
import EnvelopeProperty.Char0.DVRMonomialMultiplierBound

/-!
# Exact multiplier monomial cutoffs at actual divisorial leaf localizations

The unit derivative determinant forces total coordinate order at most one,
so the genuine source cutoff is exactly the rounded actual leaf monomial.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

/-- Under an actual total order at most one, the full weighted rational cutoff is
exactly the weighted sum of coordinate cutoffs. -/
theorem weighted_multiplier_floor_eq_of_sum_le_one {τ : Type*} [Fintype τ]
    (r d a : τ → ℕ) (q : ℚ) (hr : ∑ l, r l ≤ 1) :
    ⌊q * ((∑ l, d l * r l : ℕ) : ℚ)⌋₊ - (∑ l, a l * r l) =
      ∑ l, (⌊q * (d l : ℚ)⌋₊ - a l) * r l := by
  classical
  by_cases hz : ∀ l, r l = 0
  · simp [hz]
  · push Not at hz
    obtain ⟨l, hl⟩ := hz
    have hrl : r l = 1 := by
      have hle : r l ≤ ∑ j, r j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      omega
    have herase : ∑ j ∈ Finset.univ.erase l, r j = 0 := by
      have h := Finset.sum_erase_add Finset.univ r (Finset.mem_univ l)
      omega
    have hzero (j : τ) (hjl : j ≠ l) : r j = 0 := by
      have hle : r j ≤ ∑ j ∈ Finset.univ.erase l, r j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨hjl, Finset.mem_univ j⟩)
      omega
    have hsum (f : τ → ℕ) : ∑ j, f j * r j = f l := by
      rw [Finset.sum_eq_single l]
      · simp only [hrl, mul_one]
      · intro j _ hjl
        rw [hzero j hjl, mul_zero]
      · intro h
        exact (h (Finset.mem_univ l)).elim
    rw [hsum d, hsum a, hsum (fun l => ⌊q * (d l : ℚ)⌋₊ - a l)]

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The actual original-source multiplier contribution at a DVR localization of an
etale monomial leaf is exactly the literal inverse image of its rounded leaf
monomial ideal. No divisor-order or determinant-unit premise is supplied. -/
theorem dvrMultiplierContribution_eq_monomial_comap_of_localization
    (C E V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCE : C ≤ E) (hEV : E ≤ V) (M : Submonoid E)
    (hlocal : letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
      IsLocalization M V)
    {ι : Type u} [Fintype ι] {π : V} {u : ι → V} {n : ℕ}
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u))
    (e : Fin n ≃ Option ι) (v : Fin n → E)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) :
    dvrMultiplierContribution C V (hCE.trans hEV) hπ hu e I hI q =
      (span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^
        (⌊q * (d l : ℚ)⌋₊ - a l)}).comap (Subalgebra.inclusion (hCE.trans hEV)).toRingHom := by
  let hCV : C ≤ V := hCE.trans hEV
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsum := sum_addVal_leaf_le_one_of_localization V E hEV M hlocal hπ hu e v hv
  have hcoordfinite (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
    exact (Finset.single_le_sum
      (f := fun j => addVal V (Subalgebra.inclusion hEV (v j)))
      (fun _ _ => bot_le) (Finset.mem_univ i)).trans hsum
  let r : Fin n → ℕ := fun i => (addVal V (Subalgebra.inclusion hEV (v i))).toNat
  have hcoord (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) = (r i : ℕ∞) :=
    (ENat.natCast_toNat (hcoordfinite i)).symm
  have hsumNat : ∑ i, r i ≤ 1 := by
    simp_rw [hcoord] at hsum
    exact_mod_cast hsum
  have hselected : ∑ l, r (c l) ≤ 1 := by
    calc
      ∑ l, r (c l) = ∑ i ∈ Finset.univ.image c, r i :=
        (Finset.sum_image (fun _ _ _ _ h => hc h)).symm
      _ ≤ ∑ i ∈ Finset.univ, r i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 1 := hsumNat
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
  have hordJ : dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e) =
      ((∑ l, a l * r (c l) : ℕ) : ℕ∞) := by
    have h := dvr_leaf_source_jacobian_order E V hEV C hCE hπ hu e v hv c a hJ
    rw [dvrSourceJacobianIdeal_through_leaf C V hCV E hCE hEV hπ hu e] at h
    rw [addVal_eq_zero_iff.mpr (isUnit_dvrLeafDet_of_localization V E hEV M hlocal hπ hu e v hv),
      zero_add] at h
    simp_rw [hcoord] at h
    simpa only [nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul] using h
  ext f
  rw [mem_dvrMultiplierContribution_iff_order, Ideal.mem_comap, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd,
    addVal_prod_pow_toNat _ (fun l => ⌊q * (d l : ℚ)⌋₊ - a l) (fun l => hcoordfinite (c l))]
  change ((⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ -
    (dvrIdealOrder (dvrOriginalSourceJacobianIdeal C V hCV hπ hu e)).toNat : ℕ) : ℕ∞) ≤ _ ↔ _
  rw [hordI, hordJ]
  simp only [ENat.toNat_natCast, weighted_multiplier_floor_eq_of_sum_le_one
    (fun l => r (c l)) d a q hselected]
  rfl

end EnvelopeProperty.Char0
