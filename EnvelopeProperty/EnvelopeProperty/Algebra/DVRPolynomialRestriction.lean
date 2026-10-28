/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PrincipalDivisorRegularizableFinite

/-!
# Actual polynomial DVR ramification and analytic point restriction

A genuine injective map to a DVR with a principal-prime polynomial centre derives its
positive ramification integer from the actual image of the prime polynomial. Exact order
factorization and the corresponding original analytic point follow internally.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open IsDiscreteValuationRing MvPolynomial

namespace Berk

variable {k A B V : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra k V]

/-- The actual analytic point attached to an original map to a DVR. -/
def dvrPoint (φ : A →ₐ[k] V) (q : ℝ≥0) (hq : q ≤ 1) : Berk k A :=
  Berk.ofFun (fun f => expOrd q (addVal V (φ f))) (by simp) (by simp)
    (fun f g => by rw [map_mul, addVal_mul, expOrd_add])
    (fun f g => by
      rw [map_add, ← (expOrd_antitone hq).map_min]
      exact expOrd_antitone hq ((addVal V).map_add _ _))
    (fun c hc => by
      rw [φ.commutes, (addVal_eq_zero_iff).mpr
        ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k V)), expOrd_zero])

@[simp]
theorem dvrPoint_val (φ : A →ₐ[k] V) {q : ℝ≥0} (hq : q ≤ 1) (f : A) :
    (dvrPoint φ q hq).val f = expOrd q (addVal V (φ f)) := rfl

/-- Pullback retains the original composite map and every entire element. -/
theorem comap_dvrPoint (φ : A →ₐ[k] B) (ψ : B →ₐ[k] V) {q : ℝ≥0} (hq : q ≤ 1) :
    comap φ (dvrPoint ψ q hq) = dvrPoint (ψ.comp φ) q hq := by
  apply Berk.ext
  apply Valuation.ext
  intro f
  rfl

end Berk

section PolynomialRamification

variable {k σ V : Type*} [Field k] [Finite σ] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

/-- The actual polynomial principal-prime DVR computes every prime-power factor exactly. -/
theorem polynomialPrimeDVR_ord_of_eq_pow_mul {p f g : MvPolynomial σ k}
    (hp : Prime p) {m : ℕ} (heq : f = p ^ m * g) (hg : ¬ p ∣ g) :
    (polynomialPrimeDVR p hp).ord f = m := by
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {p})
      (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial σ k)))
      (IsFractionRing.injective _ _)) := (polynomialPrimeDVR p hp).isDVR
  rw [heq]
  exact addVal_atPrimeRange _ _ rfl hp.ne_zero m hg

/-- An actual injective polynomial map with a principal prime centre derives a positive
ramification index and the exact normalized order identity on every original polynomial. -/
theorem exists_positive_polynomial_ramification (ρ : MvPolynomial σ k →+* V)
    (hinj : Function.Injective ρ) {p : MvPolynomial σ k} (hp : Prime p)
    (hcentre : (IsLocalRing.maximalIdeal V).comap ρ = Ideal.span {p}) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : MvPolynomial σ k,
      addVal V (ρ f) = (e : ℕ∞) * (polynomialPrimeDVR p hp).ord f := by
  have hp0 : ρ p ≠ 0 := (map_ne_zero_iff ρ hinj).mpr hp.ne_zero
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := V)).not.mpr hp0)
  have hmem : ρ p ∈ IsLocalRing.maximalIdeal V := by
    change p ∈ (IsLocalRing.maximalIdeal V).comap ρ
    rw [hcentre]
    exact Ideal.subset_span (Set.mem_singleton p)
  have he0 : e ≠ 0 := by
    intro hz
    have hval : addVal V (ρ p) = 0 := by rw [← he, hz, Nat.cast_zero]
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (addVal_eq_zero_iff.mp hval)
  refine ⟨e, Nat.pos_of_ne_zero he0, fun f => ?_⟩
  by_cases hf : f = 0
  · subst f
    simp [he0]
  obtain ⟨m, g, heq, hg⟩ := exists_eq_prime_pow_mul_not_dvd (totalDegree_pos_of_prime hp) hf
  have hunit : IsUnit (ρ g) := by
    by_contra hn
    have hgmem : g ∈ (IsLocalRing.maximalIdeal V).comap ρ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    rw [hcentre, Ideal.mem_span_singleton] at hgmem
    exact hg hgmem
  rw [polynomialPrimeDVR_ord_of_eq_pow_mul hp heq hg]
  rw [heq, map_mul, map_pow, addVal_mul, addVal_pow, addVal_eq_zero_iff.mpr hunit, add_zero,
    ← he, nsmul_eq_mul]
  exact mul_comm _ _

end PolynomialRamification

namespace Berk

/-- The original analytic DVR point equals an actual polynomial principal-divisor point
with internally derived positive ramification and parameter. -/
theorem dvrPoint_eq_polynomialPrimePoint {k σ V : Type*} [Field k] [Finite σ]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra k V]
    (ρ : MvPolynomial σ k →ₐ[k] V) (hinj : Function.Injective ρ)
    {p : MvPolynomial σ k} (hp : Prime p)
    (hcentre : (IsLocalRing.maximalIdeal V).comap ρ.toRingHom = Ideal.span {p})
    {c : ℝ} (hc : 0 < c) :
    ∃ (e : ℕ) (he : 0 < e), dvrPoint ρ (expNeg c) (ProjBerk.expNeg_le_one hc.le) =
      polynomialPrimePoint p hp (c * e) (mul_pos hc (by exact_mod_cast he)) := by
  obtain ⟨e, he, hord⟩ := exists_positive_polynomial_ramification ρ.toRingHom hinj hp hcentre
  refine ⟨e, he, ?_⟩
  have hqpow : expNeg (c * e) = expNeg c ^ e := by
    apply NNReal.eq
    change Real.exp (-(c * e)) = Real.exp (-c) ^ e
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply Berk.ext
  apply Valuation.ext
  intro f
  rw [dvrPoint_val, polynomialPrimePoint, BirationalDVR.berkPoint_val]
  change expOrd (expNeg c) (addVal V (ρ.toRingHom f)) = _
  rw [hord]
  by_cases hf : f = 0
  · subst f
    simp [he.ne']
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (((polynomialPrimeDVR p hp).ord_eq_top_iff).not.mpr hf)
  rw [← hm, ← Nat.cast_mul, expOrd_coe, expOrd_coe, hqpow, pow_mul]

end Berk

/-- The generic DVR-map point uses exactly the original inclusion of a birational DVR. -/
theorem BirationalDVR.berkPoint_eq_dvrPoint {k A : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] (V : BirationalDVR k A) {q : ℝ≥0} (hq : q ≤ 1) :
    V.berkPoint q hq = Berk.dvrPoint V.toRing q hq := by
  apply Berk.ext
  apply Valuation.ext
  intro f
  rfl

end EnvelopeProperty
