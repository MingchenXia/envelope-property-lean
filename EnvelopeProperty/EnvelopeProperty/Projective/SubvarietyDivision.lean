/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyNormal
import EnvelopeProperty.Algebra.NormalDVR

/-!
# Divisorial points and division from growth on a projectively normal `V(I) ⊆ ℙᴹ`

Let `k` be a field with the trivial absolute value, `X = V(I) ⊆ ℙᴹ` a projective subvariety
(`ProjSubvariety`) with homogeneous coordinate ring `S = R_M / I`. This file proves the blueprint
lemmas `lem:pg-div-points` and `lem:pg-division` (`projective-general.tex`, subsection
`subsec:pg-normal`), the analogues on `X` of the divisorial points `ProjBerk.ordPoint` and of the
divisibility lemma `lem:bj-divisibility` on `ℙⁿ` (`Projective/CompactificationDivisibility.lean`),
with factoriality of `k[x₀, …, xₙ]` replaced by normality of `S` and discrete valuations. They are
used for Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.10(2)
(`lem:compactification`) on `X` (`lem:pg-compactification-extend`), the analogue of
Boucksom–Jonsson's `lem:FShomdiv`.

## Points attached to discrete valuations (`lem:pg-div-points`)

Let `P` be a prime of `S` such that `S_P` is a discrete valuation ring, with valuation
`ord_P = IsDiscreteValuationRing.addVal S_P` (`ProjSubvariety.ordAt`), and let
`m_P = min_j ord_P(x̄_j) ∈ ℕ` (`ProjSubvariety.minOrd`; finite since some `xⱼ ∉ I`). For `t ≥ 0`
the family `N_t(f) = e^{-t (ord_P(f̄) - c m_P)}` on forms `f` of degree `c` satisfies the
hypotheses of the graded extension lemma (`ProjBerk.IsGradedNorm`): it is multiplicative and
ultrametric because `ord_P` is a valuation, `1` on nonzero constants, and `max_j N_t(xⱼ) = 1` by
the choice of `m_P`. The resulting point `v_{P,t}` (`ProjSubvariety.divPoint`) lies in `X^an`
since `N_t` vanishes on `I`, and `|σ|_{v_{P,t}} > 0` for `σ ∉ I`.

## Division from growth (`lem:pg-division`)

If `X` is projectively normal, `σ ∉ I` is a form of degree `e`, `τ` a form of degree `N e`, and
`log|τ| - N log|σ| ≤ -β log|σ| + C` on `U_σ ∩ X^an` with `β ≥ 0`, then `σ̄^{N'}` divides `τ̄` in
`S` for `N' = ⌊N - β⌋₊`. Indeed `S` is a Noetherian integrally closed domain, so by
`lem:bj-dvr-minimal` (`EnvelopeProperty.mem_span_singleton_iff_forall_minimalPrimes_dvd`) it
suffices that `ord_P(τ̄) ≥ N' ord_P(σ̄)` for the minimal primes `P` of `σ̄^{N'} S`, at which `S_P`
is a discrete valuation ring. At `v_{P,t}` the hypothesis reads
`t ((N - β) ord_P σ̄ + β e m_P - ord_P τ̄) ≤ C` for all `t > 0`, whence
`ord_P τ̄ ≥ (N - β) ord_P σ̄ ≥ N' ord_P σ̄`. Finally, comparing homogeneous components of degree
`N e` modulo the homogeneous ideal `I` gives a form `τ'` of degree `(N - N') e` with
`τ ≡ σ^{N'} τ' (mod I)`.

## Main definitions

* `ProjSubvariety.ordAt`, `ProjSubvariety.minOrd`, `ProjSubvariety.divNorm`.
* `ProjSubvariety.divPoint X P ht : X.an` (`lem:pg-div-points`).

## Main results

* `ProjSubvariety.isGradedNorm_divNorm`, `ProjSubvariety.divPoint_val_of_isHomogeneous`,
  `ProjSubvariety.log_divPoint_val`, `ProjSubvariety.divPoint_val_ne_zero` (`lem:pg-div-points`).
* `ProjSubvariety.pow_dvd_mk_of_log_le` (divisibility in `S`),
  `ProjSubvariety.exists_isHomogeneous_sub_pow_mul_mem_of_log_le` (real form) and
  `ProjSubvariety.exists_isHomogeneous_sub_pow_mul_mem` (`EReal` form of the blueprint)
  (`lem:pg-division`).

## Deviations from the blueprint

* `lem:pg-div-points`: the point is in `U_σ` for every `σ ∉ I`, homogeneous or not.
* `lem:pg-division`: the hypotheses `e ≥ 1` and `β ≤ N` are dropped. With the natural floor
  `⌊N - β⌋₊` (which is `0` for `β > N`) the statement holds without them. The hypothesis `β ≥ 0`
  is needed (it is used to discard `β e m_P ≥ 0`). The real form assumes the growth bound only at
  points where `|σ| ≠ 0` and `|τ| ≠ 0`.
-/

open scoped NNReal ENNReal Topology

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-- `e^{-t} e^{t} = 1`. -/
theorem expNeg_mul_expNeg_neg (t : ℝ) : expNeg t * expNeg (-t) = 1 := by
  refine NNReal.eq ?_
  change Real.exp (-t) * Real.exp (-(-t)) = 1
  rw [← Real.exp_add, neg_neg, neg_add_cancel, Real.exp_zero]

open ProjBerk

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### The points `v_{P,t}` (`lem:pg-div-points`) -/

section DivPoint

variable (P : Ideal (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal)) [P.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- The order `ord_P(f̄) ∈ ℕ∞` of the image of `f ∈ R_M` in `S = R_M / I` along a prime `P` of `S`
whose localization is a discrete valuation ring. -/
def ordAt (f : MvPolynomial (Fin (M + 1)) k) : ℕ∞ :=
  IsDiscreteValuationRing.addVal (Localization.AtPrime P)
    (algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk X.ideal f))

theorem ordAt_eq_top_iff {f : MvPolynomial (Fin (M + 1)) k} :
    X.ordAt P f = ⊤ ↔ f ∈ X.ideal := by
  rw [ordAt, IsDiscreteValuationRing.addVal_eq_top_iff,
    map_eq_zero_iff _ (IsLocalization.injective (Localization.AtPrime P)
      P.primeCompl_le_nonZeroDivisors), Ideal.Quotient.eq_zero_iff_mem]

theorem ordAt_mul (f g : MvPolynomial (Fin (M + 1)) k) :
    X.ordAt P (f * g) = X.ordAt P f + X.ordAt P g := by
  simp only [ordAt, map_mul, IsDiscreteValuationRing.addVal_mul]

theorem min_le_ordAt_add (f g : MvPolynomial (Fin (M + 1)) k) :
    min (X.ordAt P f) (X.ordAt P g) ≤ X.ordAt P (f + g) := by
  simp only [ordAt, map_add]
  exact IsDiscreteValuationRing.addVal_add

theorem ordAt_pow (f : MvPolynomial (Fin (M + 1)) k) (n : ℕ) :
    X.ordAt P (f ^ n) = n • X.ordAt P f := by
  simp only [ordAt, map_pow, IsDiscreteValuationRing.addVal_pow]

theorem ordAt_C {c : k} (hc : c ≠ 0) : X.ordAt P (C c) = 0 := by
  rw [ordAt, IsDiscreteValuationRing.addVal_eq_zero_iff]
  refine IsUnit.map _ (IsUnit.map _ ?_)
  exact (isUnit_iff_ne_zero.2 hc).map C

/-- `m_P = min_j ord_P(x̄_j)` (as a natural number; the minimum is finite since some
`xⱼ ∉ I`). -/
def minOrd : ℕ :=
  (Finset.univ.inf fun i => X.ordAt P (MvPolynomial.X i)).toNat

theorem inf_ordAt_X_ne_top : (Finset.univ.inf fun i => X.ordAt P (MvPolynomial.X i)) ≠ ⊤ := by
  obtain ⟨i, hi⟩ := X.exists_X_notMem
  refine ne_top_of_le_ne_top ?_ (Finset.inf_le (Finset.mem_univ i))
  rwa [Ne, ordAt_eq_top_iff]

theorem minOrd_le_ordAt_X (i : Fin (M + 1)) :
    (X.minOrd P : ℕ∞) ≤ X.ordAt P (MvPolynomial.X i) := by
  rw [minOrd, ENat.natCast_toNat (X.inf_ordAt_X_ne_top P)]
  exact Finset.inf_le (Finset.mem_univ i)

theorem exists_ordAt_X_eq_minOrd :
    ∃ i, X.ordAt P (MvPolynomial.X i) = X.minOrd P := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset (Fin (M + 1)))
    Finset.univ_nonempty fun i => X.ordAt P (MvPolynomial.X i)
  refine ⟨i, ?_⟩
  rw [minOrd, ENat.natCast_toNat (X.inf_ordAt_X_ne_top P), hi]

/-- The family `N_t(f) = e^{-t (ord_P(f̄) - c m_P)}` on forms `f` of degree `c`, written
`e^{-t ord_P(f̄)} (e^{t})^{c m_P}` (with `e^{-∞} = 0`). -/
def divNorm (t : ℝ) (c : ℕ) (f : MvPolynomial (Fin (M + 1)) k) : ℝ≥0 :=
  expOrd (expNeg t) (X.ordAt P f) * expNeg (-t) ^ (c * X.minOrd P)

/-- For `t ≥ 0` the family `N_t` satisfies the hypotheses of the graded extension lemma
(`lem:bj-graded-extension`). -/
theorem isGradedNorm_divNorm {t : ℝ} (ht : 0 ≤ t) : IsGradedNorm (X.divNorm P t) where
  map_zero d := by
    rw [divNorm, (X.ordAt_eq_top_iff P).2 X.ideal.zero_mem, expOrd_top, zero_mul]
  map_C c hc := by rw [divNorm, X.ordAt_C P hc, expOrd_zero, zero_mul, pow_zero, mul_one]
  map_mul {d e} {f g} _ _ := by
    simp only [divNorm, X.ordAt_mul, expOrd_add, add_mul, pow_add]
    ring
  map_add_le {d} {f g} _ _ := by
    simp only [divNorm]
    rw [← max_mul_of_nonneg _ _ zero_le, ← (expOrd_antitone (expNeg_le_one ht)).map_min]
    exact mul_le_mul_of_nonneg_right
      (expOrd_antitone (expNeg_le_one ht) (X.min_le_ordAt_add P f g)) zero_le
  sup_X := by
    have hle : ∀ i, X.divNorm P t 1 (MvPolynomial.X i) ≤ 1 := by
      intro i
      have hi := X.minOrd_le_ordAt_X P i
      rw [divNorm, one_mul]
      induction h : X.ordAt P (MvPolynomial.X i) using ENat.recTopCoe with
      | top => rw [expOrd_top, zero_mul]; exact zero_le_one
      | coe n =>
        rw [h, Nat.cast_le] at hi
        rw [expOrd_coe, ← Nat.sub_add_cancel hi, pow_add, mul_assoc, ← mul_pow,
          expNeg_mul_expNeg_neg, one_pow, mul_one]
        exact pow_le_one₀ zero_le (expNeg_le_one ht)
    refine le_antisymm (Finset.sup_le fun i _ => hle i) ?_
    obtain ⟨i, hi⟩ := X.exists_ordAt_X_eq_minOrd P
    refine le_trans ?_ (Finset.le_sup (f := fun i => X.divNorm P t 1 (MvPolynomial.X i))
      (Finset.mem_univ i))
    simp only [divNorm, hi, expOrd_coe, one_mul, ← mul_pow, expNeg_mul_expNeg_neg, one_pow,
      le_refl]

/-- **The divisorial point `v_{P,t}`** (`lem:pg-div-points`): the graded extension of
`|f| = e^{-t (ord_P(f̄) - c m_P)}` on forms `f` of degree `c`; it lies in `X^an`. -/
def divPoint {t : ℝ} (ht : 0 ≤ t) : X.an :=
  ⟨ofGradedNorm (X.isGradedNorm_divNorm P ht), by
    change _ ∈ zeroLocus X.ideal
    refine (mem_zeroLocus_iff X.isHomogeneousIdeal).2 fun D f hf hfI => ?_
    rw [ofGradedNorm_val_of_isHomogeneous _ hf, divNorm, (X.ordAt_eq_top_iff P).2 hfI,
      expOrd_top, zero_mul]⟩

variable {P}

theorem divPoint_val_of_isHomogeneous {t : ℝ} (ht : 0 ≤ t) {c : ℕ}
    {f : MvPolynomial (Fin (M + 1)) k} (hf : f.IsHomogeneous c) :
    (X.divPoint P ht : ProjBerk k M).1.val f = X.divNorm P t c f :=
  ofGradedNorm_val_of_isHomogeneous _ hf

/-- `log|f|_{v_{P,t}} = -t (ord_P(f̄) - c m_P)` for a form `f ∉ I` of degree `c`
(`lem:pg-div-points`). -/
theorem log_divPoint_val {t : ℝ} (ht : 0 ≤ t) {c : ℕ} {f : MvPolynomial (Fin (M + 1)) k}
    (hf : f.IsHomogeneous c) (hfI : f ∉ X.ideal) :
    Real.log ((X.divPoint P ht : ProjBerk k M).1.val f) =
      -t * (((X.ordAt P f).toNat : ℝ) - c * X.minOrd P) := by
  have hne : X.ordAt P f ≠ ⊤ := fun h => hfI ((X.ordAt_eq_top_iff P).1 h)
  rw [X.divPoint_val_of_isHomogeneous ht hf, divNorm, ← ENat.natCast_toNat hne, expOrd_coe,
    NNReal.coe_mul, Real.log_mul, log_expNeg_pow, log_expNeg_pow]
  · simp only [ENat.toNat_natCast]
    push_cast
    ring
  · exact (NNReal.coe_pos.2 (pow_pos (expNeg_pos t) _)).ne'
  · exact (NNReal.coe_pos.2 (pow_pos (expNeg_pos (-t)) _)).ne'

/-- `|σ|_{v_{P,t}} ≠ 0` for every `σ ∉ I`: `v_{P,t} ∈ U_σ` (`lem:pg-div-points`). -/
theorem divPoint_val_ne_zero {t : ℝ} (ht : 0 ≤ t) {σ : MvPolynomial (Fin (M + 1)) k}
    (hσI : σ ∉ X.ideal) : (X.divPoint P ht : ProjBerk k M).1.val σ ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, homogeneousComponent c σ ∉ X.ideal := by
    by_contra! h
    exact hσI (mem_of_forall_homogeneousComponent_mem h)
  have hne : X.ordAt P (homogeneousComponent c σ) ≠ ⊤ := fun h =>
    hc ((X.ordAt_eq_top_iff P).1 h)
  refine (lt_of_lt_of_le ?_ ((X.isGradedNorm_divNorm P ht).le_gradedFun σ c)).ne'
  rw [divNorm, ← ENat.natCast_toNat hne, expOrd_coe]
  exact mul_pos (pow_pos (expNeg_pos t) _) (pow_pos (expNeg_pos (-t)) _)

end DivPoint

/-! ### Division from growth (`lem:pg-division`) -/

section Division

variable {X}

/-- **Division from growth**, divisibility in `S = R_M / I` (`lem:pg-division`). Let `X` be
projectively normal, `σ ∉ I` a form of degree `e`, `τ` a form of degree `N e`, and `β ≥ 0` with
`log|τ| - N log|σ| ≤ -β log|σ| + C` at every point of `X^an` where `|σ| ≠ 0` and `|τ| ≠ 0`. Then
`σ̄^{⌊N - β⌋₊}` divides `τ̄` in `S`. -/
theorem pow_dvd_mk_of_log_le (hX : X.IsProjNormal) {e : ℕ}
    {σ τ : MvPolynomial (Fin (M + 1)) k} (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) {N : ℕ}
    (hτ : τ.IsHomogeneous (N * e)) {β C : ℝ} (hβ : 0 ≤ β)
    (h : ∀ v : X.an, (v : ProjBerk k M).1.val σ ≠ 0 → (v : ProjBerk k M).1.val τ ≠ 0 →
      Real.log ((v : ProjBerk k M).1.val τ) - N * Real.log ((v : ProjBerk k M).1.val σ) ≤
        -β * Real.log ((v : ProjBerk k M).1.val σ) + C) :
    Ideal.Quotient.mk X.ideal σ ^ ⌊(N : ℝ) - β⌋₊ ∣ Ideal.Quotient.mk X.ideal τ := by
  by_cases hτI : τ ∈ X.ideal
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hτI]
    exact dvd_zero _
  have : IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal) := hX
  set N' := ⌊(N : ℝ) - β⌋₊
  have hσ0 : Ideal.Quotient.mk X.ideal σ ≠ 0 := fun h0 =>
    hσI (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hh : Ideal.Quotient.mk X.ideal σ ^ N' ≠ 0 := pow_ne_zero _ hσ0
  rw [← Ideal.mem_span_singleton, mem_span_singleton_iff_forall_minimalPrimes_dvd hh]
  intro P _ hP
  have := isDiscreteValuationRing_localization_of_mem_minimalPrimes hh hP
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, map_pow, IsDiscreteValuationRing.addVal_pow]
  change N' • X.ordAt P σ ≤ X.ordAt P τ
  have hσne : X.ordAt P σ ≠ ⊤ := fun h0 => hσI ((X.ordAt_eq_top_iff P).1 h0)
  have hτne : X.ordAt P τ ≠ ⊤ := fun h0 => hτI ((X.ordAt_eq_top_iff P).1 h0)
  set nσ := (X.ordAt P σ).toNat
  set nτ := (X.ordAt P τ).toNat
  set m := X.minOrd P
  -- the growth bound at the points `v_{P,t}`
  have hK : ((N : ℝ) - β) * nσ + β * e * m - nτ ≤ 0 := by
    refine nonpos_of_forall_mul_le (C := C) fun t ht => ?_
    have h₁ := h (X.divPoint P ht.le) (X.divPoint_val_ne_zero ht.le hσI)
      (X.divPoint_val_ne_zero ht.le hτI)
    rw [X.log_divPoint_val ht.le hσ hσI, X.log_divPoint_val ht.le hτ hτI] at h₁
    push_cast at h₁
    linear_combination h₁
  have hm : (0 : ℝ) ≤ β * e * m := by positivity
  have hnσ : (0 : ℝ) ≤ nσ := Nat.cast_nonneg _
  have key : ((N' * nσ : ℕ) : ℝ) ≤ nτ := by
    push_cast
    rcases le_or_gt 0 ((N : ℝ) - β) with hNβ | hNβ
    · calc (N' : ℝ) * nσ ≤ ((N : ℝ) - β) * nσ :=
            mul_le_mul_of_nonneg_right (Nat.floor_le hNβ) hnσ
        _ ≤ nτ := by linarith
    · have hN0 : N' = 0 := Nat.floor_eq_zero.2 (hNβ.trans one_pos)
      rw [hN0, Nat.cast_zero, zero_mul]
      exact Nat.cast_nonneg _
  have key' : N' * nσ ≤ nτ := by exact_mod_cast key
  rw [← ENat.natCast_toNat hσne, ← ENat.natCast_toNat hτne, nsmul_eq_mul, ← Nat.cast_mul,
    Nat.cast_le]
  exact key'

/-- **Division from growth** (`lem:pg-division`), real form: under the hypotheses of
`pow_dvd_mk_of_log_le`, with `N' = ⌊N - β⌋₊`, there is a form `τ'` of degree `(N - N') e` with
`τ - σ^{N'} τ' ∈ I`. -/
theorem exists_isHomogeneous_sub_pow_mul_mem_of_log_le (hX : X.IsProjNormal) {e : ℕ}
    {σ τ : MvPolynomial (Fin (M + 1)) k} (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) {N : ℕ}
    (hτ : τ.IsHomogeneous (N * e)) {β C : ℝ} (hβ : 0 ≤ β)
    (h : ∀ v : X.an, (v : ProjBerk k M).1.val σ ≠ 0 → (v : ProjBerk k M).1.val τ ≠ 0 →
      Real.log ((v : ProjBerk k M).1.val τ) - N * Real.log ((v : ProjBerk k M).1.val σ) ≤
        -β * Real.log ((v : ProjBerk k M).1.val σ) + C) :
    ∃ τ' : MvPolynomial (Fin (M + 1)) k, τ'.IsHomogeneous ((N - ⌊(N : ℝ) - β⌋₊) * e) ∧
      τ - σ ^ ⌊(N : ℝ) - β⌋₊ * τ' ∈ X.ideal := by
  set N' := ⌊(N : ℝ) - β⌋₊ with hN'_def
  have hN' : N' ≤ N := Nat.floor_le_of_le (by linarith)
  obtain ⟨r, hr⟩ := pow_dvd_mk_of_log_le hX hσ hσI hτ hβ h
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hmem : τ - σ ^ N' * ρ ∈ X.ideal := by
    rw [← map_pow, ← map_mul] at hr
    exact Ideal.Quotient.eq.1 hr
  refine ⟨homogeneousComponent ((N - N') * e) ρ, homogeneousComponent_isHomogeneous _ _, ?_⟩
  have h₁ := X.isHomogeneousIdeal _ hmem (N * e)
  have hdeg : e * N' + (N - N') * e = N * e := by
    rw [mul_comm e N', ← add_mul, Nat.add_sub_cancel' hN']
  rwa [map_sub, homogeneousComponent_eq_self hτ, ← hdeg,
    homogeneousComponent_mul_of_isHomogeneous (hσ.pow N')] at h₁

/-- **Division from growth** (`lem:pg-division`), in the `EReal` form of the blueprint: if `X` is
projectively normal, `σ ∉ I` a form of degree `e`, `τ` a form of degree `N e`, `β ≥ 0`, and
`log|τ| - N log|σ| ≤ -β log|σ| + C` on `U_σ ∩ X^an`, then for `N' = ⌊N - β⌋₊` there is a form
`τ'` of degree `(N - N') e` with `τ - σ^{N'} τ' ∈ I`. -/
theorem exists_isHomogeneous_sub_pow_mul_mem (hX : X.IsProjNormal) {e : ℕ}
    {σ τ : MvPolynomial (Fin (M + 1)) k} (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) {N : ℕ}
    (hτ : τ.IsHomogeneous (N * e)) {β C : ℝ} (hβ : 0 ≤ β)
    (h : ∀ v : X.an, (v : ProjBerk k M).1.val σ ≠ 0 →
      logAbs τ v.1 - (N : EReal) * logAbs σ v.1 ≤ -(β : EReal) * logAbs σ v.1 + (C : EReal)) :
    ∃ τ' : MvPolynomial (Fin (M + 1)) k, τ'.IsHomogeneous ((N - ⌊(N : ℝ) - β⌋₊) * e) ∧
      τ - σ ^ ⌊(N : ℝ) - β⌋₊ * τ' ∈ X.ideal := by
  refine exists_isHomogeneous_sub_pow_mul_mem_of_log_le (C := C) hX hσ hσI hτ hβ
    fun v hσv hτv => ?_
  have h₁ := h v hσv
  rw [logAbs_def, logAbs_def, ENNReal.log_of_nnreal hσv, ENNReal.log_of_nnreal hτv] at h₁
  rw [← EReal.coe_natCast, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h₁
  exact h₁

end Division

end ProjSubvariety

end EnvelopeProperty
