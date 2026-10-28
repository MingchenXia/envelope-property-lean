/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.TestIdeal.PBasisRoot

/-!
# `p`-bases of polynomial and Laurent polynomial rings

Let `A` be a commutative ring of prime characteristic `p` with a finite `p`-basis `u : σ → A`.
This file proves `lem:sg-pbasis-basics`(4) of the blueprint (`subsec:sg-pbasis`, used for the
charts `(A_i)_h[x̄_i^{±1}][t]` of the cone over a smooth projective variety in the proof of
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Theorem 3.1):

* `IsPBasis.polynomial`: `(u, X)` is a `p`-basis of `A[X]` (indexed by `Option σ`, `none ↦ X`).
  The monomials `u^a X^r` (`a ∈ [0,p)^σ`, `r < p`) span `A[X]` over `A[X]^p`, because the span
  contains `A^p`, the `u_i` and `X` and is closed under products; they are independent, since the
  coefficient of `X^{pk+r}` in `∑ c_{a,r'}^p u^a X^{r'}` is `∑_a (c_{a,r})_k^p u^a`
  (`coeff_pow_char_mul_X_pow`).
* `IsPBasis.laurentPolynomial`: `(u, T)` is a `p`-basis of `A[T, T⁻¹]`, the localization of
  `A[T]` at `T` (`IsPBasis.map_algebraMap_of_isLocalization`).
* `IsPBasis.polynomial_laurentPolynomial`: `(u, Y, t)` is a `p`-basis of `A[Y, Y⁻¹][t]`.
* `IsPBasis.traceIter_polynomial_C_mul_X_pow`, `IsPBasis.traceIter_laurentPolynomial_C_mul_T`:
  the iterated traces on monomials, `Φ^e(c X^n) = Φ_u^e(c) X^{⌊n/Q⌋}` if `n ≡ Q - 1 (mod Q)` and
  `0` otherwise (`Q = p^e`, `n ∈ ℕ` resp. `n ∈ ℤ`); these give the bidegree shifts of the traces
  on the bigraded charts.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Polynomial rings -/

section Polynomial

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A}

omit [Fintype σ] [DecidableEq σ] in
/-- `coeff (c^p X^{r'}) (pk + r) = [r' = r] (coeff c k)^p` for `r, r' < p`. -/
theorem coeff_pow_char_mul_X_pow (c : A[X]) {r r' : ℕ} (hr : r < p) (hr' : r' < p) (k : ℕ) :
    (c ^ p * X ^ r').coeff (p * k + r) = if r' = r then c.coeff k ^ p else 0 := by
  induction c using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [add_pow_char, add_mul, coeff_add, hf, hg, coeff_add, add_pow_char]
    split_ifs <;> simp
  | monomial j a =>
    have hp0 : 0 < p := hp.out.pos
    have key : j * p + r' = p * k + r ↔ j = k ∧ r' = r := by
      constructor
      · intro h
        rw [mul_comm j p] at h
        have h1 := congrArg (· % p) h
        have h2 := congrArg (· / p) h
        simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h1
        simp only [Nat.mul_add_div hp0, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr',
          add_zero] at h2
        exact ⟨h2, h1⟩
      · rintro ⟨rfl, rfl⟩
        ring
    rw [monomial_pow, X_pow_eq_monomial, monomial_mul_monomial, mul_one, coeff_monomial,
      coeff_monomial]
    simp only [key]
    by_cases hjk : j = k <;> by_cases hrr : r' = r <;>
      simp [hjk, hrr, zero_pow hp.out.ne_zero]

omit hp in
/-- Splitting a sum over `[0,p)^{Option σ}` into the `none`-digit and the `[0,p)^σ`-part. -/
theorem sum_box_option {M : Type*} [AddCommMonoid M] (F : Box (Option σ) p → M) :
    ∑ a, F a = ∑ r : Fin p, ∑ b : Box σ p, F fun o => o.elim r b := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv Equiv.piOptionEquivProd _ _ fun a => ?_
  congr 1
  funext o
  cases o <;> rfl

omit [DecidableEq σ] in
/-- The monomials of the family `(u, X)` of `A[X]`: `(u, X)^n = X^{n(none)} C(u^{n ∘ some})`. -/
theorem mono_option_elim_X_C (u : σ → A) (n : Option σ → ℕ) :
    mono (fun o : Option σ => o.elim (X : A[X]) fun i => C (u i)) n =
      X ^ n none * C (mono u fun i => n (some i)) := by
  rw [mono, Fintype.prod_option, mono, map_prod]
  simp [map_pow]

/-- **`p`-bases of polynomial rings** (`lem:sg-pbasis-basics`(4)): if `u` is a `p`-basis of `A`,
then `(u, X)` is a `p`-basis of `A[X]`, indexed by `Option σ` with `none ↦ X`. -/
theorem IsPBasis.polynomial (hu : IsPBasis p u) :
    IsPBasis p (fun o : Option σ => o.elim (X : A[X]) fun i => C (u i)) := by
  set y : Option σ → A[X] := fun o => o.elim X fun i => C (u i) with hy
  have hmono : ∀ n : Option σ → ℕ, mono y n = X ^ n none * C (mono u fun i => n (some i)) :=
    mono_option_elim_X_C u
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have key : ∀ (r : Fin p) (k : ℕ),
        pSum p u (fun b => (c fun o => o.elim r b).coeff k) = 0 := by
      intro r k
      have h := congrArg (fun f : A[X] => f.coeff (p * k + r)) hc
      simp only [pSum_apply, finsetSum_coeff, coeff_zero] at h
      rw [← h, pSum_apply, sum_box_option, sum_eq_single r]
      · refine sum_congr rfl fun b _ => ?_
        rw [hmono, ← mul_assoc, coeff_mul_C]
        simp only [Box.toNat_apply, Option.elim]
        rw [coeff_pow_char_mul_X_pow _ r.2 r.2, if_pos rfl]
        rfl
      · intro r' _ hr'
        refine sum_eq_zero fun b _ => ?_
        rw [hmono, ← mul_assoc, coeff_mul_C]
        simp only [Box.toNat_apply, Option.elim]
        rw [coeff_pow_char_mul_X_pow _ r.2 r'.2, if_neg (fun h => hr' (Fin.ext h)), zero_mul]
      · simp
    funext a
    ext k
    have h1 := congrFun (hu.injective ((key (a none) k).trans (map_zero _).symm))
      fun i => a (some i)
    have ha : (fun o : Option σ => o.elim (a none) fun i => a (some i)) = a := by
      funext o
      cases o <;> rfl
    simp only [ha, Pi.zero_apply] at h1
    simpa using h1
  · intro f
    refine AddMonoidHom.mem_mrange.1 ?_
    have hC : ∀ a : A, C a ∈ AddMonoidHom.mrange (pSum p y) := by
      intro a
      rw [← hu.sum_coeff a, map_sum]
      refine AddSubmonoid.sum_mem _ fun b _ => ?_
      rw [map_mul, map_pow]
      refine pow_mul_mem_range_pSum p y _ ?_
      convert mono_mem_range_pSum p y (fun o => o.elim 0 b.toNat) using 1
      rw [hmono]
      simp only [Option.elim, pow_zero, one_mul]
    have hX : ∀ n : ℕ, (X : A[X]) ^ n ∈ AddMonoidHom.mrange (pSum p y) := by
      intro n
      convert mono_mem_range_pSum p y (fun o => o.elim n 0) using 1
      rw [hmono]
      simp [mono]
    induction f using Polynomial.induction_on' with
    | add f g hf hg => exact add_mem hf hg
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      exact mul_mem_range_pSum p y (hC a) (hX n)

/-- The iterated trace of `(u, X)` on `c X^n`: `Φ^e(c X^n) = Φ_u^e(c) X^{⌊n/Q⌋}` if
`n ≡ Q - 1 (mod Q)`, and `0` otherwise (`Q = p^e`). -/
theorem IsPBasis.traceIter_polynomial_C_mul_X_pow (hu : IsPBasis p u) (e : ℕ) (c : A) (n : ℕ) :
    hu.polynomial.traceIter e (C c * X ^ n) =
      if n % p ^ e = p ^ e - 1 then C (hu.traceIter e c) * X ^ (n / p ^ e) else 0 := by
  have hq0 : 0 < p ^ e := pow_pos hp.out.pos e
  have hterm : ∀ a : Box σ (p ^ e),
      C (hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * c) ^ p ^ e * mono u a.toNat) * X ^ n =
        C (hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * c)) ^ p ^ e *
          mono (fun o : Option σ => o.elim (X : A[X]) fun i => C (u i))
            (fun o => o.elim n a.toNat) := by
    intro a
    rw [mono_option_elim_X_C, map_mul, map_pow]
    simp only [Option.elim]
    ring
  have hcond : ∀ a : Box σ (p ^ e),
      (∀ o : Option σ, (o.elim n a.toNat) % p ^ e = p ^ e - 1) ↔
        n % p ^ e = p ^ e - 1 ∧ a = Box.top := by
    intro a
    rw [Option.forall]
    refine and_congr Iff.rfl ⟨fun h => funext fun i => Fin.ext ?_, fun h i => ?_⟩
    · have := h i
      simp only [Option.elim, Box.toNat_apply, Nat.mod_eq_of_lt (a i).2] at this
      exact this
    · subst h
      simp only [Option.elim, Box.toNat_apply]
      exact Nat.mod_eq_of_lt (by simp [Box.top]; omega)
  conv_lhs => rw [← hu.sum_traceIter_mul_mono e c, map_sum, sum_mul]
  rw [hu.polynomial.traceIter_sum]
  simp_rw [hterm, hu.polynomial.traceIter_pow_mul_mono]
  by_cases hn : n % p ^ e = p ^ e - 1
  · rw [if_pos hn, sum_eq_single Box.top]
    · rw [if_pos ((hcond _).2 ⟨hn, rfl⟩), mono_option_elim_X_C]
      simp only [Option.elim, Box.toNat_apply]
      have h1 : (fun i : σ => ((Box.top : Box σ (p ^ e)) i : ℕ) / p ^ e) = 0 := by
        funext i
        exact Nat.div_eq_of_lt (by simp [Box.top]; omega)
      have h2 : (fun i : σ => p ^ e - 1 - ((Box.top : Box σ (p ^ e)) i : ℕ)) = 0 := by
        funext i
        simp [Box.top]
      rw [h1, h2, mono_zero, map_one, mul_one, one_mul]
    · intro b _ hb
      rw [if_neg fun h => hb ((hcond b).1 h).2]
    · simp
  · rw [if_neg hn]
    exact sum_eq_zero fun b _ => if_neg fun h => hn ((hcond b).1 h).1

end Polynomial

/-! ### Laurent polynomial rings -/

section Laurent

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A}

/-- A Laurent polynomial ring over a ring of characteristic `p` has characteristic `p`. -/
instance laurentPolynomial_charP : CharP (LaurentPolynomial A) p :=
  charP_of_injective_ringHom (f := (Polynomial.toLaurent : A[X] →+* LaurentPolynomial A))
    Polynomial.toLaurent_injective p

/-- **`p`-bases of Laurent polynomial rings** (`lem:sg-pbasis-basics`(4)): if `u` is a `p`-basis
of `A`, then `(u, T)` is a `p`-basis of `A[T, T⁻¹]`, indexed by `Option σ` with `none ↦ T`. -/
theorem IsPBasis.laurentPolynomial (hu : IsPBasis p u) :
    IsPBasis p (fun o : Option σ =>
      o.elim (LaurentPolynomial.T 1 : LaurentPolynomial A) fun i => LaurentPolynomial.C (u i)) := by
  have h := hu.polynomial.map_algebraMap_of_isLocalization (Submonoid.powers (X : A[X]))
    (LaurentPolynomial A)
  convert h using 1
  funext o
  cases o with
  | none => simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
  | some i => simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]

omit [Fintype σ] [DecidableEq σ] in
/-- The family `(u, T)` of `A[T, T⁻¹]` is the image of the family `(u, X)` of `A[X]`. -/
theorem laurentPolynomial_family_eq_toLaurent_comp (u : σ → A) :
    (fun o : Option σ =>
      o.elim (LaurentPolynomial.T 1 : LaurentPolynomial A) fun i => LaurentPolynomial.C (u i)) =
      ⇑(Polynomial.toLaurent : A[X] →+* LaurentPolynomial A) ∘
        fun o : Option σ => o.elim (X : A[X]) fun i => C (u i) := by
  funext o
  cases o <;> simp [Polynomial.toLaurent_X, Polynomial.toLaurent_C]

/-- The iterated trace of `(u, T)` on `c T^n`, `n ∈ ℤ`: `Φ^e(c T^n) = Φ_u^e(c) T^{⌊n/Q⌋}` if
`n ≡ Q - 1 (mod Q)`, and `0` otherwise (`Q = p^e`). -/
theorem IsPBasis.traceIter_laurentPolynomial_C_mul_T (hu : IsPBasis p u) (e : ℕ) (c : A)
    (n : ℤ) :
    hu.laurentPolynomial.traceIter e (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      if n % (p : ℤ) ^ e = (p : ℤ) ^ e - 1 then
        LaurentPolynomial.C (hu.traceIter e c) * LaurentPolynomial.T (n / (p : ℤ) ^ e)
      else 0 := by
  have hq0 : 0 < p ^ e := pow_pos hp.out.pos e
  have hQz : (p : ℤ) ^ e = ((p ^ e : ℕ) : ℤ) := by push_cast; rfl
  rw [hQz]
  have hφ : IsPBasis p (⇑(Polynomial.toLaurent : A[X] →+* LaurentPolynomial A) ∘
      fun o : Option σ => o.elim (X : A[X]) fun i => C (u i)) :=
    laurentPolynomial_family_eq_toLaurent_comp u ▸ hu.laurentPolynomial
  -- write `T^n = (T^{-N})^Q T^m` with `m = n + Q N ≥ 0`
  set N : ℕ := n.natAbs
  have hm : 0 ≤ n + ((p ^ e : ℕ) : ℤ) * N := by
    have h1 : (N : ℤ) ≤ ((p ^ e : ℕ) : ℤ) * N :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast hq0)
    have h2 : -n ≤ (N : ℤ) := by simpa [N] using neg_le_abs n
    linarith
  set m : ℕ := (n + ((p ^ e : ℕ) : ℤ) * N).toNat
  have hmz : (m : ℤ) = n + ((p ^ e : ℕ) : ℤ) * N := Int.toNat_of_nonneg hm
  have hT : (LaurentPolynomial.T n : LaurentPolynomial A) =
      LaurentPolynomial.T (-(N : ℤ)) ^ p ^ e * LaurentPolynomial.T m := by
    rw [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add, hmz]
    congr 1
    push_cast
    ring
  have hcond : m % p ^ e = p ^ e - 1 ↔ n % ((p ^ e : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) - 1 := by
    rw [← Nat.cast_inj (R := ℤ), Int.natCast_mod, hmz, Int.add_mul_emod_self_left,
      Nat.cast_sub (by omega : 1 ≤ p ^ e), Nat.cast_one]
  have hdiv : ((m / p ^ e : ℕ) : ℤ) = n / ((p ^ e : ℕ) : ℤ) + N := by
    rw [Int.natCast_div, hmz, Int.add_mul_ediv_left _ _ (by exact_mod_cast hq0.ne')]
  rw [hT, mul_left_comm, hu.laurentPolynomial.traceIter_pow_mul,
    ← Polynomial.toLaurent_C_mul_X_pow,
    hu.laurentPolynomial.traceIter_congr hφ (laurentPolynomial_family_eq_toLaurent_comp u),
    hu.polynomial.traceIter_map _ hφ, hu.traceIter_polynomial_C_mul_X_pow]
  by_cases h : n % ((p ^ e : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) - 1
  · rw [if_pos (hcond.2 h), if_pos h, Polynomial.toLaurent_C_mul_X_pow, hdiv, mul_left_comm,
      ← LaurentPolynomial.T_add]
    congr 2
    ring
  · rw [if_neg (mt hcond.1 h), if_neg h, map_zero, mul_zero]

/-- `(u, Y, t)` is a `p`-basis of `A[Y, Y⁻¹][t]` (`lem:sg-pbasis-basics`(4)), indexed by
`Option (Option σ)` with `none ↦ t` and `some none ↦ Y`. -/
theorem IsPBasis.polynomial_laurentPolynomial (hu : IsPBasis p u) :
    IsPBasis p (fun o : Option (Option σ) => o.elim (X : (LaurentPolynomial A)[X]) fun o' =>
      C (o'.elim (LaurentPolynomial.T 1) fun i => LaurentPolynomial.C (u i))) :=
  hu.laurentPolynomial.polynomial

end Laurent

end EnvelopeProperty.Cartier
