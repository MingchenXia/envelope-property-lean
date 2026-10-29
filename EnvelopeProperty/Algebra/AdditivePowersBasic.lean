/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Additive powers in characteristic `0` (FHX Lemma 8.2; Roberts–Singh §4)

Let `A ⊆ B` be `ℚ`-algebras. Following Roberts–Singh, *Subintegrality, invertible modules and the
Picard group*, Compositio Math. 85 (1993), p. 258, an element `b ∈ B` is *subintegral over `A`*
if there are `c₁, …, c_d ∈ B` with
`aₘ = bᵐ + ∑_{i=1}^d binom(m, i) cᵢ b^{m-i} ∈ A` for all `m ≫ 0`
(`EnvelopeProperty.IsAddPowSubintegral`, "additively power subintegral").
The first assertion of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Lemma 8.2 (`lem:normalization-local-sandwich`; blueprint `thm:gl-additive-powers`) says that every
element of a subintegral extension `A ⊆ B` of `ℚ`-algebras has this property; FHX cite
[Roberts–Singh, Theorem 4.17, Proposition 4.2, Corollary 4.3]. Here "subintegral extension" is
the tower form: `B` is a directed union of finite towers
`A = A₀ ⊆ A₁ ⊆ ⋯ ⊆ Aₙ` with `A_{i+1} = A_i[e_i]` and `e_i², e_i³ ∈ A_i`.

## Main results

* `EnvelopeProperty.pow_mem_span_addPow`, `EnvelopeProperty.addPow_mem_span_pow`
  (**`lem:gl-lagrange`**, FHX Lemma 8.2, second part): `b^{n+2d} ∈ (a_{n+d}, …, a_{n+2d})` and
  `aₘ ∈ (b^{m-d})` for `m ≥ d`, by Lagrange interpolation over `ℚ`.
* `EnvelopeProperty.addPowSubintegralClosure`: the elements of `B` that are additively power
  subintegral over `A` form a `ℚ`-subalgebra containing `A` (Roberts–Singh (4.5), (4.8)).
* `EnvelopeProperty.IsAddPowSubintegral.of_sq_of_cube`: if `b²` and `b³` are additively power
  subintegral over `A`, so is `b` (Roberts–Singh (4.13)).
* `EnvelopeProperty.isAddPowSubintegral_of_mem_adjoin_insert` (**`rmk:gl-additive-powers`**):
  for an elementary step `e², e³ ∈ A`, every `b = α + βe` of `A[e]` satisfies
  `bᵐ - m βe b^{m-1} ∈ A` for `m ≥ 1` (`d = 1`, `c₁ = -βe`);
  `EnvelopeProperty.mem_adjoin_insert_iff_add_mul` gives `A[e] = A + Ae`.
* `EnvelopeProperty.isAddPowSubintegral_of_tower`,
  `EnvelopeProperty.isAddPowSubintegral_of_mem_adjoin`,
  `EnvelopeProperty.isAddPowSubintegral_of_forall_exists_tower` (**`thm:gl-additive-powers`**,
  Roberts–Singh (4.17) (ii)⇒(i)), for explicit chain data and directed unions of towers;
  `EnvelopeProperty.IsAddPowSubintegral.exists_le` adds `N ≥ d` as in FHX.

The same conclusion for the tower predicates `EnvelopeProperty.IsSubintegralChain` and
`EnvelopeProperty.Algebra.IsSubintegralTower` of `EnvelopeProperty.Algebra.SubintegralTower` is in
`EnvelopeProperty.Algebra.AdditivePowers`.

## Implementation notes: the route

Roberts–Singh prove (4.17) (ii)⇒(i) from (4.8) (sums via (4.5), which rests on (4.2)/(4.3) and
the universal Theorem (3.8) on invertible modules; products via (4.7)) and (4.13) (via the
finite-difference lemmas (4.10)–(4.12) and again (4.3)). We bypass (3.8) and (4.2)(ii)⇒(iii)
completely. The key observation (`EnvelopeProperty.AddPow.hasExactSystem_of_eventually`) is that
a relation that holds only for `r ≥ R`, possibly with negative "exponents" as in Roberts–Singh's
systems of exponent `s` (p. 258), becomes an *exact* system (valid for **all** `n ≥ 0`, exponent
`0`) after multiplying the `n`-th relation by the rational number `π(n)`, where
`π(X) = ∏_{j=1}^{R-1} (1 - X/j)`: `π(0) = 1`, `π` kills `n = 1, …, R-1`, and `π(X) f(X)` has
no binomial coordinates below `R` whenever `f(0) = 0`. With exact systems
(`EnvelopeProperty.AddPow.HasExactSystem`):

* sums are products of exponential generating functions `C(T) e^{bT}`;
* products follow from `binom(n,k) binom(n,l) b^{n-k} b'^{n-l}` and the cut-off trick;
* (4.13) is Lagrange interpolation of `binom(t, i) binom((r - 2t)/3, j)` along the line
  `2n + 3m = r` (Roberts–Singh (4.12), without the operators `ϑ`), followed by the cut-off trick.
-/

open Polynomial Finset

noncomputable section

namespace EnvelopeProperty

namespace AddPow

/-! ### Binomial polynomials and Newton expansions over `ℚ` -/

/-- The binomial polynomial `binom(X, k) = X(X-1)⋯(X-k+1)/k!` over `ℚ`. -/
def choosePoly (k : ℕ) : ℚ[X] := ((k.factorial : ℚ)⁻¹) • descPochhammer ℚ k

lemma choosePoly_eval_natCast (k n : ℕ) : (choosePoly k).eval (n : ℚ) = (n.choose k : ℚ) := by
  rw [choosePoly, eval_smul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

lemma choosePoly_eval_zero (k : ℕ) : (choosePoly k).eval 0 = if k = 0 then 1 else 0 := by
  rw [choosePoly, eval_smul, descPochhammer_eval_zero]
  split_ifs with h <;> simp [h]

lemma choosePoly_zero : choosePoly 0 = 1 := by simp [choosePoly]

lemma natDegree_choosePoly_le (k : ℕ) : (choosePoly k).natDegree ≤ k := by
  rw [choosePoly]
  exact (natDegree_smul_le _ _).trans (descPochhammer_natDegree ℚ k).le

/-- Iterated forward difference at `0` of a polynomial function: the `k`-th coordinate of `g` in
the binomial basis. -/
def fd (g : ℚ[X]) (k : ℕ) : ℚ := (fwdDiff 1)^[k] g.eval 0

lemma fd_zero (g : ℚ[X]) : fd g 0 = g.eval 0 := rfl

/-- Gregory–Newton expansion of a polynomial at a natural number. -/
lemma eval_natCast_eq_sum_fd (g : ℚ[X]) (n : ℕ) :
    g.eval (n : ℚ) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * fd g k := by
  have := shift_eq_sum_fwdDiff_iter (1 : ℚ) g.eval n 0
  simpa [fd, nsmul_eq_mul] using this

lemma fd_eq_zero_of_natDegree_lt {g : ℚ[X]} {k : ℕ} (h : g.natDegree < k) : fd g k = 0 := by
  simp [fd, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h]

lemma fd_eq_zero_of_eval_eq_zero {g : ℚ[X]} {R k : ℕ} (hg : ∀ j < R, g.eval (j : ℚ) = 0)
    (hk : k < R) : fd g k = 0 := by
  rw [fd, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_eq_zero fun j hj => ?_
  have : j < R := by have := Finset.mem_range.1 hj; omega
  simp [hg j this]

/-- Lagrange interpolation over `ℚ`: the value at `x` of a polynomial of degree `≤ D` is a fixed
`ℚ`-linear combination of its values at `D + 1` distinct nodes. -/
lemma eval_eq_sum_lagrange {D : ℕ} {v : ℕ → ℚ} (hv : Set.InjOn v (range (D + 1))) (x : ℚ)
    {g : ℚ[X]} (hg : g.natDegree ≤ D) :
    g.eval x = ∑ k ∈ range (D + 1), (Lagrange.basis (range (D + 1)) v k).eval x * g.eval (v k) := by
  have hdeg : g.degree < (range (D + 1)).card := by
    rw [card_range]
    calc g.degree ≤ (g.natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (D : WithBot ℕ) := by exact_mod_cast hg
      _ < ((D + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self D
  conv_lhs => rw [Lagrange.eq_interpolate hv hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, mul_comm]

/-! ### Exact systems -/

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- `b` has an *exact system of subintegrality* over `A`: a finitely supported `c : ℕ → B` with
`c 0 = 1` such that `∑_{k ≤ n} binom(n,k) c_k b^{n-k} ∈ A` for **every** `n ≥ 0`, i.e. a system
`(0, p, p; c₀, …, c_p)` of exponent `0` in the sense of Roberts–Singh, p. 258 (the systems
produced by their (4.2)(iv)⇒(i)). -/
def HasExactSystem (A : Subalgebra ℚ B) (b : B) : Prop :=
  ∃ c : ℕ → B, c 0 = 1 ∧ (∃ d, ∀ k, d < k → c k = 0) ∧
    ∀ n, ∑ k ∈ range (n + 1), (n.choose k : B) * c k * b ^ (n - k) ∈ A

omit [Algebra ℚ B] in
/-- For finitely supported `c`, the binomial sum can be taken over a fixed range. -/
lemma sum_range_choose_eq (c : ℕ → B) {p : ℕ} (hp : ∀ k, p < k → c k = 0) (F : ℕ → B) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : B) * c k * F k =
      ∑ k ∈ range (p + 1), (n.choose k : B) * c k * F k := by
  have h1 : ∑ k ∈ range (n + 1), (n.choose k : B) * c k * F k =
      ∑ k ∈ range (n + p + 1), (n.choose k : B) * c k * F k := by
    apply Finset.sum_subset (range_subset_range.2 (by omega))
    intro k _ hk
    rw [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have h2 : ∑ k ∈ range (p + 1), (n.choose k : B) * c k * F k =
      ∑ k ∈ range (n + p + 1), (n.choose k : B) * c k * F k := by
    apply Finset.sum_subset (range_subset_range.2 (by omega))
    intro k _ hk
    rw [mem_range, not_lt] at hk
    rw [hp k (by omega)]
    simp
  rw [h1, h2]

/-- `A` is a `ℚ`-subalgebra, so `m x ∈ A` with `m ≠ 0` implies `x ∈ A`. -/
lemma mem_of_natCast_smul_mem {A : Subalgebra ℚ B} {x : B} {m : ℕ} (hm : m ≠ 0)
    (h : (m : ℚ) • x ∈ A) : x ∈ A := by
  have : x = ((m : ℚ)⁻¹) • ((m : ℚ) • x) := by
    rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ h _

/-- The cut-off polynomial `π(X) = ∏_{j=1}^{R-1} (1 - X/j)`: `π(0) = 1` and `π(j) = 0` for
`0 < j < R`. -/
def cutoffPoly (R : ℕ) : ℚ[X] := ∏ j ∈ Ico 1 R, (1 - C ((j : ℚ)⁻¹) * X)

lemma cutoffPoly_eval_zero (R : ℕ) : (cutoffPoly R).eval 0 = 1 := by
  simp [cutoffPoly, eval_prod]

lemma cutoffPoly_eval_natCast {R j : ℕ} (h1 : 0 < j) (h2 : j < R) :
    (cutoffPoly R).eval (j : ℚ) = 0 := by
  rw [cutoffPoly, eval_prod]
  apply Finset.prod_eq_zero (i := j) (by simp [Finset.mem_Ico]; omega)
  have : (j : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
  simp [this]

lemma natDegree_cutoffPoly_le (R : ℕ) : (cutoffPoly R).natDegree ≤ R := by
  rw [cutoffPoly]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ Ico 1 R, (1 - C ((j : ℚ)⁻¹) * X).natDegree ≤ ∑ _j ∈ Ico 1 R, 1 := by
        apply Finset.sum_le_sum; intro j _
        compute_degree
    _ = R - 1 := by simp
    _ ≤ R := Nat.sub_le _ _

/-- **The cut-off trick.** Suppose that for all `r ≥ R`,
`b^r + ∑_{i ∈ S} f_i(r) w_i b^{r - e_i} ∈ A`, where `f_i ∈ ℚ[X]` with `f_i(0) = 0` and
`e_i ≤ R`. Then `b` has an exact system over `A`. (This covers Roberts–Singh's systems of
subintegrality of any exponent `s`, valid for `n ≥ N`; compare (4.2)(ii)⇒(i).) -/
theorem hasExactSystem_of_eventually {A : Subalgebra ℚ B} {b : B} {ι : Type*} (S : Finset ι)
    (f : ι → ℚ[X]) (w : ι → B) (e : ι → ℕ) (R : ℕ)
    (hf : ∀ i ∈ S, (f i).eval 0 = 0) (he : ∀ i ∈ S, e i ≤ R)
    (h : ∀ r, R ≤ r → b ^ r + ∑ i ∈ S, (f i).eval (r : ℚ) • (w i * b ^ (r - e i)) ∈ A) :
    HasExactSystem A b := by
  classical
  set π := cutoffPoly R with hπ
  let c : ℕ → B := fun k => fd π k • b ^ k + ∑ i ∈ S, fd (π * f i) k • (w i * b ^ (k - e i))
  refine ⟨c, ?_, ?_, ?_⟩
  · simp only [c, fd_zero, pow_zero, eval_mul, hπ, cutoffPoly_eval_zero, one_smul, one_mul]
    rw [Finset.sum_eq_zero (fun i hi => by simp [hf i hi]), add_zero]
  · refine ⟨R + S.sup (fun i => (f i).natDegree), fun k hk => ?_⟩
    have h1 : fd π k = 0 :=
      fd_eq_zero_of_natDegree_lt ((natDegree_cutoffPoly_le R).trans_lt (by omega))
    have h2 : ∀ i ∈ S, fd (π * f i) k = 0 := fun i hi => fd_eq_zero_of_natDegree_lt (by
      calc (π * f i).natDegree ≤ π.natDegree + (f i).natDegree := natDegree_mul_le
        _ ≤ R + S.sup (fun i => (f i).natDegree) :=
          add_le_add (natDegree_cutoffPoly_le R) (Finset.le_sup (f := fun i => (f i).natDegree) hi)
        _ < k := hk)
    simp only [c, h1, zero_smul, zero_add]
    exact Finset.sum_eq_zero (fun i hi => by rw [h2 i hi, zero_smul])
  · intro n
    have hvan : ∀ i ∈ S, ∀ j < R, (π * f i).eval (j : ℚ) = 0 := by
      intro i hi j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [hf i hi]
      · simp [hπ, cutoffPoly_eval_natCast hj0 hj]
    have key1 : ∑ k ∈ range (n + 1), (n.choose k : B) * (fd π k • b ^ k) * b ^ (n - k) =
        π.eval (n : ℚ) • b ^ n := by
      rw [eval_natCast_eq_sum_fd π n, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hp : b ^ n = b ^ k * b ^ (n - k) := by rw [← pow_add]; congr 1; omega
      rw [hp]
      simp only [Algebra.smul_def, map_mul, map_natCast]
      ring
    have key2 : ∀ i ∈ S, ∑ k ∈ range (n + 1),
        (n.choose k : B) * (fd (π * f i) k • (w i * b ^ (k - e i))) * b ^ (n - k) =
        (π * f i).eval (n : ℚ) • (w i * b ^ (n - e i)) := by
      intro i hi
      rw [eval_natCast_eq_sum_fd (π * f i) n, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      by_cases hkR : k < R
      · rw [fd_eq_zero_of_eval_eq_zero (hvan i hi) hkR]; simp
      · have hkR : R ≤ k := not_lt.1 hkR
        have hp : b ^ (n - e i) = b ^ (k - e i) * b ^ (n - k) := by
          rw [← pow_add]; congr 1; have := he i hi; omega
        rw [hp]
        simp only [Algebra.smul_def, map_mul, map_natCast]
        ring
    have hsum : ∑ k ∈ range (n + 1), (n.choose k : B) * c k * b ^ (n - k) =
        π.eval (n : ℚ) • (b ^ n + ∑ i ∈ S, (f i).eval (n : ℚ) • (w i * b ^ (n - e i))) := by
      simp only [c, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm, key1, Finset.sum_congr rfl key2]
      simp only [smul_add, Finset.smul_sum, smul_smul, eval_mul]
    rw [hsum]
    by_cases hnR : R ≤ n
    · exact Subalgebra.smul_mem _ (h n hnR) _
    · have hnR : n < R := not_le.1 hnR
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [Finset.sum_eq_zero (fun i hi => by simp [hf i hi])]
        simp [hπ, cutoffPoly_eval_zero]
      · rw [hπ, cutoffPoly_eval_natCast hn0 hnR, zero_smul]; exact Subalgebra.zero_mem _

/-- Elements of `A` have the trivial exact system `c = (1, 0, 0, …)`. -/
lemma HasExactSystem.of_mem {A : Subalgebra ℚ B} {b : B} (hb : b ∈ A) : HasExactSystem A b := by
  classical
  refine ⟨fun k => if k = 0 then 1 else 0, by simp, ⟨0, fun k hk => by simp [hk.ne']⟩,
    fun n => ?_⟩
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (fun h => by simp at h)]
  simpa using Subalgebra.pow_mem _ hb n

/-! ### Sums: exponential generating functions -/

/-- `n! [Tⁿ] (C(T) e^{bT}) = ∑_{k ≤ n} binom(n,k) c_k b^{n-k}` for `C(T) = ∑ c_k T^k / k!`. -/
lemma factorial_smul_coeff_egf_mul_exp (c : ℕ → B) (b : B) (n : ℕ) :
    (n.factorial : ℚ) • PowerSeries.coeff n
        (PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹) • c k) *
          PowerSeries.rescale b (PowerSeries.exp B)) =
      ∑ k ∈ range (n + 1), (n.choose k : B) * c k * b ^ (n - k) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hq : (n.factorial : ℚ) * (k.factorial : ℚ)⁻¹ * (1 / ((n - k).factorial : ℚ)) =
      (n.choose k : ℚ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    push_cast
    have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    field_simp
  calc (n.factorial : ℚ) • ((((k.factorial : ℚ)⁻¹) • c k) *
        (b ^ (n - k) * algebraMap ℚ B (1 / ((n - k).factorial : ℚ))))
      = algebraMap ℚ B ((n.factorial : ℚ) * (k.factorial : ℚ)⁻¹ *
          (1 / ((n - k).factorial : ℚ))) * c k * b ^ (n - k) := by
        simp only [Algebra.smul_def, map_mul]; ring
    _ = (n.choose k : B) * c k * b ^ (n - k) := by rw [hq, map_natCast]

/-- The coefficients of `C(T) e^{bT}` lie in `A` when the binomial sums do. -/
lemma coeff_egf_mul_exp_mem {A : Subalgebra ℚ B} {c : ℕ → B} {b : B}
    (hc : ∀ n, ∑ k ∈ range (n + 1), (n.choose k : B) * c k * b ^ (n - k) ∈ A) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹) • c k) *
      PowerSeries.rescale b (PowerSeries.exp B)) ∈ A := by
  refine mem_of_natCast_smul_mem n.factorial_ne_zero ?_
  rw [factorial_smul_coeff_egf_mul_exp]
  exact hc n

/-- Sums (Roberts–Singh (4.5)): exact systems multiply as exponential generating functions. -/
theorem HasExactSystem.add {A : Subalgebra ℚ B} {b b' : B} (hb : HasExactSystem A b)
    (hb' : HasExactSystem A b') : HasExactSystem A (b + b') := by
  obtain ⟨c, hc0, ⟨d, hd⟩, hc⟩ := hb
  obtain ⟨c', hc0', ⟨d', hd'⟩, hc'⟩ := hb'
  set C := PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹) • c k) with hC
  set C' := PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹) • c' k) with hC'
  refine ⟨fun t => (t.factorial : ℚ) • PowerSeries.coeff t (C * C'), ?_,
    ⟨d + d', fun t ht => ?_⟩, fun n => ?_⟩
  · simp [hC, hC', hc0, hc0']
  · show (t.factorial : ℚ) • PowerSeries.coeff t (C * C') = 0
    rw [PowerSeries.coeff_mul]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : d < p.1
    · simp [hC, hd _ h1]
    · have : d' < p.2 := by omega
      simp [hC', hd' _ this]
  · have hmk : PowerSeries.mk (fun t => ((t.factorial : ℚ)⁻¹) •
        ((t.factorial : ℚ) • PowerSeries.coeff t (C * C'))) = C * C' := by
      ext t
      rw [PowerSeries.coeff_mk, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast t.factorial_ne_zero), one_smul]
    rw [← factorial_smul_coeff_egf_mul_exp, hmk, ← PowerSeries.exp_mul_exp_eq_exp_add]
    have : C * C' * (PowerSeries.rescale b (PowerSeries.exp B) *
        PowerSeries.rescale b' (PowerSeries.exp B)) =
        (C * PowerSeries.rescale b (PowerSeries.exp B)) *
          (C' * PowerSeries.rescale b' (PowerSeries.exp B)) := by ring
    rw [this, PowerSeries.coeff_mul]
    exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun p _ =>
      Subalgebra.mul_mem _ (coeff_egf_mul_exp_mem hc _) (coeff_egf_mul_exp_mem hc' _)) _

/-! ### Products -/

/-- Products (Roberts–Singh (4.7), (4.8)): `aₙ a'ₙ = ∑ binom(n,k) binom(n,l) c_k c'_l b^{n-k}
b'^{n-l}` is of the shape required by the cut-off trick for `bb'`. -/
theorem HasExactSystem.mul {A : Subalgebra ℚ B} {b b' : B} (hb : HasExactSystem A b)
    (hb' : HasExactSystem A b') : HasExactSystem A (b * b') := by
  classical
  obtain ⟨c, hc0, ⟨d, hd⟩, hc⟩ := hb
  obtain ⟨c', hc0', ⟨d', hd'⟩, hc'⟩ := hb'
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ range (d + 1) ×ˢ range (d' + 1) := by simp
  refine hasExactSystem_of_eventually ((range (d + 1) ×ˢ range (d' + 1)).erase (0, 0))
    (fun p => choosePoly p.1 * choosePoly p.2)
    (fun p => c p.1 * c' p.2 * b ^ (max p.1 p.2 - p.1) * b' ^ (max p.1 p.2 - p.2))
    (fun p => max p.1 p.2) (max d d') ?_ ?_ ?_
  · intro p hp
    have hne := (Finset.mem_erase.1 hp).1
    simp only [eval_mul, choosePoly_eval_zero]
    by_cases h1 : p.1 = 0
    · have h2 : p.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      simp [h2]
    · simp [h1]
  · intro p hp
    have := (Finset.mem_erase.1 hp).2
    simp only [mem_product, mem_range] at this
    omega
  · intro r hr
    have hmem := Subalgebra.mul_mem _ (hc r) (hc' r)
    rw [sum_range_choose_eq c hd, sum_range_choose_eq c' hd', Finset.sum_mul_sum,
      ← Finset.sum_product', ← Finset.add_sum_erase _ _ h00] at hmem
    convert hmem using 2
    · simp [hc0, hc0', mul_pow]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_erase.1 hp).2
      simp only [mem_product, mem_range] at hp'
      have hm1 : b ^ (r - p.1) = b ^ (max p.1 p.2 - p.1) * b ^ (r - max p.1 p.2) := by
        rw [← pow_add]; congr 1; omega
      have hm2 : b' ^ (r - p.2) = b' ^ (max p.1 p.2 - p.2) * b' ^ (r - max p.1 p.2) := by
        rw [← pow_add]; congr 1; omega
      rw [hm1, hm2, eval_mul, choosePoly_eval_natCast, choosePoly_eval_natCast, mul_pow]
      simp only [Algebra.smul_def, map_mul, map_natCast]
      ring

/-! ### Roberts–Singh (4.13): `b², b³` subintegral implies `b` subintegral -/

/-- If `b²` and `b³` have exact systems over `A`, so does `b`. Lagrange interpolation of the
products `σₙ τₘ` (`2n + 3m = r`) at `n = r/2` gives `∑_i binom(r/2, i) c_i b^{r-2i} ∈ A` for all
large `r` (Roberts–Singh (4.12)); the cut-off trick removes the half-integer arguments. -/
theorem HasExactSystem.of_sq_of_cube {A : Subalgebra ℚ B} {b : B}
    (h2 : HasExactSystem A (b ^ 2)) (h3 : HasExactSystem A (b ^ 3)) : HasExactSystem A b := by
  classical
  obtain ⟨c, hc0, ⟨p, hp⟩, hc⟩ := h2
  obtain ⟨c', hc0', ⟨q, hq⟩, hc'⟩ := h3
  refine hasExactSystem_of_eventually ((range (p + 1)).erase 0)
    (fun i => (choosePoly i).comp (C (1 / 2 : ℚ) * X)) c (fun i => 2 * i) (6 * (p + q) + 6)
    ?_ ?_ ?_
  · intro i hi
    have := (Finset.mem_erase.1 hi).1
    simp [eval_comp, choosePoly_eval_zero, this]
  · intro i hi
    have := Finset.mem_range.1 (Finset.mem_erase.1 hi).2
    omega
  · intro r hr
    set D := p + q with hD
    -- nodes `n_k = n₀ + 3k` and `m_k = (r - 2 n_k) / 3` on the line `2n + 3m = r`
    set n₀ := (2 * r) % 3 with hn₀
    let nk : ℕ → ℕ := fun k => n₀ + 3 * k
    let mk : ℕ → ℕ := fun k => (r - 2 * nk k) / 3
    have hnm : ∀ k ∈ range (D + 1), 2 * nk k + 3 * mk k = r := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      simp only [nk, mk]
      omega
    let v : ℕ → ℚ := fun k => (nk k : ℚ)
    have hv : Set.InjOn v (range (D + 1)) := by
      intro k _ l _ hkl
      simp only [v, nk, Nat.cast_inj] at hkl
      omega
    set x : ℚ := 1 / 2 * (r : ℚ) with hx
    set L : ℕ → ℚ := fun k => (Lagrange.basis (range (D + 1)) v k).eval x with hL
    -- the interpolating polynomials
    let g : ℕ → ℕ → ℚ[X] := fun i j =>
      choosePoly i * (choosePoly j).comp (C ((r : ℚ) / 3) - C (2 / 3 : ℚ) * X)
    have hg_deg : ∀ i ≤ p, ∀ j ≤ q, (g i j).natDegree ≤ D := by
      intro i hi j hj
      have hlin : (C ((r : ℚ) / 3) - C (2 / 3 : ℚ) * X).natDegree ≤ 1 := by compute_degree
      calc (g i j).natDegree
          ≤ (choosePoly i).natDegree + ((choosePoly j).comp
              (C ((r : ℚ) / 3) - C (2 / 3 : ℚ) * X)).natDegree := natDegree_mul_le
        _ ≤ i + j * 1 := by
          rw [natDegree_comp]
          exact add_le_add (natDegree_choosePoly_le i)
            (Nat.mul_le_mul (natDegree_choosePoly_le j) hlin)
        _ ≤ D := by omega
    have hg_node : ∀ k ∈ range (D + 1), ∀ i j,
        (g i j).eval (v k) = ((nk k).choose i : ℚ) * ((mk k).choose j : ℚ) := by
      intro k hk i j
      have hrat : (r : ℚ) / 3 - 2 / 3 * (nk k : ℚ) = (mk k : ℚ) := by
        have := hnm k hk
        have h' : (2 * (nk k : ℚ) + 3 * (mk k : ℚ)) = r := by exact_mod_cast this
        linarith
      simp only [g, v, eval_mul, eval_comp, eval_sub, eval_C, eval_X, hrat,
        choosePoly_eval_natCast]
    have hg_x : ∀ i j, (g i j).eval x = (choosePoly i).eval x * (if j = 0 then 1 else 0) := by
      intro i j
      have h0 : (r : ℚ) / 3 - 2 / 3 * x = 0 := by rw [hx]; ring
      simp only [g, eval_mul, eval_comp, eval_sub, eval_C, eval_X, h0, choosePoly_eval_zero]
    -- the products `σ_{n_k} τ_{m_k}` expanded
    have hprod : ∀ k ∈ range (D + 1),
        (∑ i ∈ range (nk k + 1), ((nk k).choose i : B) * c i * (b ^ 2) ^ (nk k - i)) *
          (∑ j ∈ range (mk k + 1), ((mk k).choose j : B) * c' j * (b ^ 3) ^ (mk k - j)) =
        ∑ i ∈ range (p + 1), ∑ j ∈ range (q + 1),
          (((nk k).choose i : ℚ) * ((mk k).choose j : ℚ)) •
            (c i * c' j * b ^ (r - 2 * i - 3 * j)) := by
      intro k hk
      rw [sum_range_choose_eq c hp, sum_range_choose_eq c' hq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      have hnmk := hnm k hk
      by_cases hij : i ≤ nk k ∧ j ≤ mk k
      · have hpow : (b ^ 2) ^ (nk k - i) * (b ^ 3) ^ (mk k - j) = b ^ (r - 2 * i - 3 * j) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
        rw [← hpow]
        simp only [Algebra.smul_def, map_mul, map_natCast]
        ring
      · have hz : ((nk k).choose i : ℚ) * ((mk k).choose j : ℚ) = 0 := by
          rcases not_and_or.1 hij with h | h
          · rw [Nat.choose_eq_zero_of_lt (not_le.1 h)]; simp
          · rw [Nat.choose_eq_zero_of_lt (not_le.1 h)]; simp
        have hz' : ((nk k).choose i : B) * ((mk k).choose j : B) = 0 := by
          have := congrArg (algebraMap ℚ B) hz
          simpa using this
        rw [hz, zero_smul]
        calc ((nk k).choose i : B) * c i * (b ^ 2) ^ (nk k - i) *
              (((mk k).choose j : B) * c' j * (b ^ 3) ^ (mk k - j))
            = (((nk k).choose i : B) * ((mk k).choose j : B)) *
                (c i * (b ^ 2) ^ (nk k - i) * c' j * (b ^ 3) ^ (mk k - j)) := by ring
          _ = 0 := by rw [hz', zero_mul]
    have hmemA : ∑ k ∈ range (D + 1), L k •
        ((∑ i ∈ range (nk k + 1), ((nk k).choose i : B) * c i * (b ^ 2) ^ (nk k - i)) *
          (∑ j ∈ range (mk k + 1), ((mk k).choose j : B) * c' j * (b ^ 3) ^ (mk k - j))) ∈ A :=
      Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (hc _) (hc' _)) _
    suffices hmain : ∑ k ∈ range (D + 1), L k •
        ((∑ i ∈ range (nk k + 1), ((nk k).choose i : B) * c i * (b ^ 2) ^ (nk k - i)) *
          (∑ j ∈ range (mk k + 1), ((mk k).choose j : B) * c' j * (b ^ 3) ^ (mk k - j))) =
        b ^ r + ∑ i ∈ (range (p + 1)).erase 0,
          ((choosePoly i).comp (C (1 / 2 : ℚ) * X)).eval (r : ℚ) • (c i * b ^ (r - 2 * i)) by
      rw [← hmain]; exact hmemA
    rw [Finset.sum_congr rfl fun k hk => by rw [hprod k hk]]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    -- interchange and interpolate
    have hinner : ∀ i ∈ range (p + 1), ∑ k ∈ range (D + 1), ∑ j ∈ range (q + 1),
        (L k * (((nk k).choose i : ℚ) * ((mk k).choose j : ℚ))) •
          (c i * c' j * b ^ (r - 2 * i - 3 * j)) =
        (choosePoly i).eval x • (c i * b ^ (r - 2 * i)) := by
      intro i hi
      have hi' : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      rw [Finset.sum_eq_single 0]
      · have hint := eval_eq_sum_lagrange hv x (hg_deg i hi' 0 (Nat.zero_le _))
        rw [hg_x, Finset.sum_congr rfl fun k hk => by rw [hg_node k hk]] at hint
        simp only [↓reduceIte, mul_one] at hint
        rw [← hint, hc0', mul_one, Nat.mul_zero, Nat.sub_zero]
      · intro j hj hj0
        have hj' : j ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hint := eval_eq_sum_lagrange hv x (hg_deg i hi' j hj')
        rw [hg_x, Finset.sum_congr rfl fun k hk => by rw [hg_node k hk]] at hint
        simp only [if_neg hj0, mul_zero] at hint
        rw [← hint, zero_smul]
      · intro h; simp at h
    rw [Finset.sum_congr rfl hinner, ← Finset.add_sum_erase _ _ (by simp : 0 ∈ range (p + 1))]
    simp only [choosePoly_zero, eval_one, one_smul, hc0, one_mul, Nat.mul_zero, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [eval_comp, hx]

end AddPow

open AddPow

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ### Additively power subintegral elements -/

/-- `b ∈ B` is *additively power subintegral* over the `ℚ`-subalgebra `A` (Roberts–Singh, p. 258:
"subintegral over `A`"): there are `N, d` and `c₁, …, c_d ∈ B` (here `c i = c_{i+1}`) with
`bᵐ + ∑_{i=1}^d binom(m, i) cᵢ b^{m-i} ∈ A` for all `m ≥ N`. -/
def IsAddPowSubintegral (A : Subalgebra ℚ B) (b : B) : Prop :=
  ∃ (N d : ℕ) (c : Fin d → B), ∀ m, N ≤ m →
    b ^ m + ∑ i : Fin d, (m.choose (i + 1) : B) * c i * b ^ (m - (i + 1)) ∈ A

namespace AddPow

/-- The cut-off trick turns Roberts–Singh's eventual relations into an exact system. -/
lemma hasExactSystem_of_isAddPowSubintegral {A : Subalgebra ℚ B} {b : B}
    (h : IsAddPowSubintegral A b) : HasExactSystem A b := by
  classical
  obtain ⟨N, d, c, hc⟩ := h
  refine hasExactSystem_of_eventually Finset.univ (fun i : Fin d => choosePoly (i + 1)) c
    (fun i => i + 1) (max N d) (fun i _ => by simp [choosePoly_eval_zero])
    (fun i _ => by have := i.isLt; omega) (fun r hr => ?_)
  convert hc r (le_of_max_le_left hr) using 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [choosePoly_eval_natCast]
  simp only [Algebra.smul_def, map_natCast]
  ring

/-- An exact system is in particular an eventual one (take `N = d`). -/
lemma isAddPowSubintegral_of_hasExactSystem {A : Subalgebra ℚ B} {b : B}
    (h : HasExactSystem A b) : IsAddPowSubintegral A b := by
  obtain ⟨c, hc0, ⟨d, hd⟩, hc⟩ := h
  refine ⟨d, d, fun i => c (i + 1), fun m hm => ?_⟩
  have := hc m
  rw [Finset.sum_range_succ'] at this
  convert this using 1
  rw [add_comm]
  congr 1
  · rw [Fin.sum_univ_eq_sum_range (fun i => (m.choose (i + 1) : B) * c (i + 1) * b ^ (m - (i + 1)))]
    apply Finset.sum_subset (range_subset_range.2 hm)
    intro k _ hk
    rw [mem_range, not_lt] at hk
    rw [hd (k + 1) (by omega)]
    simp
  · simp [hc0]

/-- Roberts–Singh's elementwise notion is equivalent to the existence of an exact system. -/
lemma isAddPowSubintegral_iff_hasExactSystem {A : Subalgebra ℚ B} {b : B} :
    IsAddPowSubintegral A b ↔ HasExactSystem A b :=
  ⟨hasExactSystem_of_isAddPowSubintegral, isAddPowSubintegral_of_hasExactSystem⟩

end AddPow

/-- The elements of `B` that are additively power subintegral over `A` form a `ℚ`-subalgebra
containing `A` (Roberts–Singh (4.8)). -/
def addPowSubintegralClosure (A : Subalgebra ℚ B) : Subalgebra ℚ B where
  carrier := {b | IsAddPowSubintegral A b}
  mul_mem' hb hb' := isAddPowSubintegral_of_hasExactSystem
    ((hasExactSystem_of_isAddPowSubintegral hb).mul (hasExactSystem_of_isAddPowSubintegral hb'))
  add_mem' hb hb' := isAddPowSubintegral_of_hasExactSystem
    ((hasExactSystem_of_isAddPowSubintegral hb).add (hasExactSystem_of_isAddPowSubintegral hb'))
  algebraMap_mem' q := isAddPowSubintegral_of_hasExactSystem
    (HasExactSystem.of_mem (Subalgebra.algebraMap_mem A q))

@[simp]
lemma mem_addPowSubintegralClosure {A : Subalgebra ℚ B} {b : B} :
    b ∈ addPowSubintegralClosure A ↔ IsAddPowSubintegral A b := Iff.rfl

/-- Elements of `A` are additively power subintegral over `A`. -/
lemma IsAddPowSubintegral.of_mem {A : Subalgebra ℚ B} {b : B} (hb : b ∈ A) :
    IsAddPowSubintegral A b :=
  isAddPowSubintegral_of_hasExactSystem (HasExactSystem.of_mem hb)

/-- `A ⊆ addPowSubintegralClosure A`. -/
lemma le_addPowSubintegralClosure (A : Subalgebra ℚ B) : A ≤ addPowSubintegralClosure A :=
  fun _ hb => IsAddPowSubintegral.of_mem hb

/-- Sums of additively power subintegral elements (Roberts–Singh (4.5)). -/
lemma IsAddPowSubintegral.add {A : Subalgebra ℚ B} {b b' : B} (hb : IsAddPowSubintegral A b)
    (hb' : IsAddPowSubintegral A b') : IsAddPowSubintegral A (b + b') :=
  (addPowSubintegralClosure A).add_mem hb hb'

/-- Products of additively power subintegral elements (Roberts–Singh (4.8)). -/
lemma IsAddPowSubintegral.mul {A : Subalgebra ℚ B} {b b' : B} (hb : IsAddPowSubintegral A b)
    (hb' : IsAddPowSubintegral A b') : IsAddPowSubintegral A (b * b') :=
  (addPowSubintegralClosure A).mul_mem hb hb'

/-- Roberts–Singh (4.13): if `b²` and `b³` are additively power subintegral over `A`, so is `b`. -/
theorem IsAddPowSubintegral.of_sq_of_cube {A : Subalgebra ℚ B} {b : B}
    (h2 : IsAddPowSubintegral A (b ^ 2)) (h3 : IsAddPowSubintegral A (b ^ 3)) :
    IsAddPowSubintegral A b :=
  isAddPowSubintegral_of_hasExactSystem (HasExactSystem.of_sq_of_cube
    (hasExactSystem_of_isAddPowSubintegral h2) (hasExactSystem_of_isAddPowSubintegral h3))

/-- FHX's normalization `N ≥ d` (Lemma 8.2: "integers `N ≥ d ≥ 0`"), after enlarging `N`. -/
theorem IsAddPowSubintegral.exists_le {A : Subalgebra ℚ B} {b : B} (h : IsAddPowSubintegral A b) :
    ∃ (N d : ℕ) (c : Fin d → B), d ≤ N ∧ ∀ m, N ≤ m →
      b ^ m + ∑ i : Fin d, (m.choose (i + 1) : B) * c i * b ^ (m - (i + 1)) ∈ A := by
  obtain ⟨N, d, c, hc⟩ := h
  exact ⟨max N d, d, c, le_max_right _ _, fun m hm => hc m (le_of_max_le_left hm)⟩

/-! ### The elementary step (`rmk:gl-additive-powers`) -/

/-- `A[e] = A + Ae` when `e² ∈ A`. -/
theorem mem_adjoin_insert_iff_add_mul {A : Subalgebra ℚ B} {e : B} (he2 : e ^ 2 ∈ A) {b : B} :
    b ∈ Algebra.adjoin ℚ (insert e (A : Set B)) ↔ ∃ α ∈ A, ∃ β ∈ A, b = α + β * e := by
  constructor
  · intro hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨0, A.zero_mem, 1, A.one_mem, by ring⟩
      · exact ⟨x, hx, 0, A.zero_mem, by ring⟩
    | algebraMap q => exact ⟨algebraMap ℚ B q, A.algebraMap_mem q, 0, A.zero_mem, by ring⟩
    | add x y _ _ hx hy =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hx
      obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hy
      exact ⟨α + γ, A.add_mem hα hγ, β + δ, A.add_mem hβ hδ, by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hx
      obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hy
      refine ⟨α * γ + β * δ * e ^ 2, A.add_mem (A.mul_mem hα hγ)
        (A.mul_mem (A.mul_mem hβ hδ) he2), α * δ + β * γ,
        A.add_mem (A.mul_mem hα hδ) (A.mul_mem hβ hγ), by ring⟩
  · rintro ⟨α, hα, β, hβ, rfl⟩
    have hsub : (A : Set B) ⊆ Algebra.adjoin ℚ (insert e (A : Set B)) :=
      (Set.subset_insert _ _).trans Algebra.subset_adjoin
    exact Subalgebra.add_mem _ (hsub hα) (Subalgebra.mul_mem _ (hsub hβ)
      (Algebra.subset_adjoin (Set.mem_insert _ _)))

/-- `u², u³ ∈ A` implies `uʲ ∈ A` for all `j ≥ 2`. -/
lemma AddPow.pow_mem_of_two_le_of_sq_of_cube {A : Subalgebra ℚ B} {u : B} (hu2 : u ^ 2 ∈ A) (hu3 : u ^ 3 ∈ A) :
    ∀ j, 2 ≤ j → u ^ j ∈ A := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases (show j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | h4
    · exact hu2
    · exact hu3
    · have : u ^ j = u ^ 2 * u ^ (j - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact A.mul_mem hu2 (ih (j - 2) (by omega) (by omega))

/-- The explicit system of an elementary step: if `α ∈ A` and `u², u³ ∈ A`, then
`(α + u)ᵐ - m u (α + u)^{m-1} ∈ A` for `m ≥ 1` (`d = 1`, `c₁ = -u`). -/
theorem addPow_mem_of_sq_of_cube {A : Subalgebra ℚ B} {α u : B} (hα : α ∈ A) (hu2 : u ^ 2 ∈ A)
    (hu3 : u ^ 3 ∈ A) {m : ℕ} (hm : 1 ≤ m) :
    (α + u) ^ m + (m.choose 1 : B) * (-u) * (α + u) ^ (m - 1) ∈ A := by
  have hpow := AddPow.pow_mem_of_two_le_of_sq_of_cube hu2 hu3
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.choose_one_right]
  -- `(α + u)^{m+1} = α^{m+1} + (m+1) α^m u + X`, `u (α + u)^m = α^m u + Y`, `X, Y ∈ A`
  have hX : (α + u) ^ (m + 1) - (α ^ (m + 1) + ((m + 1 : ℕ) : B) * α ^ m * u) ∈ A := by
    rw [add_comm α u, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    have : ∑ k ∈ range m, u ^ (k + 1 + 1) * α ^ (m + 1 - (k + 1 + 1)) *
        ((m + 1).choose (k + 1 + 1) : B) ∈ A :=
      Subalgebra.sum_mem _ fun k _ => A.mul_mem (A.mul_mem (hpow _ (by omega))
        (A.pow_mem hα _)) (A.natCast_mem _)
    convert this using 1
    simp only [Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, pow_zero, pow_one,
      zero_add, Nat.sub_zero, Nat.add_sub_cancel]
    push_cast
    ring
  have hY : u * (α + u) ^ m - α ^ m * u ∈ A := by
    rw [add_comm α u, add_pow, Finset.sum_range_succ', mul_add, Finset.mul_sum]
    have : ∑ k ∈ range m, u * (u ^ (k + 1) * α ^ (m - (k + 1)) * (m.choose (k + 1) : B)) ∈ A :=
      Subalgebra.sum_mem _ fun k _ => by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ']
        exact A.mul_mem (A.mul_mem (hpow _ (by omega)) (A.pow_mem hα _)) (A.natCast_mem _)
    convert this using 1
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero]
    ring
  have hfin : (α + u) ^ (m + 1) + ((m + 1 : ℕ) : B) * -u * (α + u) ^ m =
      α ^ (m + 1) + ((α + u) ^ (m + 1) - (α ^ (m + 1) + ((m + 1 : ℕ) : B) * α ^ m * u)) -
        ((m + 1 : ℕ) : B) * (u * (α + u) ^ m - α ^ m * u) := by ring
  rw [hfin]
  exact A.sub_mem (A.add_mem (A.pow_mem hα _) hX) (A.mul_mem (A.natCast_mem _) hY)

/-- **Elementary step** (`rmk:gl-additive-powers`): if `e², e³ ∈ A`, every `b = α + βe ∈ A[e]` is
additively power subintegral over `A`, with `N = d = 1` and `c₁ = -βe`. -/
theorem isAddPowSubintegral_of_mem_adjoin_insert {A : Subalgebra ℚ B} {e : B} (he2 : e ^ 2 ∈ A)
    (he3 : e ^ 3 ∈ A) {b : B} (hb : b ∈ Algebra.adjoin ℚ (insert e (A : Set B))) :
    ∃ α ∈ A, ∃ β ∈ A, b = α + β * e ∧ ∀ m, 1 ≤ m →
      b ^ m + (m.choose 1 : B) * (-(β * e)) * b ^ (m - 1) ∈ A := by
  obtain ⟨α, hα, β, hβ, rfl⟩ := (mem_adjoin_insert_iff_add_mul he2).1 hb
  refine ⟨α, hα, β, hβ, rfl, fun m hm => addPow_mem_of_sq_of_cube hα ?_ ?_ hm⟩
  · rw [mul_pow]; exact A.mul_mem (A.pow_mem hβ _) he2
  · rw [mul_pow]; exact A.mul_mem (A.pow_mem hβ _) he3

/-- Elementary step, as a predicate: `e², e³ ∈ A` implies every element of `A[e]` is additively
power subintegral over `A`. -/
theorem IsAddPowSubintegral.of_mem_adjoin_insert {A : Subalgebra ℚ B} {e : B} (he2 : e ^ 2 ∈ A)
    (he3 : e ^ 3 ∈ A) {b : B} (hb : b ∈ Algebra.adjoin ℚ (insert e (A : Set B))) :
    IsAddPowSubintegral A b := by
  obtain ⟨α, -, β, -, -, h⟩ := isAddPowSubintegral_of_mem_adjoin_insert he2 he3 hb
  refine ⟨1, 1, fun _ => -(β * e), fun m hm => ?_⟩
  simpa using h m hm

/-! ### Towers (`thm:gl-additive-powers`, Roberts–Singh (4.17) (ii)⇒(i)) -/

/-- **Additive powers along a tower.** Let `A 0 ⊆ A 1 ⊆ ⋯` be explicit chain data with
`A (i+1) ⊆ (A i)[e i]` and `(e i)², (e i)³ ∈ A i`. Then every element of every `A n` is additively
power subintegral over `A 0`. (Monotonicity of `A` is not needed.) -/
theorem isAddPowSubintegral_of_tower (A : ℕ → Subalgebra ℚ B) (e : ℕ → B)
    (he2 : ∀ i, e i ^ 2 ∈ A i) (he3 : ∀ i, e i ^ 3 ∈ A i)
    (hstep : ∀ i, A (i + 1) ≤ Algebra.adjoin ℚ (insert (e i) (A i : Set B))) (n : ℕ) :
    ∀ b ∈ A n, IsAddPowSubintegral (A 0) b := by
  suffices h : A n ≤ addPowSubintegralClosure (A 0) from fun b hb => h hb
  induction n with
  | zero => exact le_addPowSubintegralClosure _
  | succ n ih =>
    refine (hstep n).trans (Algebra.adjoin_le (Set.insert_subset ?_ ih))
    exact IsAddPowSubintegral.of_sq_of_cube (ih (he2 n)) (ih (he3 n))

/-- **Additive powers, Stacks `0CND`(2) form.** If `b ∈ A[e₀, …, e_{n-1}]` with
`e_i², e_i³ ∈ A[e₀, …, e_{i-1}]`, then `b` is additively power subintegral over `A`. -/
theorem isAddPowSubintegral_of_mem_adjoin (A : Subalgebra ℚ B) (e : ℕ → B) (n : ℕ)
    (he2 : ∀ i < n, e i ^ 2 ∈ Algebra.adjoin ℚ ((A : Set B) ∪ e '' Set.Iio i))
    (he3 : ∀ i < n, e i ^ 3 ∈ Algebra.adjoin ℚ ((A : Set B) ∪ e '' Set.Iio i)) {b : B}
    (hb : b ∈ Algebra.adjoin ℚ ((A : Set B) ∪ e '' Set.Iio n)) : IsAddPowSubintegral A b := by
  suffices h : ∀ i ≤ n,
      Algebra.adjoin ℚ ((A : Set B) ∪ e '' Set.Iio i) ≤ addPowSubintegralClosure A from
    h n le_rfl hb
  intro i hi
  induction i with
  | zero =>
    have h0 : Set.Iio (0 : ℕ) = ∅ := by ext; simp
    rw [h0, Set.image_empty, Set.union_empty]
    exact Algebra.adjoin_le (le_addPowSubintegralClosure A)
  | succ i ih =>
    have ih := ih (by omega)
    refine Algebra.adjoin_le (Set.union_subset (le_addPowSubintegralClosure A) ?_)
    rintro _ ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih (Algebra.subset_adjoin (Set.mem_union_right _ ⟨j, hj, rfl⟩))
    · exact IsAddPowSubintegral.of_sq_of_cube (ih (he2 j (by omega))) (ih (he3 j (by omega)))

/-- **Additive powers for a directed union of towers** (`thm:gl-additive-powers`): if every
element of `B` lies in the top of a finite elementary tower over `A`, every element of `B` is
additively power subintegral over `A`. -/
theorem isAddPowSubintegral_of_forall_exists_tower (A : Subalgebra ℚ B)
    (h : ∀ b : B, ∃ (A' : ℕ → Subalgebra ℚ B) (e : ℕ → B) (n : ℕ), A' 0 = A ∧
      (∀ i, e i ^ 2 ∈ A' i) ∧ (∀ i, e i ^ 3 ∈ A' i) ∧
      (∀ i, A' (i + 1) ≤ Algebra.adjoin ℚ (insert (e i) (A' i : Set B))) ∧ b ∈ A' n)
    (b : B) : IsAddPowSubintegral A b := by
  obtain ⟨A', e, n, h0, h2, h3, hstep, hb⟩ := h b
  subst h0
  exact isAddPowSubintegral_of_tower A' e h2 h3 hstep n b hb

/-! ### Lagrange interpolation (`lem:gl-lagrange`, FHX Lemma 8.2, second part) -/

/-- **`lem:gl-lagrange`, first claim.** With `a m = bᵐ + ∑_{i=1}^d binom(m,i) cᵢ b^{m-i}`,
`b^{n+2d} ∈ (a_{n+d}, …, a_{n+2d})` for every `n` (FHX state it for `n ≥ N - d`). -/
theorem pow_mem_span_addPow (b : B) (d : ℕ) (c : Fin d → B) (n : ℕ) :
    b ^ (n + 2 * d) ∈ Ideal.span ((fun m : ℕ => b ^ m + ∑ i : Fin d,
      (m.choose (i + 1) : B) * c i * b ^ (m - (i + 1))) '' Set.Icc (n + d) (n + 2 * d)) := by
  set a : ℕ → B := fun m => b ^ m + ∑ i : Fin d, (m.choose (i + 1) : B) * c i * b ^ (m - (i + 1))
    with ha
  set v : ℕ → ℚ := fun r => ((n + d + r : ℕ) : ℚ) with hv
  have hinj : Set.InjOn v (range (d + 1)) := by
    intro k _ l _ hkl
    simp only [hv, Nat.cast_inj] at hkl
    omega
  set L : ℕ → ℚ := fun r => (Lagrange.basis (range (d + 1)) v r).eval 0 with hL
  -- `b^{d-r} a_{n+d+r} = b^{n+2d} + ∑ binom(n+d+r, i+1) cᵢ b^{n+2d-(i+1)}`
  have hshift : ∀ r ∈ range (d + 1), b ^ (d - r) * a (n + d + r) = b ^ (n + 2 * d) +
      ∑ i : Fin d, ((n + d + r).choose (i + 1) : B) * c i * b ^ (n + 2 * d - (i + 1)) := by
    intro r hr
    have hr' : r ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    simp only [ha, mul_add, Finset.mul_sum]
    congr 1
    · rw [← pow_add]; congr 1; omega
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      have : b ^ (n + 2 * d - (i + 1)) = b ^ (d - r) * b ^ (n + d + r - (i + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
  have hsum : ∑ r ∈ range (d + 1), L r • (b ^ (d - r) * a (n + d + r)) = b ^ (n + 2 * d) := by
    rw [Finset.sum_congr rfl fun r hr => by rw [hshift r hr]]
    simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have h1 : ∑ r ∈ range (d + 1), L r = 1 := by
      have := eval_eq_sum_lagrange hinj 0 (g := 1) (by simp)
      simpa using this.symm
    have h2 : ∀ i : Fin d, ∑ r ∈ range (d + 1), L r • (((n + d + r).choose (i + 1) : B) * c i *
        b ^ (n + 2 * d - (i + 1))) = 0 := by
      intro i
      have hi := i.isLt
      have := eval_eq_sum_lagrange hinj 0 (natDegree_choosePoly_le (i + 1) |>.trans
        (show (i : ℕ) + 1 ≤ d by omega))
      rw [choosePoly_eval_zero, if_neg (by omega)] at this
      simp only [hv, choosePoly_eval_natCast] at this
      have h' : ∑ r ∈ range (d + 1), L r • (((n + d + r).choose (i + 1) : B) * c i *
          b ^ (n + 2 * d - (i + 1))) = (∑ r ∈ range (d + 1), L r *
            ((n + d + r).choose (i + 1) : ℚ)) • (c i * b ^ (n + 2 * d - (i + 1))) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [Algebra.smul_def, map_mul, map_natCast]
        ring
      rw [h', ← this, zero_smul]
    rw [Finset.sum_eq_zero fun i _ => h2 i, add_zero, ← Finset.sum_smul, h1, one_smul]
  rw [← hsum]
  refine Ideal.sum_mem _ fun r hr => ?_
  have hr' : r ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [← smul_mul_assoc]
  refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n + d + r, ⟨by omega, by omega⟩, rfl⟩)

omit [Algebra ℚ B] in
/-- **`lem:gl-lagrange`, second claim.** `aₘ ∈ (b^{m-d})` for `m ≥ d`. -/
theorem addPow_mem_span_pow (b : B) (d : ℕ) (c : Fin d → B) {m : ℕ} (hm : d ≤ m) :
    b ^ m + ∑ i : Fin d, (m.choose (i + 1) : B) * c i * b ^ (m - (i + 1)) ∈
      Ideal.span {b ^ (m - d)} := by
  rw [Ideal.mem_span_singleton']
  refine ⟨b ^ d + ∑ i : Fin d, (m.choose (i + 1) : B) * c i * b ^ (d - (i + 1)), ?_⟩
  rw [add_mul, Finset.sum_mul, ← pow_add, Nat.add_sub_cancel' hm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have : b ^ (m - (i + 1)) = b ^ (d - (i + 1)) * b ^ (m - d) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; ring

end EnvelopeProperty
