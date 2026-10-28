/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.TestIdeal.Grading

/-!
# Test ideals in polynomial rings over perfect fields

Let `K` be a perfect field of characteristic `p`, `R = K[x_i : i ∈ σ]` with `σ` finite. Following
Blickle–Mustaţă–Smith (*Discreteness and rationality of F-thresholds*, §2), the test ideal of
`I ⊆ R` with exponent `c ∈ ℚ` is the union of the ascending chain
`e ↦ (I^⌈c p^e⌉)^[1/p^e]` (`testChain`, `testChain_mono`), which stabilizes since `R` is
Noetherian (`exists_testIdeal_eq`). Since `I^[1/q] = Φ_e(I)` (by definition of `frobRoot`), for
`e ≫ 0` the test ideal is the stable Frobenius-trace image `Φ_e(I^⌈c p^e⌉)`
(`exists_coe_testIdeal_eq_image`), which is the description used in FHX Section 3
(eq. `eq:test-def`).

Main results:
* `testIdeal_mono`, `testIdeal_anti`: monotone in `I`, antitone in `c`;
* `le_testIdeal_one`: `I ≤ τ(I^1)`; `testIdeal_of_nonpos`: `τ(I^c) = R` for `c ≤ 0`;
* `isHomogeneous_testIdeal`: test ideals of weighted homogeneous ideals are homogeneous, and
  `HasWeightedGeneratorsLE.testIdeal`: if `I` is generated in `w`-degree `≤ D` then `τ(I^c)` is
  generated in `w`-degree `≤ ⌊c D⌋`;
* `testIdeal_pow`: `τ((I^r)^c) = τ(I^{r c})` for `I ≠ 0`, `c ≥ 0`;
* subadditivity `testIdeal_add_le : τ(I^{c+d}) ≤ τ(I^c) τ(I^d)` and
  `testIdeal_nsmul_le : τ(I^{l c}) ≤ τ(I^c)^l` (for `I ≠ 0`, `c, d ≥ 0`).

The last two use the "test element" estimate `frobRoot_le_frobRoot_pow_add`: for `0 ≠ g ∈ I` and
`p^k > deg g^r`, `(I^N)^[1/p^e] = (g^r (I^N)^[p^k])^[1/p^(k+e)] ≤ (I^(N p^k + r))^[1/p^(k+e)]`,
which rests on `frobRoot_span_singleton_eq_top`.
-/

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {σ K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]
variable [Finite σ]

/-- The `e`-th term `(I^⌈c p^e⌉)^[1/p^e]` of the Blickle–Mustaţă–Smith chain. -/
def testChain (I : Ideal (MvPolynomial σ K)) (c : ℚ) (e : ℕ) : Ideal (MvPolynomial σ K) :=
  frobRoot p e (I ^ ⌈c * (p : ℚ) ^ e⌉₊)

/-- The test ideal `τ(I^c) = ⋃_e (I^⌈c p^e⌉)^[1/p^e]` (Blickle–Mustaţă–Smith). For `e ≫ 0` it
equals `testChain p I c e` (`exists_testIdeal_eq`). -/
def testIdeal (I : Ideal (MvPolynomial σ K)) (c : ℚ) : Ideal (MvPolynomial σ K) :=
  ⨆ e, testChain p I c e

omit hp [Finite σ] in
theorem testChain_ceil_succ_le (c : ℚ) (e : ℕ) :
    ⌈c * (p : ℚ) ^ (e + 1)⌉₊ ≤ ⌈c * (p : ℚ) ^ e⌉₊ * p := by
  rw [Nat.ceil_le]
  push_cast
  rw [pow_succ, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg p)

theorem testChain_le_succ (I : Ideal (MvPolynomial σ K)) (c : ℚ) (e : ℕ) :
    testChain p I c e ≤ testChain p I c (e + 1) := by
  have h1 : frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊) ≤ I ^ ⌈c * (p : ℚ) ^ (e + 1)⌉₊ := by
    refine (frobPow_le_pow _ _).trans ?_
    rw [← pow_mul, pow_one]
    exact Ideal.pow_le_pow_right (testChain_ceil_succ_le p c e)
  calc testChain p I c e
      = frobRoot p e (frobRoot p 1 (frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊))) := by
        rw [frobRoot_frobPow]; rfl
    _ = frobRoot p (1 + e) (frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊)) := frobRoot_frobRoot ..
    _ ≤ testChain p I c (e + 1) := by
        rw [add_comm]
        exact frobRoot_mono p _ h1

/-- The Blickle–Mustaţă–Smith chain is ascending. -/
theorem testChain_mono (I : Ideal (MvPolynomial σ K)) (c : ℚ) : Monotone (testChain p I c) :=
  monotone_nat_of_le_succ (testChain_le_succ p I c)

theorem testChain_le_testIdeal (I : Ideal (MvPolynomial σ K)) (c : ℚ) (e : ℕ) :
    testChain p I c e ≤ testIdeal p I c :=
  le_iSup (testChain p I c) e

/-- The chain stabilizes: `τ(I^c) = (I^⌈c p^e⌉)^[1/p^e]` for all `e ≫ 0`. -/
theorem exists_testIdeal_eq (I : Ideal (MvPolynomial σ K)) (c : ℚ) :
    ∃ e₀, ∀ e, e₀ ≤ e → testIdeal p I c = testChain p I c e := by
  obtain ⟨e₀, he₀⟩ := monotone_stabilizes_iff_noetherian.2
    (inferInstance : IsNoetherianRing (MvPolynomial σ K)) ⟨testChain p I c, testChain_mono p I c⟩
  refine ⟨e₀, fun e he => le_antisymm (iSup_le fun e' => ?_) (testChain_le_testIdeal p I c e)⟩
  have h1 : testChain p I c e = testChain p I c (max e' e) :=
    (he₀ e he).symm.trans (he₀ _ (he.trans (le_max_right _ _)))
  rw [h1]
  exact testChain_mono p I c (le_max_left _ _)

/-- For `e ≫ 0`, `τ(I^c)` is the Frobenius-trace image `Φ_e(I^⌈c p^e⌉)` (FHX eq. `eq:test-def`). -/
theorem exists_coe_testIdeal_eq_image (I : Ideal (MvPolynomial σ K)) (c : ℚ) :
    ∃ e₀, ∀ e, e₀ ≤ e → (testIdeal p I c : Set (MvPolynomial σ K)) =
      frobTrace p e '' (I ^ ⌈c * (p : ℚ) ^ e⌉₊ : Ideal (MvPolynomial σ K)) := by
  obtain ⟨e₀, he₀⟩ := exists_testIdeal_eq p I c
  exact ⟨e₀, fun e he => by rw [he₀ e he]; rfl⟩

/-- `τ(I^c)` is monotone in `I`. -/
theorem testIdeal_mono {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (c : ℚ) :
    testIdeal p I c ≤ testIdeal p J c :=
  iSup_mono fun _ => frobRoot_mono p _ (Ideal.pow_right_mono h _)

/-- `τ(I^c)` is antitone in `c`. -/
theorem testIdeal_anti (I : Ideal (MvPolynomial σ K)) {c c' : ℚ} (h : c ≤ c') :
    testIdeal p I c' ≤ testIdeal p I c :=
  iSup_mono fun _ => frobRoot_mono p _ (Ideal.pow_le_pow_right
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right h (by positivity))))

theorem le_testIdeal_of_le_one (I : Ideal (MvPolynomial σ K)) {c : ℚ} (hc : c ≤ 1) :
    I ≤ testIdeal p I c := by
  refine le_trans ?_ (testChain_le_testIdeal p I c 0)
  rw [testChain, frobRoot_zero, pow_zero, mul_one]
  refine le_trans (pow_one I).ge (Ideal.pow_le_pow_right ?_)
  rw [Nat.ceil_le]
  exact_mod_cast hc

/-- `I ≤ τ(I^1)`. -/
theorem le_testIdeal_one (I : Ideal (MvPolynomial σ K)) : I ≤ testIdeal p I 1 :=
  le_testIdeal_of_le_one p I le_rfl

theorem testIdeal_of_nonpos (I : Ideal (MvPolynomial σ K)) {c : ℚ} (hc : c ≤ 0) :
    testIdeal p I c = ⊤ := by
  refine top_le_iff.1 (le_trans ?_ (testChain_le_testIdeal p I c 0))
  rw [testChain, frobRoot_zero, pow_zero, mul_one, Nat.ceil_eq_zero.2 hc, pow_zero,
    Ideal.one_eq_top]

@[simp]
theorem testIdeal_zero (I : Ideal (MvPolynomial σ K)) : testIdeal p I 0 = ⊤ :=
  testIdeal_of_nonpos p I le_rfl

/-! ### Homogeneity and degree bounds -/

omit [Finite σ] in
theorem weighted_isHomogeneous_pow {w : σ → ℕ} {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w)) :
    ∀ n : ℕ, (I ^ n).IsHomogeneous (weightedHomogeneousSubmodule K w)
  | 0 => by rw [pow_zero, Ideal.one_eq_top]; exact Ideal.IsHomogeneous.top _
  | n + 1 => by rw [pow_succ]; exact (weighted_isHomogeneous_pow hI n).mul hI

/-- Test ideals of `w`-homogeneous ideals are `w`-homogeneous. -/
theorem isHomogeneous_testIdeal {w : σ → ℕ} {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w)) (c : ℚ) :
    (testIdeal p I c).IsHomogeneous (weightedHomogeneousSubmodule K w) :=
  Ideal.IsHomogeneous.iSup fun e =>
    isHomogeneous_frobRoot p (weighted_isHomogeneous_pow hI _) e

/-- If `I` is generated by `w`-homogeneous polynomials of degree `≤ D` and `c ≥ 0`, then `τ(I^c)`
is generated by `w`-homogeneous polynomials of degree `≤ ⌊c D⌋`. -/
theorem HasWeightedGeneratorsLE.testIdeal {w : σ → ℕ} {D : ℕ} {I : Ideal (MvPolynomial σ K)}
    (hI : HasWeightedGeneratorsLE w D I) {c : ℚ} (hc : 0 ≤ c) :
    HasWeightedGeneratorsLE w ⌊c * D⌋₊ (testIdeal p I c) := by
  obtain ⟨e₀, he₀⟩ := exists_testIdeal_eq p I c
  set m := ⌊c * D⌋₊
  have hδ : 0 < (m : ℚ) + 1 - c * D := by
    have := Nat.lt_floor_add_one (c * D)
    linarith
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((D : ℚ) / ((m : ℚ) + 1 - c * D)) hp1
  set e := max e₀ n
  have hpe : (p : ℚ) ^ n ≤ (p : ℚ) ^ e := pow_le_pow_right₀ hp1.le (le_max_right _ _)
  have hDlt : (D : ℚ) < ((m : ℚ) + 1 - c * D) * (p : ℚ) ^ e := by
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  rw [he₀ e (le_max_left _ _), testChain]
  refine ((hI.pow _).frobRoot p e).mono ?_
  have hq : 0 < p ^ e := Nat.pos_of_ne_zero (frobExp_ne_zero p e)
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hq]
  have hN : (⌈c * (p : ℚ) ^ e⌉₊ : ℚ) < c * (p : ℚ) ^ e + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : ((⌈c * (p : ℚ) ^ e⌉₊ * D : ℕ) : ℚ) ≤ (c * (p : ℚ) ^ e + 1) * D := by
    push_cast
    exact mul_le_mul_of_nonneg_right hN.le (Nat.cast_nonneg D)
  have h2 : ((⌈c * (p : ℚ) ^ e⌉₊ * D : ℕ) : ℚ) < ((m.succ * p ^ e : ℕ) : ℚ) := by
    refine lt_of_le_of_lt h1 ?_
    push_cast
    nlinarith
  exact_mod_cast h2

/-! ### Comparison of exponents and subadditivity -/

/-- The test element estimate: for `I ≠ 0` and `r : ℕ` there is `k₀` such that for `k ≥ k₀`,
`(I^N)^[1/p^e] ≤ (I^(N p^k + r))^[1/p^(k + e)]` for all `e, N`. -/
theorem frobRoot_le_frobRoot_pow_add {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊥) (r : ℕ) :
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ e N, frobRoot p e (I ^ N) ≤ frobRoot p (k + e) (I ^ (N * p ^ k + r)) := by
  obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨(g ^ r).totalDegree, fun k hk e N => ?_⟩
  have hdeg : (g ^ r).totalDegree < p ^ k :=
    lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) (Nat.pow_le_pow_right hp.out.pos hk)
  have htop := frobRoot_span_singleton_eq_top p (pow_ne_zero r hg0) hdeg
  calc frobRoot p e (I ^ N)
      = frobRoot p e (frobRoot p k (Ideal.span {g ^ r}) * I ^ N) := by rw [htop, Ideal.top_mul]
    _ = frobRoot p e (frobRoot p k (Ideal.span {g ^ r} * frobPow (p ^ k) (I ^ N))) := by
        rw [frobRoot_mul_frobPow]
    _ = frobRoot p (k + e) (Ideal.span {g ^ r} * frobPow (p ^ k) (I ^ N)) := frobRoot_frobRoot ..
    _ ≤ frobRoot p (k + e) (I ^ (N * p ^ k + r)) := by
        refine frobRoot_mono p _ ?_
        rw [pow_add, pow_mul, mul_comm]
        refine Ideal.mul_mono ?_ ?_
        · exact frobPow_le_pow _ _
        · rw [Ideal.span_singleton_le_iff_mem]
          exact Ideal.pow_mem_pow hgI r

/-- `τ((I^r)^c) = τ(I^{r c})` for `I ≠ 0` and `c ≥ 0` (BMS). -/
theorem testIdeal_pow {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊥) {c : ℚ} (hc : 0 ≤ c) (r : ℕ) :
    testIdeal p (I ^ r) c = testIdeal p I (r * c) := by
  apply le_antisymm
  · refine iSup_le fun e => le_trans ?_ (testChain_le_testIdeal p I _ e)
    refine frobRoot_mono p _ ?_
    rw [← pow_mul]
    refine Ideal.pow_le_pow_right ?_
    rw [Nat.ceil_le]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg r)
  · obtain ⟨k₀, hk₀⟩ := frobRoot_le_frobRoot_pow_add p hI r
    refine iSup_le fun e => le_trans (hk₀ k₀ le_rfl e _) ?_
    refine le_trans ?_ (testChain_le_testIdeal p (I ^ r) c (k₀ + e))
    refine frobRoot_mono p _ ?_
    rw [← pow_mul]
    refine Ideal.pow_le_pow_right ?_
    have h1 : (⌈c * (p : ℚ) ^ (k₀ + e)⌉₊ : ℚ) < c * (p : ℚ) ^ (k₀ + e) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (r : ℚ) * c * (p : ℚ) ^ e ≤ ⌈(r : ℚ) * c * (p : ℚ) ^ e⌉₊ := Nat.le_ceil _
    have h3 : ((r * ⌈c * (p : ℚ) ^ (k₀ + e)⌉₊ : ℕ) : ℚ) ≤
        ((⌈(r : ℚ) * c * (p : ℚ) ^ e⌉₊ * p ^ k₀ + r : ℕ) : ℚ) := by
      push_cast
      have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
      have hpk : (0 : ℚ) ≤ (p : ℚ) ^ k₀ := by positivity
      calc (r : ℚ) * ⌈c * (p : ℚ) ^ (k₀ + e)⌉₊ ≤ r * (c * (p : ℚ) ^ (k₀ + e) + 1) :=
            mul_le_mul_of_nonneg_left h1.le hr
        _ = r * c * (p : ℚ) ^ e * (p : ℚ) ^ k₀ + r := by rw [pow_add]; ring
        _ ≤ ⌈(r : ℚ) * c * (p : ℚ) ^ e⌉₊ * (p : ℚ) ^ k₀ + r := by
            gcongr
    exact_mod_cast h3

/-- Subadditivity: `τ(I^{c+d}) ≤ τ(I^c) τ(I^d)` for `I ≠ 0` and `c, d ≥ 0`. -/
theorem testIdeal_add_le {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊥) {c d : ℚ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) : testIdeal p I (c + d) ≤ testIdeal p I c * testIdeal p I d := by
  obtain ⟨k₀, hk₀⟩ := frobRoot_le_frobRoot_pow_add p hI 2
  refine iSup_le fun e => le_trans (hk₀ k₀ le_rfl e _) ?_
  set P := (p : ℚ) ^ (k₀ + e)
  have hP : 0 ≤ P := by positivity
  have h1 : (⌈c * P⌉₊ : ℚ) < c * P + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1' : (⌈d * P⌉₊ : ℚ) < d * P + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (c + d) * (p : ℚ) ^ e ≤ ⌈(c + d) * (p : ℚ) ^ e⌉₊ := Nat.le_ceil _
  have h3 : ((⌈c * P⌉₊ + ⌈d * P⌉₊ : ℕ) : ℚ) ≤
      ((⌈(c + d) * (p : ℚ) ^ e⌉₊ * p ^ k₀ + 2 : ℕ) : ℚ) := by
    push_cast
    have hpk : (0 : ℚ) ≤ (p : ℚ) ^ k₀ := by positivity
    have : (c + d) * P = (c + d) * (p : ℚ) ^ e * (p : ℚ) ^ k₀ := by
      simp only [P, pow_add]; ring
    nlinarith
  have h4 : I ^ (⌈(c + d) * (p : ℚ) ^ e⌉₊ * p ^ k₀ + 2) ≤ I ^ ⌈c * P⌉₊ * I ^ ⌈d * P⌉₊ := by
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by exact_mod_cast h3)
  refine le_trans (frobRoot_mono p _ h4) (le_trans (frobRoot_mul_le p _ _ _) ?_)
  exact Ideal.mul_mono (testChain_le_testIdeal p I c (k₀ + e))
    (testChain_le_testIdeal p I d (k₀ + e))

/-- `τ(I^{l c}) ≤ τ(I^c)^l` for `I ≠ 0` and `c ≥ 0`. -/
theorem testIdeal_nsmul_le {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊥) {c : ℚ} (hc : 0 ≤ c) :
    ∀ l : ℕ, testIdeal p I (l * c) ≤ testIdeal p I c ^ l
  | 0 => by rw [pow_zero, Ideal.one_eq_top]; exact le_top
  | l + 1 => by
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact le_trans (testIdeal_add_le p hI (by positivity) hc)
      (Ideal.mul_mono_left (testIdeal_nsmul_le hI hc l))

end EnvelopeProperty
