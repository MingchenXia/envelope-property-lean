/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.TestIdeal.PBasisRoot

/-!
# Test ideals and asymptotic test ideals in rings with a `p`-basis

Let `A` be a commutative ring of prime characteristic `p` with a finite `p`-basis `u`
(`hu : EnvelopeProperty.Cartier.IsPBasis p u`), and let `I^[1/p^e] = hu.frobRoot e I` be the
Frobenius roots of `EnvelopeProperty.TestIdeal.PBasisRoot`. This file ports
`EnvelopeProperty.TestIdeal.Basic` and `EnvelopeProperty.TestIdeal.Asymptotic` from polynomial
rings over perfect fields to such rings, following the blueprint `subsec:sg-pbasis`
(`def:sg-test-ideal`, `lem:sg-test-stable`, `lem:sg-test-subadditive`, `lem:sg-asymptotic`) for
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Theorem 3.1 on a smooth
projective variety (eqs. `eq:test-def`, `eq:smooth-test-inclusions`).

## Test ideals

`hu.testIdeal I c = τ(I^c) = ⨆_e (I^⌈c p^e⌉)^[1/p^e]` (Blickle–Mustaţă–Smith), the union of the
ascending chain `hu.testChain I c` (`testChain_mono`). For Noetherian `A` it stabilizes
(`exists_testIdeal_eq`, `lem:sg-test-stable`). Further: `testIdeal_mono`, `testIdeal_anti`,
`le_testIdeal_one` (`I ≤ τ(I^1)`), `testIdeal_of_nonpos`. In a Noetherian domain, for `I ≠ 0` and
`c, d ≥ 0` (`lem:sg-test-subadditive`):

* `frobRoot_pow_le_frobRoot_pow_add`: if `g ∈ I` and `(g^r)^[1/p^k] = A` then
  `(I^N)^[1/Q] ≤ (I^(N p^k + r))^[1/(p^k Q)]` (the test element estimate; `k` exists by
  `exists_frobRoot_span_singleton_eq_top`);
* `testIdeal_pow`: `τ((I^r)^c) = τ(I^{r c})`;
* `testIdeal_add_le`: `τ(I^{c+d}) ≤ τ(I^c) τ(I^d)`, and `testIdeal_nsmul_le`: `τ(I^{l c}) ≤ τ(I^c)^l`.

## Asymptotic test ideals

For a graded sequence `J` (`J m * J r ≤ J (m + r)`, `J q ≠ 0` for `q > 0`),
`hu.asymptoticTestIdeal J m = B_m = ⨆_{q > 0} τ(J_q^{m/q})` (`lem:sg-asymptotic`):
`testIdeal_le_testIdeal_of_dvd`, `exists_asymptoticTestIdeal_eq` (`B_m = τ(J_q^{m/q})` for all `q`
divisible by some `q₀`), `exists_asymptoticTestIdeal_eq_frobRoot` (and then
`B_m = (J_q^⌈(m/q) p^e⌉)^[1/p^e]` for `e ≫ 0`), `le_asymptoticTestIdeal` (`J_m ≤ B_m`),
`asymptoticTestIdeal_mul_le` (`B_{m l} ≤ B_m^l`).

## Independence of the `p`-basis and base change

All three constructions do not depend on the `p`-basis (`testIdeal_eq_testIdeal`,
`asymptoticTestIdeal_eq_asymptoticTestIdeal`) and commute with base change along any
`φ : A → B` for which `φ ∘ u` is a `p`-basis of `B`, e.g. localizations
(`testIdeal_map`, `asymptoticTestIdeal_map`). This is what is used to compare the local test
ideals of the charts of the cone over a smooth projective variety on their overlaps.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem ceil_mul_pow_succ_le (c : ℚ) (e : ℕ) :
    ⌈c * (p : ℚ) ^ (e + 1)⌉₊ ≤ ⌈c * (p : ℚ) ^ e⌉₊ * p := by
  rw [Nat.ceil_le]
  push_cast
  rw [pow_succ, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg p)

/-- In a graded sequence of ideals, `J_q^k ≤ J_{kq}` for `k > 0`. -/
theorem pow_le_of_mul_le_add {R : Type*} [CommRing R] {J : ℕ → Ideal R}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (q : ℕ) {k : ℕ} (hk : 0 < k) : J q ^ k ≤ J (k * q) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    rw [pow_succ, add_mul, one_mul]
    exact le_trans (Ideal.mul_mono_left ih) (hJ _ _)

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A} (hu : IsPBasis p u)

namespace IsPBasis

/-! ### Test ideals (`def:sg-test-ideal`, `lem:sg-test-stable`) -/

/-- The `e`-th term `(I^⌈c p^e⌉)^[1/p^e]` of the Blickle–Mustaţă–Smith chain. -/
def testChain (I : Ideal A) (c : ℚ) (e : ℕ) : Ideal A :=
  hu.frobRoot e (I ^ ⌈c * (p : ℚ) ^ e⌉₊)

/-- The test ideal `τ(I^c) = ⋃_e (I^⌈c p^e⌉)^[1/p^e]` with respect to the `p`-basis `u`
(`def:sg-test-ideal`). For Noetherian `A` it equals `testChain hu I c e` for `e ≫ 0`
(`exists_testIdeal_eq`); it does not depend on `u` (`testIdeal_eq_testIdeal`). -/
def testIdeal (I : Ideal A) (c : ℚ) : Ideal A :=
  ⨆ e, hu.testChain I c e

theorem testChain_le_succ (I : Ideal A) (c : ℚ) (e : ℕ) :
    hu.testChain I c e ≤ hu.testChain I c (e + 1) := by
  have h1 : frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊) ≤ I ^ ⌈c * (p : ℚ) ^ (e + 1)⌉₊ := by
    refine (frobPow_le_pow _ _).trans ?_
    rw [← pow_mul, pow_one]
    exact Ideal.pow_le_pow_right (ceil_mul_pow_succ_le c e)
  calc hu.testChain I c e
      = hu.frobRoot e (hu.frobRoot 1 (frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊))) := by
        rw [frobRoot_frobPow]; rfl
    _ = hu.frobRoot (1 + e) (frobPow (p ^ 1) (I ^ ⌈c * (p : ℚ) ^ e⌉₊)) := hu.frobRoot_frobRoot ..
    _ ≤ hu.testChain I c (e + 1) := by
        rw [add_comm]
        exact hu.frobRoot_mono _ h1

/-- The Blickle–Mustaţă–Smith chain is ascending (`lem:sg-test-stable`). -/
theorem testChain_mono (I : Ideal A) (c : ℚ) : Monotone (hu.testChain I c) :=
  monotone_nat_of_le_succ (hu.testChain_le_succ I c)

theorem testChain_le_testIdeal (I : Ideal A) (c : ℚ) (e : ℕ) :
    hu.testChain I c e ≤ hu.testIdeal I c :=
  le_iSup (hu.testChain I c) e

/-- **Stabilization** (`lem:sg-test-stable`): `τ(I^c) = (I^⌈c p^e⌉)^[1/p^e]` for all `e ≫ 0`. -/
theorem exists_testIdeal_eq [IsNoetherianRing A] (I : Ideal A) (c : ℚ) :
    ∃ e₀, ∀ e, e₀ ≤ e → hu.testIdeal I c = hu.testChain I c e := by
  obtain ⟨e₀, he₀⟩ := monotone_stabilizes_iff_noetherian.2
    (inferInstance : IsNoetherianRing A) ⟨hu.testChain I c, hu.testChain_mono I c⟩
  refine ⟨e₀, fun e he => le_antisymm (iSup_le fun e' => ?_) (hu.testChain_le_testIdeal I c e)⟩
  have h1 : hu.testChain I c e = hu.testChain I c (max e' e) :=
    (he₀ e he).symm.trans (he₀ _ (he.trans (le_max_right _ _)))
  rw [h1]
  exact hu.testChain_mono I c (le_max_left _ _)

/-- For `e ≫ 0`, `τ(I^c)` is the Frobenius-trace image `Φ_u^e(I^⌈c p^e⌉)` (FHX eq. `eq:test-def`). -/
theorem exists_coe_testIdeal_eq_image [IsNoetherianRing A] (I : Ideal A) (c : ℚ) :
    ∃ e₀, ∀ e, e₀ ≤ e → (hu.testIdeal I c : Set A) =
      hu.traceIter e '' (I ^ ⌈c * (p : ℚ) ^ e⌉₊ : Ideal A) := by
  obtain ⟨e₀, he₀⟩ := hu.exists_testIdeal_eq I c
  exact ⟨e₀, fun e he => by rw [he₀ e he]; rfl⟩

/-- `τ(I^c)` is monotone in `I`. -/
theorem testIdeal_mono {I J : Ideal A} (h : I ≤ J) (c : ℚ) : hu.testIdeal I c ≤ hu.testIdeal J c :=
  iSup_mono fun _ => hu.frobRoot_mono _ (Ideal.pow_right_mono h _)

/-- `τ(I^c)` is antitone in `c`. -/
theorem testIdeal_anti (I : Ideal A) {c c' : ℚ} (h : c ≤ c') :
    hu.testIdeal I c' ≤ hu.testIdeal I c :=
  iSup_mono fun _ => hu.frobRoot_mono _ (Ideal.pow_le_pow_right
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right h (by positivity))))

theorem le_testIdeal_of_le_one (I : Ideal A) {c : ℚ} (hc : c ≤ 1) : I ≤ hu.testIdeal I c := by
  refine le_trans ?_ (hu.testChain_le_testIdeal I c 0)
  rw [testChain, frobRoot_zero, pow_zero, mul_one]
  refine le_trans (pow_one I).ge (Ideal.pow_le_pow_right ?_)
  rw [Nat.ceil_le]
  exact_mod_cast hc

/-- `I ≤ τ(I^1)` (`lem:sg-test-stable`). -/
theorem le_testIdeal_one (I : Ideal A) : I ≤ hu.testIdeal I 1 :=
  hu.le_testIdeal_of_le_one I le_rfl

theorem testIdeal_of_nonpos (I : Ideal A) {c : ℚ} (hc : c ≤ 0) : hu.testIdeal I c = ⊤ := by
  refine top_le_iff.1 (le_trans ?_ (hu.testChain_le_testIdeal I c 0))
  rw [testChain, frobRoot_zero, pow_zero, mul_one, Nat.ceil_eq_zero.2 hc, pow_zero,
    Ideal.one_eq_top]

@[simp]
theorem testIdeal_zero (I : Ideal A) : hu.testIdeal I 0 = ⊤ :=
  hu.testIdeal_of_nonpos I le_rfl

/-- **Independence of the `p`-basis**: test ideals with respect to two `p`-bases agree. -/
theorem testIdeal_eq_testIdeal {τ : Type*} [Fintype τ] [DecidableEq τ] {v : τ → A}
    (hv : IsPBasis p v) (I : Ideal A) (c : ℚ) : hu.testIdeal I c = hv.testIdeal I c := by
  simp only [testIdeal, testChain, hu.frobRoot_eq_frobRoot hv]

/-! ### Comparison of exponents and subadditivity (`lem:sg-test-subadditive`) -/

/-- **The test element estimate** (`lem:sg-test-subadditive`(1)): if `g ∈ I` and
`(g^r)^[1/p^k] = A`, then `(I^N)^[1/Q] ≤ (I^(N p^k + r))^[1/(p^k Q)]` for all `N` and `Q = p^e`,
since `(I^N)^[1/Q] = (g^r (I^N)^[p^k])^[1/(p^k Q)]`. -/
theorem frobRoot_pow_le_frobRoot_pow_add {I : Ideal A} {g : A} (hgI : g ∈ I) {r k : ℕ}
    (hk : hu.frobRoot k (Ideal.span {g ^ r}) = ⊤) (e N : ℕ) :
    hu.frobRoot e (I ^ N) ≤ hu.frobRoot (k + e) (I ^ (N * p ^ k + r)) :=
  calc hu.frobRoot e (I ^ N)
      = hu.frobRoot e (hu.frobRoot k (Ideal.span {g ^ r}) * I ^ N) := by rw [hk, Ideal.top_mul]
    _ = hu.frobRoot e (hu.frobRoot k (Ideal.span {g ^ r} * frobPow (p ^ k) (I ^ N))) := by
        rw [frobRoot_mul_frobPow]
    _ = hu.frobRoot (k + e) (Ideal.span {g ^ r} * frobPow (p ^ k) (I ^ N)) :=
        hu.frobRoot_frobRoot ..
    _ ≤ hu.frobRoot (k + e) (I ^ (N * p ^ k + r)) := by
        refine hu.frobRoot_mono _ ?_
        rw [pow_add, pow_mul, mul_comm]
        refine Ideal.mul_mono ?_ ?_
        · exact frobPow_le_pow _ _
        · rw [Ideal.span_singleton_le_iff_mem]
          exact Ideal.pow_mem_pow hgI r

/-- In a Noetherian domain, for `I ≠ 0` and `r : ℕ` there is `k` with
`(I^N)^[1/p^e] ≤ (I^(N p^k + r))^[1/p^(k + e)]` for all `e, N`. -/
theorem exists_frobRoot_pow_le_frobRoot_pow_add [IsDomain A] [IsNoetherianRing A] {I : Ideal A}
    (hI : I ≠ ⊥) (r : ℕ) :
    ∃ k, ∀ e N, hu.frobRoot e (I ^ N) ≤ hu.frobRoot (k + e) (I ^ (N * p ^ k + r)) := by
  obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨k, hk⟩ := hu.exists_frobRoot_span_singleton_eq_top (pow_ne_zero r hg0)
  exact ⟨k, hu.frobRoot_pow_le_frobRoot_pow_add hgI hk⟩

variable [IsDomain A] [IsNoetherianRing A]

/-- `τ((I^r)^c) = τ(I^{r c})` for `I ≠ 0` and `c ≥ 0` (`lem:sg-test-subadditive`(2)). -/
theorem testIdeal_pow {I : Ideal A} (hI : I ≠ ⊥) {c : ℚ} (hc : 0 ≤ c) (r : ℕ) :
    hu.testIdeal (I ^ r) c = hu.testIdeal I (r * c) := by
  apply le_antisymm
  · refine iSup_le fun e => le_trans ?_ (hu.testChain_le_testIdeal I _ e)
    refine hu.frobRoot_mono _ ?_
    rw [← pow_mul]
    refine Ideal.pow_le_pow_right ?_
    rw [Nat.ceil_le]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg r)
  · obtain ⟨k₀, hk₀⟩ := hu.exists_frobRoot_pow_le_frobRoot_pow_add hI r
    refine iSup_le fun e => le_trans (hk₀ e _) ?_
    refine le_trans ?_ (hu.testChain_le_testIdeal (I ^ r) c (k₀ + e))
    refine hu.frobRoot_mono _ ?_
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

/-- **Subadditivity** (`lem:sg-test-subadditive`(3)): `τ(I^{c+d}) ≤ τ(I^c) τ(I^d)` for `I ≠ 0`
and `c, d ≥ 0`. -/
theorem testIdeal_add_le {I : Ideal A} (hI : I ≠ ⊥) {c d : ℚ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    hu.testIdeal I (c + d) ≤ hu.testIdeal I c * hu.testIdeal I d := by
  obtain ⟨k₀, hk₀⟩ := hu.exists_frobRoot_pow_le_frobRoot_pow_add hI 2
  refine iSup_le fun e => le_trans (hk₀ e _) ?_
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
  refine le_trans (hu.frobRoot_mono _ h4) (le_trans (hu.frobRoot_mul_le _ _ _) ?_)
  exact Ideal.mul_mono (hu.testChain_le_testIdeal I c (k₀ + e))
    (hu.testChain_le_testIdeal I d (k₀ + e))

/-- `τ(I^{l c}) ≤ τ(I^c)^l` for `I ≠ 0` and `c ≥ 0` (`lem:sg-test-subadditive`(3)). -/
theorem testIdeal_nsmul_le {I : Ideal A} (hI : I ≠ ⊥) {c : ℚ} (hc : 0 ≤ c) :
    ∀ l : ℕ, hu.testIdeal I (l * c) ≤ hu.testIdeal I c ^ l
  | 0 => by rw [pow_zero, Ideal.one_eq_top]; exact le_top
  | l + 1 => by
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact le_trans (hu.testIdeal_add_le hI (by positivity) hc)
      (Ideal.mul_mono_left (testIdeal_nsmul_le hI hc l))

end IsPBasis

/-! ### Asymptotic test ideals (`lem:sg-asymptotic`) -/

namespace IsPBasis

/-- The asymptotic test ideal `B_m = τ(J_•^m) = ⨆_{q > 0} τ(J_q^{m/q})` of a sequence of ideals,
with respect to the `p`-basis `u` (`lem:sg-asymptotic`). For a graded sequence of nonzero ideals in
a Noetherian domain it equals `τ(J_q^{m/q})` for all sufficiently divisible `q`
(`exists_asymptoticTestIdeal_eq`). -/
def asymptoticTestIdeal (J : ℕ → Ideal A) (m : ℕ) : Ideal A :=
  ⨆ (q : ℕ) (_ : 0 < q), hu.testIdeal (J q) ((m : ℚ) / q)

theorem testIdeal_le_asymptoticTestIdeal (J : ℕ → Ideal A) (m : ℕ) {q : ℕ} (hq : 0 < q) :
    hu.testIdeal (J q) ((m : ℚ) / q) ≤ hu.asymptoticTestIdeal J m :=
  le_iSup₂ (f := fun (q : ℕ) (_ : 0 < q) => hu.testIdeal (J q) ((m : ℚ) / q)) q hq

/-- Independence of the `p`-basis for asymptotic test ideals. -/
theorem asymptoticTestIdeal_eq_asymptoticTestIdeal {τ : Type*} [Fintype τ] [DecidableEq τ]
    {v : τ → A} (hv : IsPBasis p v) (J : ℕ → Ideal A) (m : ℕ) :
    hu.asymptoticTestIdeal J m = hv.asymptoticTestIdeal J m := by
  simp only [asymptoticTestIdeal, hu.testIdeal_eq_testIdeal hv]

/-- `J_m ≤ B_m` for `m > 0` (`lem:sg-asymptotic`(3)). -/
theorem le_asymptoticTestIdeal (J : ℕ → Ideal A) {m : ℕ} (hm : 0 < m) :
    J m ≤ hu.asymptoticTestIdeal J m := by
  refine le_trans ?_ (hu.testIdeal_le_asymptoticTestIdeal J m hm)
  rw [div_self (Nat.cast_ne_zero.2 hm.ne')]
  exact hu.le_testIdeal_one (J m)

variable [IsDomain A] [IsNoetherianRing A] {J : ℕ → Ideal A}

/-- `τ(J_q^{m/q}) ≤ τ(J_{q'}^{m/q'})` whenever `q ∣ q'` (`lem:sg-asymptotic`(1)). -/
theorem testIdeal_le_testIdeal_of_dvd (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hdvd : q ∣ q') :
    hu.testIdeal (J q) ((m : ℚ) / q) ≤ hu.testIdeal (J q') ((m : ℚ) / q') := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hq'
  have hc : (0 : ℚ) ≤ (m : ℚ) / (q * k : ℕ) := by positivity
  have h1 : (m : ℚ) / q = (k : ℚ) * ((m : ℚ) / (q * k : ℕ)) := by
    push_cast
    field_simp
  rw [h1, ← hu.testIdeal_pow (hne q hq) hc k]
  refine hu.testIdeal_mono (le_trans (pow_le_of_mul_le_add hJ q hk) ?_) _
  rw [mul_comm]

/-- **Stabilization** (`lem:sg-asymptotic`(2)): there is `q₀ > 0` such that `B_m = τ(J_q^{m/q})`
for every `q > 0` divisible by `q₀`. -/
theorem exists_asymptoticTestIdeal_eq (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ q₀, 0 < q₀ ∧ ∀ q, 0 < q → q₀ ∣ q →
      hu.asymptoticTestIdeal J m = hu.testIdeal (J q) ((m : ℚ) / q) := by
  set F : ℕ → Ideal A := fun q => hu.testIdeal (J q) ((m : ℚ) / q)
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2
    (inferInstance : IsNoetherianRing A) {I | ∃ q, 0 < q ∧ F q = I} ⟨F 1, 1, one_pos, rfl⟩
  have hle : ∀ q, 0 < q → F q ≤ F q₀ := by
    intro q hq
    have hqq : 0 < q * q₀ := Nat.mul_pos hq hq₀
    have h1 : F q ≤ F (q * q₀) :=
      hu.testIdeal_le_testIdeal_of_dvd hJ hne m hq hqq (dvd_mul_right q q₀)
    have h2 : F q₀ ≤ F (q * q₀) :=
      hu.testIdeal_le_testIdeal_of_dvd hJ hne m hq₀ hqq (dvd_mul_left q₀ q)
    have h3 : F q₀ = F (q * q₀) := by
      by_contra hne'
      exact hmax _ ⟨q * q₀, hqq, rfl⟩ (lt_of_le_of_ne h2 hne')
    rw [h3]
    exact h1
  have hB : hu.asymptoticTestIdeal J m = F q₀ :=
    le_antisymm (iSup₂_le hle) (hu.testIdeal_le_asymptoticTestIdeal J m hq₀)
  refine ⟨q₀, hq₀, fun q hq hdvd => le_antisymm ?_ ?_⟩
  · rw [hB]
    exact hu.testIdeal_le_testIdeal_of_dvd hJ hne m hq₀ hq hdvd
  · exact hu.testIdeal_le_asymptoticTestIdeal J m hq

/-- `B_m` as a single Frobenius root: for `q` divisible enough and `e ≫ 0`,
`B_m = (J_q^⌈(m/q) p^e⌉)^[1/p^e]`. -/
theorem exists_asymptoticTestIdeal_eq_frobRoot (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ q₀, 0 < q₀ ∧ ∀ q, 0 < q → q₀ ∣ q → ∃ e₀, ∀ e, e₀ ≤ e →
      hu.asymptoticTestIdeal J m = hu.frobRoot e (J q ^ ⌈(m : ℚ) / q * (p : ℚ) ^ e⌉₊) := by
  obtain ⟨q₀, hq₀, h₀⟩ := hu.exists_asymptoticTestIdeal_eq hJ hne m
  refine ⟨q₀, hq₀, fun q hq hdvd => ?_⟩
  obtain ⟨e₀, he₀⟩ := hu.exists_testIdeal_eq (J q) ((m : ℚ) / q)
  exact ⟨e₀, fun e he => (h₀ q hq hdvd).trans (he₀ e he)⟩

/-- **Subadditivity of asymptotic test ideals** (`lem:sg-asymptotic`(3)): `B_{m l} ≤ B_m ^ l`. -/
theorem asymptoticTestIdeal_mul_le (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m l : ℕ) :
    hu.asymptoticTestIdeal J (m * l) ≤ hu.asymptoticTestIdeal J m ^ l := by
  obtain ⟨q₁, hq₁, h₁⟩ := hu.exists_asymptoticTestIdeal_eq hJ hne (m * l)
  obtain ⟨q₂, hq₂, h₂⟩ := hu.exists_asymptoticTestIdeal_eq hJ hne m
  have hq : 0 < q₁ * q₂ := Nat.mul_pos hq₁ hq₂
  rw [h₁ _ hq (dvd_mul_right _ _), h₂ _ hq (dvd_mul_left _ _)]
  have h : ((m * l : ℕ) : ℚ) / (q₁ * q₂ : ℕ) = (l : ℚ) * ((m : ℚ) / (q₁ * q₂ : ℕ)) := by
    push_cast
    ring
  rw [h]
  exact hu.testIdeal_nsmul_le (hne _ hq) (by positivity) l

end IsPBasis

/-! ### Base change -/

section BaseChange

variable {B : Type*} [CommRing B] [CharP B p] (φ : A →+* B) (hφu : IsPBasis p (φ ∘ u))

/-- **Test ideals commute with base change** along any `φ : A → B` for which `φ ∘ u` is a
`p`-basis of `B` (e.g. a localization): `τ((I B)^c) = τ(I^c) B`. -/
theorem IsPBasis.testIdeal_map (I : Ideal A) (c : ℚ) :
    hφu.testIdeal (I.map φ) c = (hu.testIdeal I c).map φ := by
  simp only [IsPBasis.testIdeal, IsPBasis.testChain, ← Ideal.map_pow, hu.frobRoot_map φ hφu,
    Ideal.map_iSup]

/-- **Asymptotic test ideals commute with base change** along any `φ : A → B` for which `φ ∘ u`
is a `p`-basis of `B`: `B_m(B; J_• B) = B_m(A; J_•) B`. -/
theorem IsPBasis.asymptoticTestIdeal_map (J : ℕ → Ideal A) (m : ℕ) :
    hφu.asymptoticTestIdeal (fun q => (J q).map φ) m = (hu.asymptoticTestIdeal J m).map φ := by
  simp only [IsPBasis.asymptoticTestIdeal, hu.testIdeal_map φ hφu, Ideal.map_iSup]

end BaseChange

end EnvelopeProperty.Cartier
