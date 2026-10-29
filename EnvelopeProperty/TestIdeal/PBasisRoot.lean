/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Cartier.FormsDVR
import EnvelopeProperty.TestIdeal.FrobeniusRoot

/-!
# Frobenius roots in rings with a `p`-basis

Let `A` be a commutative ring of prime characteristic `p` with a finite `p`-basis
`u : σ → A` (`EnvelopeProperty.Cartier.IsPBasis p u`), and let `Φ_u^e` be the iterated Frobenius
trace (`IsPBasis.traceIter`). This file ports the Frobenius algebra of
`EnvelopeProperty.TestIdeal.FrobeniusRoot` from polynomial rings over perfect fields (variables =
`p`-basis) to such rings, following the blueprint `subsec:sg-pbasis` (`conv:sg-pbasis`,
`lem:sg-pbasis-basics`, `def:sg-root`, `lem:sg-root-basic`, `lem:sg-test-element`), which is the
local test-ideal theory used for Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Theorem 3.1 on a smooth projective variety (eq. `eq:test-def`).

## `p`-bases (`lem:sg-pbasis-basics`)

* `IsPBasis.traceIter_pow_mul_mono`: `Φ_u^e(g^Q u^n) = g u^{⌊n/Q⌋}` if every `n_i ≡ Q - 1 mod Q`,
  and `0` otherwise (`Q = p^e`).
* `IsPBasis.sum_traceIter_mul_mono`, `IsPBasis.traceIter_mono_sub_mul_sum`: every `f` is uniquely
  `f = ∑_{a ∈ [0,Q)^σ} f_{[a]}^Q u^a`, and `f_{[a]} = Φ_u^e(u^{Q-1-a} f)` (part (1)).
* `IsPBasis.traceIter_eq_of_sum_eq`: `Φ_u^e(f) = f_{[Q-1,…,Q-1]}`, and
  `IsPBasis.traceIter_mono_pow_sub_one`: `Φ_u^e(u^{Q-1}) = 1`.
* `IsPBasis.traceIter_eq_traceIter_jac_pow_mul`: for two `p`-bases `y, u` of a field,
  `Φ_u^e(f) = Φ_y^e(J(y/u)^{Q-1} f)` (part (2), the transformation rule), and its version
  `IsPBasis.traceIter_eq_traceIter_jac_pow_mul_of_isDomain` for a domain.
* `IsPBasis.map_algebraMap_of_isLocalization`, `IsPBasis.traceIter_mk'`: `u` is a `p`-basis of any
  localization `B = M⁻¹A` (of characteristic `p`), and `Φ_u^e(f/s) = Φ_u^e(s^{Q-1} f)/s` (part (3)).
  `IsPBasis.map_ringEquiv` transports `p`-bases along ring isomorphisms.

## Frobenius roots (`def:sg-root`, `lem:sg-root-basic`, `lem:sg-test-element`)

* `IsPBasis.frobRoot hu e I`: the Frobenius root `I^[1/p^e]`, *defined* as the image
  `Φ_u^e '' I` (an ideal by `p^{-e}`-linearity).
* `IsPBasis.frobRoot_le_iff`: the adjunction `I^[1/Q] ≤ J ↔ I ≤ J^[Q]`
  (`gc_frobRoot_frobPow`). Consequently the root does not depend on the `p`-basis
  (`IsPBasis.frobRoot_eq_frobRoot`), commutes with every base change `φ : A → B` along which `u`
  stays a `p`-basis, e.g. localizations and fraction fields (`IsPBasis.frobRoot_map`).
* `frobRoot_frobPow`, `frobRoot_frobRoot`, `frobRoot_mul_le`, `frobRoot_mul_frobPow`,
  `frobRoot_mono`, `frobRoot_sup`, `frobRoot_span`, `frobRoot_le_frobRoot_add` (increasing in `e`).
* `IsPBasis.exists_frobRoot_span_singleton_eq_top`: the test-element lemma; in a Noetherian domain,
  `(g)^[1/p^e] = A` for some `e` whenever `g ≠ 0`. The degree argument of the polynomial case is
  replaced by Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isDomain`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Digit arithmetic -/

section Digits

/-- `x mod ab = ab - 1` iff `x mod a = a - 1` and `⌊x/a⌋ mod b = b - 1`. -/
theorem mod_mul_eq_mul_sub_one_iff {a b x : ℕ} (ha : 0 < a) (hb : 0 < b) :
    x % (a * b) = a * b - 1 ↔ x % a = a - 1 ∧ x / a % b = b - 1 := by
  rw [Nat.mod_mul]
  have h1 : x % a < a := Nat.mod_lt _ ha
  have h2 : x / a % b < b := Nat.mod_lt _ hb
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_lt hb
  simp only [zero_add] at h2 ⊢
  have hab : a * (b' + 1) - 1 = (a - 1) + a * b' := by rw [mul_add, mul_one]; omega
  rw [hab, Nat.add_sub_cancel]
  constructor
  · intro h
    have hmod := congrArg (· % a) h
    have hdiv := congrArg (· / a) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt (show a - 1 < a by omega)] at hmod
    simp only [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt h1,
      Nat.div_eq_of_lt (show a - 1 < a by omega), zero_add] at hdiv
    exact ⟨hmod, hdiv⟩
  · rintro ⟨h, h'⟩
    rw [h, h']

/-- For `a < Q`: `(Q - 1 - a + x) mod Q = Q - 1` iff `a = x mod Q`. -/
theorem sub_one_sub_add_mod_eq_iff {Q a x : ℕ} (hQ : 0 < Q) (ha : a < Q) :
    (Q - 1 - a + x) % Q = Q - 1 ↔ a = x % Q := by
  have hx := Nat.div_add_mod x Q
  have hr : x % Q < Q := Nat.mod_lt _ hQ
  set k := x / Q
  set r := x % Q
  have h1 : Q - 1 - a + x = Q * k + (Q - 1 - a + r) := by omega
  rw [h1, Nat.mul_add_mod]
  constructor
  · intro h
    by_contra hne
    by_cases hlt : Q - 1 - a + r < Q
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · have h2 : Q - 1 - a + r = (r - a - 1) + Q * 1 := by omega
      rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro h
    rw [← h, show Q - 1 - a + a = Q - 1 by omega, Nat.mod_eq_of_lt (by omega)]

/-- `⌊(Q - 1 - (x mod Q) + x)/Q⌋ = ⌊x/Q⌋`. -/
theorem sub_one_sub_mod_add_div {Q x : ℕ} (hQ : 0 < Q) : (Q - 1 - x % Q + x) / Q = x / Q := by
  have hx := Nat.div_add_mod x Q
  have hr : x % Q < Q := Nat.mod_lt _ hQ
  have h1 : Q - 1 - x % Q + x = Q * (x / Q) + (Q - 1) := by
    generalize Q * (x / Q) = m at hx ⊢
    generalize x % Q = r at hx hr ⊢
    omega
  rw [h1, Nat.mul_add_div hQ, Nat.div_eq_of_lt (show Q - 1 < Q by omega), add_zero]

/-- `(a - 1) b + (b - 1) = ab - 1` for `a, b > 0`. -/
theorem sub_one_mul_add_sub_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a - 1) * b + (b - 1) = a * b - 1 := by
  have h : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  rw [Nat.sub_one_mul]
  omega

end Digits

/-! ### Iterated Frobenius traces -/

section Ring

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A} (hu : IsPBasis p u)

namespace IsPBasis

theorem traceIter_map_zero (e : ℕ) : hu.traceIter e 0 = 0 := by
  induction e with
  | zero => rfl
  | succ e ih => rw [traceIter_succ, ih, map_zero]

/-- The iterated Frobenius trace `Φ_u^e` as an additive map. -/
def traceIterHom (e : ℕ) : A →+ A where
  toFun := hu.traceIter e
  map_zero' := hu.traceIter_map_zero e
  map_add' := hu.traceIter_add e

@[simp]
theorem traceIterHom_apply (e : ℕ) (f : A) : hu.traceIterHom e f = hu.traceIter e f :=
  rfl

theorem traceIter_sum {ι : Type*} (s : Finset ι) (e : ℕ) (f : ι → A) :
    hu.traceIter e (∑ i ∈ s, f i) = ∑ i ∈ s, hu.traceIter e (f i) :=
  map_sum (hu.traceIterHom e) f s

/-- The trace only depends on the family: equal families give equal traces. -/
theorem traceIter_congr {v : σ → A} (hv : IsPBasis p v) (h : u = v) (e : ℕ) (f : A) :
    hu.traceIter e f = hv.traceIter e f := by
  subst h
  rfl

/-- `Φ_u^e(g^Q u^n) = g u^{⌊n/Q⌋}` if `n_i ≡ Q - 1 (mod Q)` for all `i`, and `0` otherwise
(`Q = p^e`). -/
theorem traceIter_pow_mul_mono (e : ℕ) (g : A) (n : σ → ℕ) :
    hu.traceIter e (g ^ p ^ e * mono u n) =
      if ∀ i, n i % p ^ e = p ^ e - 1 then g * mono u (fun i => n i / p ^ e) else 0 := by
  induction e generalizing g n with
  | zero => simp [Nat.mod_one]
  | succ e ih =>
    have hp0 : 0 < p := hp.out.pos
    have hq0 : 0 < p ^ e := pow_pos hp0 e
    rw [traceIter_succ', show g ^ p ^ (e + 1) = (g ^ p ^ e) ^ p by rw [pow_succ, pow_mul],
      hu.trace_pow_mul_mono_nat]
    have key : ∀ i, n i % p ^ (e + 1) = p ^ (e + 1) - 1 ↔
        n i % p = p - 1 ∧ n i / p % p ^ e = p ^ e - 1 := fun i => by
      rw [pow_succ', mod_mul_eq_mul_sub_one_iff hp0 hq0]
    by_cases h : Box.ofNat (p := p) n = Box.top
    · have hd : ∀ i, n i % p = p - 1 := fun i => by
        have := congrArg (fun a : Box σ p => (a i : ℕ)) h
        simpa [Box.ofNat, Box.top] using this
      rw [if_pos h, ih]
      by_cases h2 : ∀ i, n i % p ^ (e + 1) = p ^ (e + 1) - 1
      · rw [if_pos fun i => ((key i).1 (h2 i)).2, if_pos h2]
        congr 2
        funext i
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      · rw [if_neg h2, if_neg]
        exact fun h3 => h2 fun i => (key i).2 ⟨hd i, h3 i⟩
    · rw [if_neg h, traceIter_map_zero, if_neg]
      intro hall
      apply h
      funext i
      apply Fin.ext
      simpa [Box.ofNat, Box.top] using ((key i).1 (hall i)).1

/-- `Φ_u^e(u^{Q-1}) = 1` for `Q = p^e`. -/
theorem traceIter_mono_pow_sub_one (e : ℕ) : hu.traceIter e (mono u fun _ => p ^ e - 1) = 1 := by
  have hq0 : 0 < p ^ e := pow_pos hp.out.pos e
  have h := hu.traceIter_pow_mul_mono e 1 fun _ => p ^ e - 1
  rw [one_pow, one_mul, if_pos fun _ => Nat.mod_eq_of_lt (by omega)] at h
  rw [h, one_mul]
  convert mono_zero u using 2
  funext i
  exact Nat.div_eq_of_lt (by omega)

/-- `Φ_u^e(u^{Q-1-a} g^Q u^n) = g u^{⌊n/Q⌋}` if `a = n mod Q`, and `0` otherwise. -/
theorem traceIter_mono_sub_mul (e : ℕ) (a : Box σ (p ^ e)) (g : A)
    (n : σ → ℕ) :
    hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * (g ^ p ^ e * mono u n)) =
      if a = Box.ofNat n then g * mono u (fun i => n i / p ^ e) else 0 := by
  have hq0 : 0 < p ^ e := pow_pos hp.out.pos e
  rw [mul_left_comm, ← mono_add, hu.traceIter_pow_mul_mono]
  have hiff : (∀ i, ((fun i => p ^ e - 1 - (a i : ℕ)) + n) i % p ^ e = p ^ e - 1) ↔
      a = Box.ofNat n := by
    simp only [Pi.add_apply]
    refine ⟨fun h => funext fun i => Fin.ext ?_, fun h i => ?_⟩
    · exact (sub_one_sub_add_mod_eq_iff hq0 (a i).2).1 (h i)
    · subst h
      exact (sub_one_sub_add_mod_eq_iff hq0 (Box.ofNat (p := p ^ e) n i).2).2 rfl
  by_cases h : a = Box.ofNat n
  · rw [if_pos (hiff.2 h), if_pos h]
    subst h
    congr 2
    funext i
    exact sub_one_sub_mod_add_div hq0
  · rw [if_neg (mt hiff.1 h), if_neg h]

/-- **The expansion of order `Q = p^e`** (`lem:sg-pbasis-basics`(1)):
`f = ∑_{a ∈ [0,Q)^σ} (Φ_u^e(u^{Q-1-a} f))^Q u^a`. -/
theorem sum_traceIter_mul_mono (e : ℕ) (f : A) :
    ∑ a : Box σ (p ^ e),
      hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * f) ^ p ^ e * mono u a.toNat = f := by
  -- every `f` is a sum of terms `g^(p^e) u^n`
  have hcl : ∀ (e : ℕ) (f : A),
      f ∈ AddSubmonoid.closure {x | ∃ (g : A) (n : σ → ℕ), g ^ p ^ e * mono u n = x} := by
    intro e
    induction e with
    | zero => exact fun f => AddSubmonoid.subset_closure ⟨f, 0, by simp⟩
    | succ e ih =>
      intro f
      rw [← hu.sum_coeff f]
      refine AddSubmonoid.sum_mem _ fun b _ => ?_
      have hb := ih (hu.coeff f b)
      generalize hu.coeff f b = x at hb ⊢
      induction hb using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨g, n, rfl⟩ := hx
        refine AddSubmonoid.subset_closure ⟨g, p • n + b.toNat, ?_⟩
        rw [mono_add, mono_smul, mul_pow, pow_succ, pow_mul]
        ring
      | zero => rw [zero_pow hp.out.ne_zero, zero_mul]; exact zero_mem _
      | add x y _ _ hx hy => rw [add_pow_char, add_mul]; exact add_mem hx hy
  -- the right-hand side is additive in `f`
  let S : A →+ A :=
    { toFun := fun f => ∑ a : Box σ (p ^ e),
        hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * f) ^ p ^ e * mono u a.toNat
      map_zero' := by simp [traceIter_map_zero, zero_pow (pow_ne_zero e hp.out.ne_zero)]
      map_add' := fun f g => by
        simp only [mul_add, traceIter_add, add_pow_char_pow, add_mul, sum_add_distrib] }
  change S f = f
  induction hcl e f using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨g, n, rfl⟩ := hx
    change ∑ a : Box σ (p ^ e), _ = _
    simp_rw [hu.traceIter_mono_sub_mul]
    rw [sum_eq_single (Box.ofNat n)]
    · rw [if_pos rfl, mul_pow, mul_assoc, ← mono_eq_pow_mul]
    · intro b _ hb
      rw [if_neg hb, zero_pow (pow_ne_zero e hp.out.ne_zero), zero_mul]
    · simp
  | zero => exact map_zero S
  | add x y _ _ hx hy => rw [map_add, hx, hy]

/-- **Uniqueness of the expansion of order `Q = p^e`**: the coefficient of `u^a` in
`∑_b c_b^Q u^b` is `c_a = Φ_u^e(u^{Q-1-a} ∑_b c_b^Q u^b)`. -/
theorem traceIter_mono_sub_mul_sum (e : ℕ) (c : Box σ (p ^ e) → A)
    (a : Box σ (p ^ e)) :
    hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * ∑ b, c b ^ p ^ e * mono u b.toNat) =
      c a := by
  rw [mul_sum, traceIter_sum, sum_eq_single a]
  · rw [hu.traceIter_mono_sub_mul, if_pos (Box.ofNat_toNat a).symm]
    convert mul_one (c a) using 2
    convert mono_zero u using 2
    funext i
    exact Nat.div_eq_of_lt (a i).2
  · intro b _ hb
    rw [hu.traceIter_mono_sub_mul, if_neg]
    rw [Box.ofNat_toNat]
    exact Ne.symm hb
  · simp

/-- Uniqueness of the expansion, in the form: any decomposition `f = ∑_b c_b^Q u^b` has the
coefficients `c_a = Φ_u^e(u^{Q-1-a} f)`. -/
theorem eq_traceIter_of_sum_eq (e : ℕ) {f : A} {c : Box σ (p ^ e) → A}
    (hf : ∑ b, c b ^ p ^ e * mono u b.toNat = f) (a : Box σ (p ^ e)) :
    c a = hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * f) := by
  rw [← hf, hu.traceIter_mono_sub_mul_sum]

/-- `Φ_u^e(f) = f_{[Q-1,…,Q-1]}`: the iterated trace is the top coefficient of the expansion of
order `Q = p^e`. -/
theorem traceIter_eq_of_sum_eq (e : ℕ) {f : A} {c : Box σ (p ^ e) → A}
    (hf : ∑ b, c b ^ p ^ e * mono u b.toNat = f) : hu.traceIter e f = c Box.top := by
  rw [hu.eq_traceIter_of_sum_eq e hf Box.top]
  congr 1
  convert (one_mul f).symm using 2
  convert mono_zero u using 2
  funext i
  exact Nat.sub_self _

end IsPBasis

end Ring

/-! ### Change of `p`-basis (`lem:sg-pbasis-basics`(2)) -/

section ChangeOfBasis

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The transformation rule** (`lem:sg-pbasis-basics`(2)). For `p`-bases `y, u` of a field of
characteristic `p` and `Q = p^e`: `Φ_u^e(f) = Φ_y^e(J(y/u)^{Q-1} f)`, `J(y/u) = det(∂y_i/∂u_j)`. -/
theorem IsPBasis.traceIter_eq_traceIter_jac_pow_mul {F : Type*} [Field F] [CharP F p]
    {y u : σ → F} (hy : IsPBasis p y) (hu : IsPBasis p u) (e : ℕ) (x : F) :
    hu.traceIter e x = hy.traceIter e (hu.jac y ^ (p ^ e - 1) * x) := by
  induction e generalizing x with
  | zero => simp
  | succ e ih =>
    have hq0 : 0 < p ^ e := pow_pos hp.out.pos e
    rw [traceIter_succ', ih, hy.trace_eq_trace_jac_pow_mul hu, ← hy.trace_pow_mul,
      ← traceIter_succ', ← mul_assoc, ← pow_mul, ← pow_add, pow_succ,
      sub_one_mul_add_sub_one hq0 hp.out.pos]

/-- The transformation rule in a domain: for `p`-bases `y, u` of a domain `A`,
`Φ_u^e(f) = Φ_y^e(J(y/u)^{Q-1} f)`. -/
theorem IsPBasis.traceIter_eq_traceIter_jac_pow_mul_of_isDomain {A : Type*} [CommRing A]
    [IsDomain A] [CharP A p] {y u : σ → A} (hy : IsPBasis p y) (hu : IsPBasis p u) (e : ℕ)
    (x : A) : hu.traceIter e x = hy.traceIter e (hu.jac y ^ (p ^ e - 1) * x) := by
  have hyK := hy.map_of_isFractionRing (K := FractionRing A)
  have huK := hu.map_of_isFractionRing (K := FractionRing A)
  apply IsFractionRing.injective A (FractionRing A)
  rw [← hu.traceIter_map _ huK, ← hy.traceIter_map _ hyK, map_mul, map_pow,
    ← hu.jac_map (algebraMap A (FractionRing A)) huK y,
    hyK.traceIter_eq_traceIter_jac_pow_mul huK]

end ChangeOfBasis

/-! ### Localization and ring isomorphisms (`lem:sg-pbasis-basics`(3)) -/

section Localization

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A}

/-- A `p`-basis is transported along ring isomorphisms. -/
theorem IsPBasis.map_ringEquiv {B : Type*} [CommRing B] [CharP B p] (hu : IsPBasis p u)
    (φ : A ≃+* B) : IsPBasis p (φ ∘ u) := by
  have h : ∀ c : Box σ p → A, pSum p ((φ : A →+* B) ∘ u) ((φ : A →+* B) ∘ c) =
      φ (pSum p u c) := fun c => (map_pSum p (φ : A →+* B) u c).symm
  constructor
  · intro c d hcd
    have hc : c = (φ : A →+* B) ∘ (φ.symm ∘ c) := by funext a; simp
    have hd : d = (φ : A →+* B) ∘ (φ.symm ∘ d) := by funext a; simp
    have h1 : pSum p ((φ : A →+* B) ∘ u) c = pSum p ((φ : A →+* B) ∘ u) d := hcd
    rw [hc, hd, h, h] at h1
    have h2 := hu.injective (φ.injective h1)
    funext a
    simpa using congrFun h2 a
  · intro f
    obtain ⟨c, hc⟩ := hu.surjective (φ.symm f)
    refine ⟨(φ : A →+* B) ∘ c, ?_⟩
    change pSum p ((φ : A →+* B) ∘ u) ((φ : A →+* B) ∘ c) = f
    rw [h, hc, RingEquiv.apply_symm_apply]

variable (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] [CharP B p]

include M in
/-- **`p`-bases of localizations** (`lem:sg-pbasis-basics`(3)): a `p`-basis of `A` is a `p`-basis
of every localization `B = M⁻¹A` of characteristic `p` (e.g. `A_h`, or `Frac A` for a domain). -/
theorem IsPBasis.map_algebraMap_of_isLocalization (hu : IsPBasis p u) :
    IsPBasis p (algebraMap A B ∘ u) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M univ c
    choose d hd using fun a => hb a (mem_univ a)
    have hd0 : algebraMap A B (pSum p u d) = 0 := by
      rw [map_pSum]
      have : algebraMap A B ∘ d = (algebraMap A B (b : A)) • c := by
        funext a
        rw [Function.comp_apply, hd a, Algebra.smul_def]
        rfl
      rw [this, pSum_smul, hc, mul_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M B _).1 hd0
    have hmd : pSum p u ((m : A) • d) = 0 := by
      rw [pSum_smul, ← pow_sub_one_mul hp.out.ne_zero, mul_assoc, hm, mul_zero]
    have hd' : (m : A) • d = 0 := hu.injective (by rw [hmd, map_zero])
    funext a
    have h1 : (m : A) * d a = 0 := congrFun hd' a
    have h2 : algebraMap A B (m : A) * (algebraMap A B (b : A) * c a) = 0 := by
      have h3 := hd a
      rw [Algebra.smul_def] at h3
      rw [← h3, ← map_mul, h1, map_zero]
    rw [Pi.zero_apply]
    rwa [(IsLocalization.map_units B m).mul_right_eq_zero,
      (IsLocalization.map_units B b).mul_right_eq_zero] at h2
  · intro f
    obtain ⟨⟨g, s⟩, rfl⟩ := IsLocalization.mk'_surjective M f
    obtain ⟨w, hw⟩ := IsLocalization.map_units B s
    refine ⟨((w⁻¹ : Bˣ) : B) • (algebraMap A B ∘ hu.coeff (s ^ (p - 1) * g)), ?_⟩
    rw [pSum_smul, ← map_pSum, hu.pSum_coeff, eq_comm, IsLocalization.mk'_eq_iff_eq_mul,
      map_mul, map_pow, ← hw]
    have h1 : (w : B) ^ (p - 1) * (w : B) = (w : B) ^ p := pow_sub_one_mul hp.out.ne_zero _
    calc algebraMap A B g = (((w⁻¹ : Bˣ) : B) * w) ^ p * algebraMap A B g := by simp
      _ = _ := by rw [mul_pow, ← h1]; ring

/-- `Φ_u^e(f/s) = Φ_u^e(s^{Q-1} f)/s` in a localization `B = M⁻¹A` (`lem:sg-pbasis-basics`(3)). -/
theorem IsPBasis.traceIter_mk' (hu : IsPBasis p u) (hB : IsPBasis p (algebraMap A B ∘ u))
    (e : ℕ) (f : A) (s : M) :
    hB.traceIter e (IsLocalization.mk' B f s) =
      IsLocalization.mk' B (hu.traceIter e ((s : A) ^ (p ^ e - 1) * f)) s := by
  obtain ⟨w, hw⟩ := IsLocalization.map_units B s
  have h1 : IsLocalization.mk' B f s =
      ((w⁻¹ : Bˣ) : B) ^ p ^ e * algebraMap A B ((s : A) ^ (p ^ e - 1) * f) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_mul, map_pow, ← hw]
    have h2 : (w : B) ^ (p ^ e - 1) * (w : B) = (w : B) ^ p ^ e :=
      pow_sub_one_mul (pow_ne_zero e hp.out.ne_zero) _
    calc algebraMap A B f = (((w⁻¹ : Bˣ) : B) * w) ^ p ^ e * algebraMap A B f := by simp
      _ = _ := by rw [mul_pow, ← h2]; ring
  rw [h1, hB.traceIter_pow_mul, hu.traceIter_map (algebraMap A B) hB, eq_comm,
    IsLocalization.mk'_eq_iff_eq_mul, ← hw, mul_right_comm, Units.inv_mul, one_mul]

end Localization

/-! ### Frobenius roots (`def:sg-root`, `lem:sg-root-basic`) -/

section Root

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A} (hu : IsPBasis p u)

namespace IsPBasis

/-- The Frobenius root `I^[1/p^e]` with respect to the `p`-basis `u`, defined as the image
`Φ_u^e '' I` of `I` (an ideal by `Φ_u^e(g^{p^e} f) = g Φ_u^e(f)`). By `frobRoot_le_iff` it is the
smallest ideal `J` with `I ≤ J^[p^e]`, so it does not depend on `u` (`frobRoot_eq_frobRoot`). -/
def frobRoot (e : ℕ) (I : Ideal A) : Ideal A where
  carrier := hu.traceIter e '' I
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, I.add_mem hf hg, hu.traceIter_add e f g⟩
  zero_mem' := ⟨0, I.zero_mem, hu.traceIter_map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c ^ p ^ e * f, I.mul_mem_left _ hf, hu.traceIter_pow_mul e c f⟩

theorem coe_frobRoot (e : ℕ) (I : Ideal A) : (hu.frobRoot e I : Set A) = hu.traceIter e '' I :=
  rfl

theorem mem_frobRoot {e : ℕ} {I : Ideal A} {f : A} :
    f ∈ hu.frobRoot e I ↔ ∃ g ∈ I, hu.traceIter e g = f :=
  Iff.rfl

theorem traceIter_mem_frobRoot {e : ℕ} {I : Ideal A} {f : A} (hf : f ∈ I) :
    hu.traceIter e f ∈ hu.frobRoot e I :=
  ⟨f, hf, rfl⟩

/-- `Φ_u^e` maps `J^[p^e]` into `J`. -/
theorem traceIter_mem_of_mem_frobPow {e : ℕ} {J : Ideal A} {f : A} (hf : f ∈ frobPow (p ^ e) J) :
    hu.traceIter e f ∈ J := by
  suffices h : ∀ r, hu.traceIter e (r * f) ∈ J by simpa using h 1
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    intro r
    rw [mul_comm, hu.traceIter_pow_mul]
    exact J.mul_mem_right _ hg
  | zero => intro r; rw [mul_zero, traceIter_map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => intro r; rw [mul_add, traceIter_add]; exact J.add_mem (hx r) (hy r)
  | smul a x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx (r * a)

/-- `I ≤ (I^[1/p^e])^[p^e]`: every `f ∈ I` is `∑_a f_{[a]}^Q u^a` with
`f_{[a]} = Φ_u^e(u^{Q-1-a} f) ∈ I^[1/Q]`. -/
theorem le_frobPow_frobRoot (e : ℕ) (I : Ideal A) : I ≤ frobPow (p ^ e) (hu.frobRoot e I) := by
  intro f hf
  rw [← hu.sum_traceIter_mul_mono e f]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _
    (pow_mem_frobPow (hu.traceIter_mem_frobRoot (I.mul_mem_left _ hf)))

/-- **The adjunction** (`lem:sg-root-basic`(1)): `I^[1/Q] ≤ J ↔ I ≤ J^[Q]`. -/
theorem frobRoot_le_iff {e : ℕ} {I J : Ideal A} : hu.frobRoot e I ≤ J ↔ I ≤ frobPow (p ^ e) J := by
  constructor
  · intro h
    exact (hu.le_frobPow_frobRoot e I).trans (frobPow_mono _ h)
  · rintro h _ ⟨f, hf, rfl⟩
    exact hu.traceIter_mem_of_mem_frobPow (h hf)

/-- Frobenius roots are left adjoint to Frobenius powers. -/
theorem gc_frobRoot_frobPow (e : ℕ) : GaloisConnection (hu.frobRoot e) (frobPow (p ^ e)) :=
  fun _ _ => hu.frobRoot_le_iff

theorem frobRoot_mono (e : ℕ) : Monotone (hu.frobRoot e) :=
  (hu.gc_frobRoot_frobPow e).monotone_l

/-- `I^[1/Q]` is the smallest ideal `J` with `I ≤ J^[Q]`. -/
theorem isLeast_frobRoot (e : ℕ) (I : Ideal A) :
    IsLeast {J | I ≤ frobPow (p ^ e) J} (hu.frobRoot e I) :=
  ⟨hu.le_frobPow_frobRoot e I, fun _ hJ => hu.frobRoot_le_iff.2 hJ⟩

/-- **Independence of the `p`-basis**: Frobenius roots with respect to two `p`-bases agree (both
are left adjoint to `J ↦ J^[p^e]`). -/
theorem frobRoot_eq_frobRoot {τ : Type*} [Fintype τ] [DecidableEq τ] {v : τ → A}
    (hv : IsPBasis p v) (e : ℕ) (I : Ideal A) : hu.frobRoot e I = hv.frobRoot e I :=
  (hu.gc_frobRoot_frobPow e).l_unique (hv.gc_frobRoot_frobPow e) fun _ => rfl

/-- The root of an ideal given by generators is generated by the coefficients
`Φ_u^e(u^{Q-1-a} f)` of the generators. -/
theorem frobRoot_span (e : ℕ) (S : Set A) :
    hu.frobRoot e (Ideal.span S) = Ideal.span
      {g | ∃ f ∈ S, ∃ a : Box σ (p ^ e), hu.traceIter e (mono u (fun i => p ^ e - 1 - a i) * f) = g} := by
  apply le_antisymm
  · rw [frobRoot_le_iff, Ideal.span_le]
    intro f hf
    rw [SetLike.mem_coe, ← hu.sum_traceIter_mul_mono e f]
    exact Ideal.sum_mem _ fun a _ =>
      Ideal.mul_mem_right _ _ (pow_mem_frobPow (Ideal.subset_span ⟨f, hf, a, rfl⟩))
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, a, rfl⟩
    exact hu.traceIter_mem_frobRoot (Ideal.mul_mem_left _ _ (Ideal.subset_span hf))

@[simp]
theorem frobRoot_zero (I : Ideal A) : hu.frobRoot 0 I = I := by
  ext f
  simp [mem_frobRoot]

@[simp]
theorem frobRoot_bot (e : ℕ) : hu.frobRoot e (⊥ : Ideal A) = ⊥ :=
  (hu.gc_frobRoot_frobPow e).l_bot

/-- `(J^[Q])^[1/Q] = J` (`lem:sg-root-basic`(2)). -/
@[simp]
theorem frobRoot_frobPow (e : ℕ) (J : Ideal A) : hu.frobRoot e (frobPow (p ^ e) J) = J := by
  refine le_antisymm ((hu.gc_frobRoot_frobPow e).l_u_le J) fun g hg => ?_
  refine ⟨g ^ p ^ e * mono u (fun _ => p ^ e - 1),
    Ideal.mul_mem_right _ _ (pow_mem_frobPow hg), ?_⟩
  rw [hu.traceIter_pow_mul, hu.traceIter_mono_pow_sub_one, mul_one]

@[simp]
theorem frobRoot_top (e : ℕ) : hu.frobRoot e (⊤ : Ideal A) = ⊤ := by
  simpa using hu.frobRoot_frobPow e ⊤

theorem frobRoot_sup (e : ℕ) (I J : Ideal A) :
    hu.frobRoot e (I ⊔ J) = hu.frobRoot e I ⊔ hu.frobRoot e J :=
  (hu.gc_frobRoot_frobPow e).l_sup

theorem frobRoot_iSup (e : ℕ) {ι : Sort*} (I : ι → Ideal A) :
    hu.frobRoot e (⨆ i, I i) = ⨆ i, hu.frobRoot e (I i) :=
  (hu.gc_frobRoot_frobPow e).l_iSup

/-- `(I J^[Q])^[1/Q] = I^[1/Q] J`. -/
theorem frobRoot_mul_frobPow (e : ℕ) (I J : Ideal A) :
    hu.frobRoot e (I * frobPow (p ^ e) J) = hu.frobRoot e I * J := by
  apply le_antisymm
  · rw [frobRoot_le_iff, frobPow_mul]
    exact Ideal.mul_mono_left (hu.le_frobPow_frobRoot e I)
  · rw [Ideal.mul_le]
    rintro _ ⟨f, hf, rfl⟩ g hg
    refine ⟨g ^ p ^ e * f, ?_, ?_⟩
    · rw [mul_comm (g ^ p ^ e) f]
      exact Ideal.mul_mem_mul hf (pow_mem_frobPow hg)
    · rw [hu.traceIter_pow_mul, mul_comm]

/-- `(I J)^[1/Q] ≤ I^[1/Q] J^[1/Q]` (`lem:sg-root-basic`(3)). -/
theorem frobRoot_mul_le (e : ℕ) (I J : Ideal A) :
    hu.frobRoot e (I * J) ≤ hu.frobRoot e I * hu.frobRoot e J := by
  rw [frobRoot_le_iff, frobPow_mul]
  exact Ideal.mul_mono (hu.le_frobPow_frobRoot e I) (hu.le_frobPow_frobRoot e J)

/-- `(I^[1/Q])^[1/Q'] = I^[1/(Q Q')]` (`lem:sg-root-basic`(2)). -/
theorem frobRoot_frobRoot (e e' : ℕ) (I : Ideal A) :
    hu.frobRoot e' (hu.frobRoot e I) = hu.frobRoot (e + e') I := by
  ext f
  simp only [mem_frobRoot]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, by rw [hu.traceIter_traceIter, add_comm]⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hu.traceIter e g, ⟨g, hg, rfl⟩, by rw [hu.traceIter_traceIter, add_comm]⟩

/-- The roots `I^[1/p^e]` increase with `e`. -/
theorem frobRoot_le_frobRoot_succ (e : ℕ) (I : Ideal A) :
    hu.frobRoot e I ≤ hu.frobRoot (e + 1) I :=
  calc hu.frobRoot e I = hu.frobRoot e (hu.frobRoot 1 (frobPow (p ^ 1) I)) := by
        rw [frobRoot_frobPow]
    _ = hu.frobRoot (1 + e) (frobPow (p ^ 1) I) := hu.frobRoot_frobRoot ..
    _ ≤ hu.frobRoot (e + 1) I := by
        rw [add_comm]
        exact hu.frobRoot_mono _ (frobPow_le (pow_ne_zero 1 hp.out.ne_zero) I)

theorem frobRoot_le_frobRoot_add (e k : ℕ) (I : Ideal A) :
    hu.frobRoot e I ≤ hu.frobRoot (e + k) I := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih.trans (hu.frobRoot_le_frobRoot_succ (e + k) I)

theorem frobRoot_monotone_exp (I : Ideal A) : Monotone fun e => hu.frobRoot e I :=
  monotone_nat_of_le_succ fun e => hu.frobRoot_le_frobRoot_succ e I

/-! ### Test elements (`lem:sg-test-element`) -/

/-- **Test elements.** In a Noetherian domain with a `p`-basis, every `g ≠ 0` has
`(g)^[1/p^e] = A` for some `e`. The ideals `(g)^[1/p^e]` increase and stabilize at some `𝔠`; since
`(g) ≤ 𝔠^[p^e] ≤ 𝔠^(p^e)` for all large `e`, `g ∈ ⋂_n 𝔠^n`, which is `0` by Krull's intersection
theorem unless `𝔠 = A`. -/
theorem exists_frobRoot_span_singleton_eq_top [IsDomain A] [IsNoetherianRing A] {g : A}
    (hg : g ≠ 0) : ∃ e, hu.frobRoot e (Ideal.span {g}) = ⊤ := by
  obtain ⟨e₀, he₀⟩ := monotone_stabilizes_iff_noetherian.2
    (inferInstance : IsNoetherianRing A)
    ⟨fun e => hu.frobRoot e (Ideal.span {g}), hu.frobRoot_monotone_exp _⟩
  refine ⟨e₀, ?_⟩
  by_contra hne
  set 𝔠 := hu.frobRoot e₀ (Ideal.span {g})
  have hmem : ∀ n : ℕ, g ∈ 𝔠 ^ n := by
    intro n
    set e := max e₀ n
    have hn : n ≤ p ^ e :=
      (Nat.lt_pow_self hp.out.one_lt).le.trans (Nat.pow_le_pow_right hp.out.pos (le_max_right _ _))
    have h1 : Ideal.span {g} ≤ frobPow (p ^ e) (hu.frobRoot e (Ideal.span {g})) :=
      hu.le_frobPow_frobRoot e _
    have h2 : hu.frobRoot e (Ideal.span {g}) = 𝔠 := (he₀ e (le_max_left _ _)).symm
    rw [h2] at h1
    exact ((h1.trans (frobPow_le_pow _ _)).trans (Ideal.pow_le_pow_right hn))
      (Ideal.mem_span_singleton_self g)
  have h0 := Ideal.iInf_pow_eq_bot_of_isDomain 𝔠 hne
  have hg' : g ∈ ⨅ n : ℕ, 𝔠 ^ n := Submodule.mem_iInf _ |>.2 hmem
  rw [h0, Ideal.mem_bot] at hg'
  exact hg hg'

/-- Once `(g)^[1/p^k] = A`, also `(g)^[1/p^e] = A` for all `e ≥ k`. -/
theorem frobRoot_eq_top_of_le {I : Ideal A} {k e : ℕ} (hk : hu.frobRoot k I = ⊤) (h : k ≤ e) :
    hu.frobRoot e I = ⊤ :=
  top_le_iff.1 (hk ▸ hu.frobRoot_monotone_exp I h)

end IsPBasis

end Root

/-! ### Base change -/

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] [CharP A p] [CharP B p] (φ : A →+* B)
  {σ : Type*} [Fintype σ] [DecidableEq σ] {u : σ → A} (hu : IsPBasis p u)
  (hφu : IsPBasis p (φ ∘ u))

/-- `φ(J^[q]) ≤ (φ J)^[q]`. -/
theorem map_frobPow_le (q : ℕ) (J : Ideal A) : (frobPow q J).map φ ≤ frobPow q (J.map φ) := by
  rw [Ideal.map_le_iff_le_comap, frobPow_le_iff]
  intro f hf
  rw [Ideal.mem_comap, map_pow]
  exact pow_mem_frobPow (Ideal.mem_map_of_mem φ hf)

/-- **Frobenius roots commute with base change** along any `φ : A → B` for which `φ ∘ u` is a
`p`-basis of `B` (e.g. localizations `A → A_h`, the fraction field of a domain, ring
isomorphisms): `(I B)^[1/Q] = I^[1/Q] B`. -/
theorem IsPBasis.frobRoot_map (e : ℕ) (I : Ideal A) :
    hφu.frobRoot e (I.map φ) = (hu.frobRoot e I).map φ := by
  apply le_antisymm
  · rw [IsPBasis.frobRoot_le_iff]
    exact (Ideal.map_mono (hu.le_frobPow_frobRoot e I)).trans (map_frobPow_le φ _ _)
  · rw [Ideal.map_le_iff_le_comap]
    rintro _ ⟨f, hf, rfl⟩
    rw [Ideal.mem_comap, ← hu.traceIter_map φ hφu]
    exact hφu.traceIter_mem_frobRoot (Ideal.mem_map_of_mem φ hf)

end BaseChange

end EnvelopeProperty.Cartier
