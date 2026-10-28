import EnvelopeProperty.Cartier.PBasis

/-!
# Order estimates for Frobenius traces at a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `ϖ` and fraction field `F`. For `n : ℤ` we write
`OrdGE ϖ n f` for `f ∈ ϖ^n R ⊆ F`, i.e. `ord_R f ≥ n` (every `n` holds for `f = 0`).

If `y` is a `p`-basis of `F` and the Frobenius trace `Φ_y` satisfies the *one-step estimate*
`ord_R(Φ_y f) ≥ ⌊(ord_R f + a)/p⌋ - a`, then the semilinearity `Φ_y(g^p f) = g Φ_y f` and the
identity `⌊⌊x/p^e⌋/p⌋ = ⌊x/p^{e+1}⌋` give for all `e`
`ord_R(Φ_y^e f) ≥ ⌊(ord_R f + a)/p^e⌋ - a ≥ (ord_R f - (p^e - 1)(a + 1))/p^e`
(`ordGE_traceIter_of_step`, `sub_mul_succ_le_mul_ediv_sub`). This is the shape of the first display
in the proof of FHX Lemma 3.3 (`lem:divisorial-trace-estimate`) and of FHX (3.11)
(`eq:divisorial-trace-bound`), with `a = A_S(ord_E) - 1`.

The one-step estimate follows from a bound on a single lattice: if `Φ_y(ϖ^c R) ⊆ ϖ^d R` then
`ord_R(Φ_y f) ≥ ⌊(ord_R f - c)/p⌋ + d` (`ordGE_trace_of_bound`).

## Main definitions

* `EnvelopeProperty.Cartier.OrdGE ϖ n f`: `f ∈ ϖ^n R`.

## Main results

* `EnvelopeProperty.Cartier.ordGE_trace_of_bound`
* `EnvelopeProperty.Cartier.ordGE_traceIter_of_step`
* `EnvelopeProperty.Cartier.sub_mul_succ_le_mul_ediv_sub`
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

section OrdGE

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]

/-- `OrdGE ϖ n f` means `f ∈ ϖ^n R` inside `F`; for a uniformizer `ϖ` of a DVR `R` this is
`ord_R f ≥ n`. -/
def OrdGE (ϖ : R) (n : ℤ) (f : F) : Prop :=
  ∃ r : R, f = algebraMap R F ϖ ^ n * algebraMap R F r

variable {ϖ : R}

theorem ordGE_zero_iff {f : F} : OrdGE ϖ 0 f ↔ ∃ r : R, f = algebraMap R F r := by
  simp [OrdGE]

theorem ordGE_algebraMap (r : R) : OrdGE ϖ 0 (algebraMap R F r) :=
  ordGE_zero_iff.2 ⟨r, rfl⟩

theorem ordGE_zero (n : ℤ) : OrdGE ϖ n (0 : F) :=
  ⟨0, by simp⟩

theorem OrdGE.add {n : ℤ} {f g : F} (hf : OrdGE ϖ n f) (hg : OrdGE ϖ n g) :
    OrdGE ϖ n (f + g) := by
  obtain ⟨r, rfl⟩ := hf
  obtain ⟨s, rfl⟩ := hg
  exact ⟨r + s, by rw [map_add, mul_add]⟩

theorem OrdGE.neg {n : ℤ} {f : F} (hf : OrdGE ϖ n f) : OrdGE ϖ n (-f) := by
  obtain ⟨r, rfl⟩ := hf
  exact ⟨-r, by rw [map_neg, mul_neg]⟩

theorem OrdGE.sum {ι : Type*} (s : Finset ι) {n : ℤ} {f : ι → F}
    (hf : ∀ i ∈ s, OrdGE ϖ n (f i)) : OrdGE ϖ n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ordGE_zero n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable (hϖ : algebraMap R F ϖ ≠ 0)
include hϖ

theorem OrdGE.mul {m n : ℤ} {f g : F} (hf : OrdGE ϖ m f) (hg : OrdGE ϖ n g) :
    OrdGE ϖ (m + n) (f * g) := by
  obtain ⟨r, rfl⟩ := hf
  obtain ⟨s, rfl⟩ := hg
  exact ⟨r * s, by rw [zpow_add₀ hϖ, map_mul]; ring⟩

theorem OrdGE.algebraMap_mul {n : ℤ} {f : F} (hf : OrdGE ϖ n f) (r : R) :
    OrdGE ϖ n (algebraMap R F r * f) := by
  simpa using (ordGE_algebraMap r).mul hϖ hf

omit hϖ in
theorem ordGE_zpow (n : ℤ) : OrdGE ϖ n (algebraMap R F ϖ ^ n) :=
  ⟨1, by simp⟩

theorem OrdGE.zpow_mul {n : ℤ} {f : F} (hf : OrdGE ϖ n f) (m : ℤ) :
    OrdGE ϖ (m + n) (algebraMap R F ϖ ^ m * f) :=
  (ordGE_zpow m).mul hϖ hf

theorem OrdGE.mono {m n : ℤ} {f : F} (hf : OrdGE ϖ n f) (h : m ≤ n) : OrdGE ϖ m f := by
  obtain ⟨r, rfl⟩ := hf
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  refine ⟨ϖ ^ k * r, ?_⟩
  rw [map_mul, map_pow, ← zpow_natCast, ← hk, ← mul_assoc, ← zpow_add₀ hϖ, add_sub_cancel]

/-- `f ∈ ϖ^n R` iff `ϖ^{-n} f ∈ R`. -/
theorem ordGE_iff_zpow_neg_mul {n : ℤ} {f : F} :
    OrdGE ϖ n f ↔ OrdGE ϖ 0 (algebraMap R F ϖ ^ (-n) * f) := by
  constructor
  · intro hf
    simpa using hf.zpow_mul hϖ (-n)
  · intro hf
    have := hf.zpow_mul hϖ n
    rwa [← mul_assoc, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, one_mul, add_zero] at this

end OrdGE

section DVR

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
  [IsFractionRing R F] {ϖ : R}

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem algebraMap_uniformizer_ne_zero (hϖ : Irreducible ϖ) : algebraMap R F ϖ ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hϖ.ne_zero

/-- Every element of the fraction field has some order bound. -/
theorem exists_ordGE (hϖ : Irreducible ϖ) (f : F) : ∃ n : ℤ, OrdGE ϖ n f := by
  by_cases hf : f = 0
  · exact ⟨0, hf ▸ ordGE_zero 0⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hf
  exact ⟨n, (u : R), by rw [Units.smul_def, Algebra.smul_def, mul_comm]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- For `u` a unit, `u ϖ^m ∈ ϖ^n R` iff `n ≤ m`. -/
theorem ordGE_unit_mul_zpow_iff (hϖ : Irreducible ϖ) (u : Rˣ) {m n : ℤ} :
    OrdGE ϖ n (algebraMap R F u * algebraMap R F ϖ ^ m) ↔ n ≤ m := by
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := F) hϖ
  constructor
  · rintro ⟨r, hr⟩
    by_contra hlt
    push Not at hlt
    -- `u = ϖ^{n-m} r` with `n - m ≥ 1`, so `ϖ ∣ u`
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hlt.le)
    have hk1 : 1 ≤ k := by omega
    have hu : algebraMap R F (u : R) = algebraMap R F (ϖ ^ k * r) := by
      rw [map_mul, map_pow, ← zpow_natCast, ← hk]
      have := congrArg (· * algebraMap R F ϖ ^ (-m)) hr
      simp only [mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one] at this
      rw [this]
      rw [mul_comm (algebraMap R F ϖ ^ n), mul_assoc, ← zpow_add₀ hϖ0, sub_eq_add_neg,
        add_comm (-m), mul_comm]
    have hu' := IsFractionRing.injective R F hu
    have : ϖ ∣ (u : R) := ⟨ϖ ^ (k - 1) * r, by
      rw [hu', ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1]⟩
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  · intro h
    exact ((ordGE_algebraMap (u : R)).mul hϖ0 (ordGE_zpow m)).mono hϖ0 (by simpa using h)

/-- `OrdGE ϖ n f` means `ord_R f ≥ n`: whenever `f = u ϖ^m` with `u` a unit, `n ≤ m`
(and `f = 0` satisfies every `OrdGE`). -/
theorem ordGE_iff (hϖ : Irreducible ϖ) {n : ℤ} {f : F} :
    OrdGE ϖ n f ↔ ∀ (m : ℤ) (u : Rˣ), f = algebraMap R F u * algebraMap R F ϖ ^ m → n ≤ m := by
  constructor
  · rintro hf m u rfl
    exact (ordGE_unit_mul_zpow_iff hϖ u).1 hf
  · intro h
    by_cases hf : f = 0
    · exact hf ▸ ordGE_zero n
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hf
    rw [Units.smul_def, Algebra.smul_def] at h ⊢
    exact (ordGE_unit_mul_zpow_iff hϖ u).2 (h m u rfl)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- On `R`, `OrdGE ϖ n` is divisibility by `ϖ^n`. -/
theorem ordGE_algebraMap_iff_dvd (n : ℕ) (r : R) :
    OrdGE ϖ n (algebraMap R F r) ↔ ϖ ^ n ∣ r := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, IsFractionRing.injective R F ?_⟩
    rw [hs, map_mul, map_pow, zpow_natCast]
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [map_mul, map_pow, zpow_natCast]⟩

/-- On `R`, `OrdGE` is the order of Mathlib's additive valuation `IsDiscreteValuationRing.addVal`. -/
theorem ordGE_algebraMap_iff_addVal (hϖ : Irreducible ϖ) (n : ℕ) (r : R) :
    OrdGE ϖ n (algebraMap R F r) ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal R r := by
  rw [ordGE_algebraMap_iff_dvd, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one]

end DVR

/-! ### Trace estimates -/

section Trace

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] {ϖ : R}
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
  {σ : Type*} [Fintype σ] [DecidableEq σ] {y : σ → F} (hy : IsPBasis p y)

include hy

/-- From a bound on one lattice to all lattices: if `Φ_y(ϖ^c R) ⊆ ϖ^d R` then
`ord(Φ_y f) ≥ ⌊(ord f - c)/p⌋ + d`. -/
theorem ordGE_trace_of_bound (hϖ : algebraMap R F ϖ ≠ 0) {c d : ℤ}
    (h : ∀ f : F, OrdGE ϖ c f → OrdGE ϖ d (hy.trace f)) {n : ℤ} {f : F} (hf : OrdGE ϖ n f) :
    OrdGE ϖ ((n - c) / p + d) (hy.trace f) := by
  set ℓ := (n - c) / p
  have hpℓ : (p : ℤ) * ℓ ≤ n - c := Int.mul_ediv_self_le (by exact_mod_cast hp.out.ne_zero)
  -- `f = (ϖ^ℓ)^p * f'` with `f' ∈ ϖ^c R`
  set f' := algebraMap R F ϖ ^ (-(p * ℓ)) * f
  have hf' : OrdGE ϖ c f' := (hf.zpow_mul hϖ (-(p * ℓ))).mono hϖ (by omega)
  have hff' : f = (algebraMap R F ϖ ^ ℓ) ^ p * f' := by
    rw [← zpow_natCast, ← zpow_mul, ← mul_assoc, ← zpow_add₀ hϖ, mul_comm ℓ, add_neg_cancel,
      zpow_zero, one_mul]
  rw [hff', hy.trace_pow_mul, add_comm]
  exact (h f' hf').zpow_mul hϖ ℓ |>.mono hϖ (by omega)

/-- Iterating the one-step estimate `ord(Φ_y f) ≥ ⌊(ord f + a)/p⌋ - a`:
`ord(Φ_y^e f) ≥ ⌊(ord f + a)/p^e⌋ - a`. -/
theorem ordGE_traceIter_of_step {a : ℤ}
    (h : ∀ (n : ℤ) (f : F), OrdGE ϖ n f → OrdGE ϖ ((n + a) / p - a) (hy.trace f))
    (e : ℕ) {n : ℤ} {f : F} (hf : OrdGE ϖ n f) :
    OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a) (hy.traceIter e f) := by
  induction e with
  | zero => simpa using hf
  | succ e ih =>
    rw [hy.traceIter_succ]
    have := h _ _ ih
    rwa [sub_add_cancel, Int.ediv_ediv_of_nonneg (by positivity), ← Nat.cast_mul, ← pow_succ]
      at this

end Trace

/-- The arithmetic step from the floor bound to FHX (3.11):
`n - (q - 1)(a + 1) ≤ q (⌊(n + a)/q⌋ - a)`, i.e. `⌊(n+a)/q⌋ - a ≥ (n - (q-1)(a+1))/q`. -/
theorem sub_mul_succ_le_mul_ediv_sub {q : ℤ} (hq : 0 < q) (n a : ℤ) :
    n - (q - 1) * (a + 1) ≤ q * ((n + a) / q - a) := by
  have h1 := Int.emod_add_mul_ediv (n + a) q
  have h2 := Int.emod_lt_of_pos (n + a) hq
  nlinarith

end EnvelopeProperty.Cartier
