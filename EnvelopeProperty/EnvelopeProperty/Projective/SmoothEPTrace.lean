/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.TestIdealBridge
import EnvelopeProperty.Projective.Divisorial
import EnvelopeProperty.Cartier.Discrepancy

/-!
# Asymptotic test ideals at divisorial points of `(ℙⁿ)^an`

Let `k` be a perfect field of characteristic `p > 0`. This file provides step (d) of the assembly
of Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Theorem 3.1
for `ℙⁿ` (`thm:smooth-EP`; blueprint `thm:pn-ep`, `rmk:bj-pn-ep-assembly`): the valuative bound
for asymptotic test ideals at the divisorial points of `def:pn-div` (`ProjBerk.IsDivisorial`).

The test ideals of `EnvelopeProperty.TestIdeal` live in the cone ring
`k[x₀, …, xₙ, t] = MvPolynomial (Option (Fin (n + 1))) k`, whereas a divisorial point comes with a
discrete valuation ring `R'` of `k(x, t) = FractionRing R[t]`, where
`R[t] = (MvPolynomial (Fin (n + 1)) k)[X]` (`BirationalDVR`). Rather than transporting `R'`, we
give `FractionRing R[t]` the structure of a fraction field of `k[x, t]` through the isomorphism
`ProjBerk.coneEquiv` (so the variables of the cone ring are the images of `t` and the `xᵢ`, and
the hypothesis `y' = x` of the trace estimate holds by definition), and apply the Frobenius trace
estimate FHX Lemma 3.3 (`lem:divisorial-trace-estimate`, blueprint `lem:pn-divisorial-trace`,
`Cartier.exists_logDiscrepancy_polynomial`).

## Main results

* `ProjBerk.exists_le_ord_frobTrace`: for `R' : BirationalDVR k R[t]` there is `a ∈ ℕ`
  (`a = ord_{R'}(dx/du)`, so `A(ord_{R'}) = 1 + a`) with
  `ord_{R'}(Φ_e f) ≥ ⌊(ord_{R'} f + a)/p^e⌋ - a` for all `e` and all `f ∈ k[x, t]`, where `Φ_e` is
  the Frobenius trace of the test-ideal API and `ord_{R'}` is computed on `coneEquiv⁻¹ f`.
* `ProjBerk.exists_phiIdeal_asymptoticTestIdeal_le`: for a graded sequence `J_•` of nonzero ideals
  of `k[x, t]` and a divisorial point `v`, there is `A ≥ 0` such that for every `m > 0` there is
  `q > 0` with `φ_{B_m}(v) ≤ (m/q) φ_{J_q}(v) + A`, where `B_m = τ(J_•^m)` is the asymptotic test
  ideal (`asymptoticTestIdeal`). This is the inequality `ord_{R'}(B_m) ≥ (m/q) ord_{R'}(J_q) - A` of
  step (d), multiplied by the constant `-c` of `v`; here `A = c (1 + a)`.

The proof of the second result writes `B_m = Φ_e(J_q^N)` with `N = ⌈m p^e/q⌉` for `q` divisible
enough and `e ≫ 0` (`exists_asymptoticTestIdeal_eq`, `exists_testIdeal_eq`); for `G = Φ_e(F)`,
`F ∈ J_q^N`, the trace estimate and `sub_mul_succ_le_mul_ediv_sub` give
`log|G|_{σ(v)} ≤ log|F|_{σ(v)}/p^e + c(1 + a) ≤ (N/p^e) φ_{J_q}(v) + c(1 + a)`, and the rounding
`N ≥ m p^e/q` is absorbed since `φ_{J_q} ≤ 0` (`phiIdeal_le_zero`).
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

section Trace

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- **The Frobenius trace estimate on the cone ring** (FHX Lemma 3.3, `lem:pn-divisorial-trace`,
transported along `coneEquiv`): for a discrete valuation ring `k[x, t] ⊆ R' ⊆ k(x, t)`, essentially
of finite type over `k`, there is `a ∈ ℕ` such that `ord_{R'} f ≥ N` and `ord_{R'}(Φ_e f) = M`
imply `⌊(N + a)/p^e⌋ - a ≤ M`. -/
theorem exists_le_ord_frobTrace (R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) :
    ∃ a : ℕ, ∀ (e : ℕ) (f : MvPolynomial (Option (Fin (n + 1))) k) (N M : ℕ),
      (N : ℕ∞) ≤ R'.ord ((coneEquiv k n).symm f) →
      R'.ord ((coneEquiv k n).symm (frobTrace p e f)) = M →
      ((N : ℤ) + a) / ((p ^ e : ℕ) : ℤ) - a ≤ M := by
  classical
  let B := (MvPolynomial (Fin (n + 1)) k)[X]
  let F := FractionRing B
  let : Algebra (MvPolynomial (Option (Fin (n + 1))) k) F :=
    ((algebraMap B F).comp (coneEquiv k n).symm.toRingEquiv.toRingHom).toAlgebra
  have : IsFractionRing (MvPolynomial (Option (Fin (n + 1))) k) F :=
    IsFractionRing.of_ringEquiv_left (coneEquiv k n).symm.toRingEquiv (fun _ => rfl)
  have : CharP R'.ring p := charP_of_injective_algebraMap (algebraMap k R'.ring).injective p
  have : IsFractionRing R'.ring F := R'.isFractionRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R'.ring
  have hmap : ∀ f : MvPolynomial (Option (Fin (n + 1))) k,
      algebraMap (MvPolynomial (Option (Fin (n + 1))) k) F f =
        algebraMap R'.ring F (R'.toRing ((coneEquiv k n).symm f)) := fun _ => rfl
  obtain ⟨u, hu, a, w, -, h⟩ := Cartier.exists_logDiscrepancy_polynomial (p := p) (k := k)
    (F := F) (R := R'.ring)
    (y' := fun i => R'.toRing ((coneEquiv k n).symm (MvPolynomial.X i))) (fun i => rfl) hϖ
  refine ⟨a, fun e f N M hN hM => ?_⟩
  have hf : Cartier.OrdGE ϖ (N : ℤ) (algebraMap (MvPolynomial (Option (Fin (n + 1))) k) F f) := by
    rw [hmap]
    exact (Cartier.ordGE_algebraMap_iff_addVal hϖ N _).2 hN
  have h2 := h e N f hf
  rw [← frobTrace_apply_eq_polyTrace, hmap] at h2
  set z : ℤ := ((N : ℤ) + a) / ((p ^ e : ℕ) : ℤ) - a
  rcases le_or_gt z 0 with hz | hz
  · exact hz.trans (Nat.cast_nonneg M)
  · have hz' : z = (z.toNat : ℤ) := (Int.toNat_of_nonneg hz.le).symm
    rw [hz'] at h2 ⊢
    have h3 := (Cartier.ordGE_algebraMap_iff_addVal hϖ z.toNat _).1 h2
    change (z.toNat : ℕ∞) ≤ R'.ord _ at h3
    rw [hM] at h3
    exact_mod_cast h3

end Trace

/-- `((N : ℕ∞) : EReal) = ((N : ℝ) : EReal)`. -/
theorem enat_coe_natCast_eq (N : ℕ) : ((N : ℕ∞) : EReal) = ((N : ℝ) : EReal) := by
  norm_cast

/-- At a divisorial point, `log|g|_{σ(v)} = -c N` when `ord_{R'}(g) = N`. -/
theorem logAbs_gaussExt_eq_of_ord_eq {v : ProjBerk k n}
    {R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]} {c : ℚ}
    (hlog : ∀ g : (MvPolynomial (Fin (n + 1)) k)[X],
      Berk.logAbs g (gaussExt v) = -((c : ℝ) : EReal) * (R'.ord g : EReal))
    {g : (MvPolynomial (Fin (n + 1)) k)[X]} {N : ℕ} (hN : R'.ord g = N) :
    Berk.logAbs g (gaussExt v) = ((-((c : ℝ) * N) : ℝ) : EReal) := by
  rw [hlog, hN, enat_coe_natCast_eq, ← EReal.coe_neg, ← EReal.coe_mul, neg_mul]

/-- A nonzero element has finite order. -/
theorem exists_ord_eq_of_ne_zero (R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X])
    {g : (MvPolynomial (Fin (n + 1)) k)[X]} (hg : g ≠ 0) : ∃ N : ℕ, R'.ord g = N := by
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 (mt R'.ord_eq_top_iff.1 hg)
  exact ⟨N, hN.symm⟩

section Asymptotic

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- **Asymptotic test ideals at divisorial points** (`rmk:bj-pn-ep-assembly`, step (d)): for a
graded sequence `J_•` of nonzero ideals of `k[x₀, …, xₙ, t]` and a divisorial point `v` there is
`A ≥ 0` such that for every `m > 0` there is `q > 0` with
`φ_{B_m}(v) ≤ (m/q) φ_{J_q}(v) + A`, `B_m = τ(J_•^m)`; ideals of `k[x, t]` are evaluated in
`R[t]` through `coneEquiv`. -/
theorem exists_phiIdeal_asymptoticTestIdeal_le
    {J : ℕ → Ideal (MvPolynomial (Option (Fin (n + 1))) k)}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (hne : ∀ q, 0 < q → J q ≠ ⊥)
    {v : ProjBerk k n} (hv : v.IsDivisorial) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
      phiIdeal ((asymptoticTestIdeal p J m).comap (coneEquiv k n)) v ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal ((J q).comap (coneEquiv k n)) v + (A : EReal) := by
  obtain ⟨R', c, hc, hlog⟩ := hv
  obtain ⟨a, ha⟩ := exists_le_ord_frobTrace p R'
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨c * (a + 1), by positivity, fun m hm => ?_⟩
  obtain ⟨q, hq, hBq⟩ := exists_asymptoticTestIdeal_eq p hJ hne m
  refine ⟨q, hq, ?_⟩
  obtain ⟨e, he⟩ := exists_testIdeal_eq p (J q) ((m : ℚ) / q)
  rw [hBq q hq dvd_rfl, he e le_rfl, phiIdeal_comap_coneEquiv]
  set N := ⌈(m : ℚ) / q * (p : ℚ) ^ e⌉₊ with hN
  set L := phiIdeal ((J q).comap (coneEquiv k n)) v with hL
  have hL0 : L ≤ 0 := phiIdeal_le_zero _ v
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hNpos : 0 < N := Nat.ceil_pos.2 (by positivity)
  refine iSup₂_le fun G hG => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_frobRoot p).1 hG
  by_cases hG0 : frobTrace p e g = 0
  · rw [hG0, map_zero, Berk.logAbs_zero]
    exact bot_le
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hG0 (map_zero _)
  obtain ⟨N', hN'⟩ := exists_ord_eq_of_ne_zero R'
    ((map_ne_zero_iff _ (coneEquiv k n).symm.injective).2 hg0)
  obtain ⟨M, hM⟩ := exists_ord_eq_of_ne_zero R'
    ((map_ne_zero_iff _ (coneEquiv k n).symm.injective).2 hG0)
  have htr := ha e g N' M hN'.ge hM
  have h1 : Berk.logAbs ((coneEquiv k n).symm g) (gaussExt v) ≤ (N : EReal) * L := by
    rw [hL, ← phiIdeal_pow, ← comap_coneEquiv_pow]
    exact le_phiIdeal _ v (Ideal.mem_comap.2 (by rw [AlgEquiv.apply_symm_apply]; exact hg))
  rw [logAbs_gaussExt_eq_of_ord_eq hlog hN'] at h1
  rw [logAbs_gaussExt_eq_of_ord_eq hlog hM]
  have hNcast : (N : EReal) = ((N : ℝ) : EReal) := by norm_cast
  have hLbot : L ≠ ⊥ := by
    intro hbot
    rw [hbot, hNcast, EReal.coe_mul_bot_of_pos (by exact_mod_cast hNpos), le_bot_iff] at h1
    exact EReal.coe_ne_bot _ h1
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hL0
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, L = ℓ := ⟨L.toReal, (EReal.coe_toReal hLtop hLbot).symm⟩
  rw [hℓ, hNcast, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
  rw [hℓ, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hℓ0 : ℓ ≤ 0 := by
    rw [hℓ] at hL0
    exact_mod_cast hL0
  -- the trace estimate in real numbers: `N' - (p^e - 1)(a + 1) ≤ p^e M`
  have hQ : (0 : ℤ) < ((p ^ e : ℕ) : ℤ) := by exact_mod_cast pow_pos (Fact.out : p.Prime).pos e
  have hint : (N' : ℤ) - (((p ^ e : ℕ) : ℤ) - 1) * ((a : ℤ) + 1) ≤ ((p ^ e : ℕ) : ℤ) * M :=
    (Cartier.sub_mul_succ_le_mul_ediv_sub hQ N' a).trans (mul_le_mul_of_nonneg_left htr hQ.le)
  have hreal : (N' : ℝ) - ((p : ℝ) ^ e - 1) * ((a : ℝ) + 1) ≤ (p : ℝ) ^ e * M := by
    exact_mod_cast hint
  have hceil : (m : ℝ) / q * (p : ℝ) ^ e ≤ N := by
    have := Nat.le_ceil ((m : ℚ) / q * (p : ℚ) ^ e)
    rw [← hN] at this
    have h2 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h2
    exact h2
  have hQr : (0 : ℝ) < (p : ℝ) ^ e := by exact_mod_cast pow_pos (Fact.out : p.Prime).pos e
  have hNℓ : (N : ℝ) * ℓ ≤ (m : ℝ) / q * (p : ℝ) ^ e * ℓ :=
    mul_le_mul_of_nonpos_right hceil hℓ0
  have hcr := mul_le_mul_of_nonneg_left hreal hc'.le
  have ha0 : (0 : ℝ) ≤ c * (a + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hQr
  nlinarith

end Asymptotic

end ProjBerk

end EnvelopeProperty
