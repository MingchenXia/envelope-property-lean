/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeTest
import EnvelopeProperty.Cartier.Discrepancy

/-!
# The valuative bound for the asymptotic test ideals of the cone

Let `k` be a perfect field of characteristic `p`, `X = V(I) ⊆ ℙᴹ` with cone ring `T = S[t]`,
`K = Frac T`, `D : X.ConeTraceData p` the chart data of the punctured cone, and `B_m`
(`ConeTraceData.testSeq`) the asymptotic test ideals of a graded sequence `J_•` of nonzero ideals
of `T` (blueprint `def:sg-test-X`, chapter `smooth-general.tex`). This file proves the valuative
bound **`prop:sg-valuative-bound`**, the form of Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Lemma 3.3 (`lem:divisorial-trace-estimate`,
eq. `eq:divisorial-test-bound`) used in the proof of their Theorem 3.1 on a smooth `X`:

for a discrete valuation ring `T ⊆ R' ⊆ K`, essentially of finite type over `k`, in which some
`x̄ⱼ` is a unit, there is `A ≥ 0` such that for every graded sequence `J_•` and every `m`,
`ord_{R'}(B_m) ≥ (m/r) ord_{R'}(J_r) - A` for all sufficiently divisible `r`.

The proof follows the blueprint: by the trace estimate (`lem:sg-trace-estimate`,
`Cartier.exists_logDiscrepancy`) for `R'` and the homogeneous `p`-basis `z ⊆ T ⊆ R'` there is `a`
with `ord(Φ^e_z f) ≥ ⌊(ord f + a)/p^e⌋ - a`; with `b ≥ ord_{R'}(ι_c)` for all `c` (so
`ord_{R'}(μ_c) ≥ -b`, as `μ_c ι_c = s_c^{2N₁} ∈ T`), every element of
`Θ = Φ^e_z(J_r^N M₀) 𝔍₀` has order `≥ ⌊(N ord(J_r) - b + a)/p^e⌋ - a ≥ (m/r) ord(J_r) - A`,
`A = 1 + a + b` (`ConeTraceData.ordGE_of_mem_thetaK`), and `B_m ⊆ Θ^sat` with `ord(x̄ⱼ) = 0`.

## Main results

* `ConeTraceData.ordGE_of_mem_thetaK`: the order bound on `Φ^e_z(𝔞^N M₀) 𝔍₀`, for any subring
  `R ⊆ K` containing `T` and any `ϖ ∈ R` (in terms of `Cartier.OrdGE`).
* **`ConeTraceData.exists_ord_testSeq_ge`** (`prop:sg-valuative-bound`): for
  `R' : BirationalDVR k X.ConeRing` with `ord_{R'}(x̄ⱼ) = 0` there is `A ∈ ℕ` such that for every
  graded sequence `J_•` of nonzero ideals and every `m` there is `r₀ > 0` with
  `(m/r) o - A ≤ ord_{R'}(f)` for all `r > 0` divisible by `r₀`, all lower bounds `o` of
  `ord_{R'}` on `J_r`, and all `f ∈ B_m`.
* **`ConeTraceData.exists_phiIdeal_testSeq_le`** (`prop:sg-valuative-bound` at divisorial points,
  the form used in step (c) of `thm:sg-ep-charp`): for a divisorial point `v ∈ X^an`
  (`ProjSubvariety.IsDivisorial`, `def:sg-div`) there is `A ≥ 0` such that for every graded
  sequence `J_•` of nonzero ideals and every `m` there is `r₀ > 0` with
  `φ_{B_m}(v) ≤ (m/r) φ_{J_r}(v) + A` for every `r > 0` divisible by `r₀`.

## Deviations from the blueprint

* The order of an ideal is not formalized: the bound is stated for every lower bound `o` of
  `ord_{R'}` on `J_r` and every `f ∈ B_m` (`ord_{R'}(f) = ν` with `ν ∈ ℕ`, i.e. `f ≠ 0`).
* The constant is `A = 1 + a + b` with `b` any common bound `ord_{R'}(ι_c) ≤ b`, as in the
  blueprint; at a divisorial point with constant `c` the additive constant is `c A`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

open ProjBerk (phiIdeal gaussExt)

universe u

namespace ProjSubvariety

namespace ConeTraceData

open Cartier IsDiscreteValuationRing

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M} {p : ℕ} [hp : Fact p.Prime]
  [CharP k p] (D : X.ConeTraceData p)

/-! ### Orders on `Θ` -/

section OrdGE

variable {R : Type*} [CommRing R] [Algebra R (FractionRing X.ConeRing)] {ϖ : R}
  (hϖ : algebraMap R (FractionRing X.ConeRing) ϖ ≠ 0)
  (hT : ∀ t : X.ConeRing, OrdGE ϖ 0 (algebraMap X.ConeRing (FractionRing X.ConeRing) t))
include hϖ hT

/-- `ord(𝔞^N) ≥ N o` if `ord(𝔞) ≥ o`. -/
theorem ordGE_of_mem_pow {𝔞 : Ideal X.ConeRing} {o : ℕ}
    (ho : ∀ g ∈ 𝔞, OrdGE ϖ o (algebraMap X.ConeRing (FractionRing X.ConeRing) g)) :
    ∀ (N : ℕ), ∀ g ∈ 𝔞 ^ N,
      OrdGE ϖ ((N * o : ℕ) : ℤ) (algebraMap X.ConeRing (FractionRing X.ConeRing) g)
  | 0 => fun g _ => by simpa using hT g
  | N + 1 => fun g hg => by
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, show (((N + 1) * o : ℕ) : ℤ) = ((N * o : ℕ) : ℤ) + (o : ℤ) by push_cast; ring]
      exact (ordGE_of_mem_pow ho N x hx).mul hϖ (ho y hy)
    · rw [map_add]
      exact hx.add hy

/-- Elements of `𝔞^N M₀` have order `≥ N o - b` if `ord(𝔞) ≥ o` and `ord(μ_c) ≥ -b`. -/
theorem ordGE_of_mem_smul_M0 {b : ℕ} (hb : ∀ c, OrdGE ϖ (-(b : ℤ)) (D.mu c)) {𝔞 : Ideal X.ConeRing}
    {o : ℕ} (ho : ∀ g ∈ 𝔞, OrdGE ϖ o (algebraMap X.ConeRing (FractionRing X.ConeRing) g))
    {N : ℕ} {x : FractionRing X.ConeRing} (hx : x ∈ 𝔞 ^ N • D.M0) :
    OrdGE ϖ ((N * o : ℕ) - (b : ℤ)) x := by
  have hM0 : ∀ y ∈ D.M0, OrdGE ϖ (-(b : ℤ)) y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y h =>
      obtain ⟨c, rfl⟩ := h
      exact hb c
    | zero => exact ordGE_zero _
    | add y y' _ _ hy hy' => exact hy.add hy'
    | smul t y _ hy =>
      rw [Algebra.smul_def]
      simpa using (hT t).mul hϖ hy
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => hx.add hy)
  rw [Algebra.smul_def, sub_eq_add_neg]
  exact (ordGE_of_mem_pow hϖ hT ho N r hr).mul hϖ (hM0 n hn)

/-- **The order bound on `Θ`** (`prop:sg-valuative-bound`): if `Φ^e_z` satisfies the trace
estimate `ord(Φ^e_z f) ≥ ⌊(ord f + a)/p^e⌋ - a`, `ord(μ_c) ≥ -b` for all `c` and `ord(𝔞) ≥ o`,
then every element of `Φ^e_z(𝔞^N M₀) 𝔍₀` has order `≥ ⌊(N o - b + a)/p^e⌋ - a`. -/
theorem ordGE_of_mem_thetaK {a : ℕ}
    (htr : ∀ (e : ℕ) (n : ℤ) (f : FractionRing X.ConeRing), OrdGE ϖ n f →
      OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a) (D.isPBasis_z.traceIter e f))
    {b : ℕ} (hb : ∀ c, OrdGE ϖ (-(b : ℤ)) (D.mu c)) {𝔞 : Ideal X.ConeRing} {o : ℕ}
    (ho : ∀ g ∈ 𝔞, OrdGE ϖ o (algebraMap X.ConeRing (FractionRing X.ConeRing) g)) {e N : ℕ}
    {y : FractionRing X.ConeRing} (hy : y ∈ D.thetaK e N 𝔞) :
    OrdGE ϖ (((N * o : ℕ) - (b : ℤ) + a) / (p ^ e : ℕ) - a) y := by
  refine Submodule.mul_induction_on hy (fun m hm n hn => ?_) (fun x y hx hy => hx.add hy)
  obtain ⟨x, hx, rfl⟩ := hm
  obtain ⟨j, -, rfl⟩ := Submodule.mem_map.1 hn
  simpa using (htr e _ x (D.ordGE_of_mem_smul_M0 hϖ hT hb ho hx)).mul hϖ (hT j)

end OrdGE

/-! ### The valuative bound -/

/-- The real arithmetic of `prop:sg-valuative-bound`: if `N ≥ (m/r) Q` then
`⌊(N o - b + a)/Q⌋ - a ≥ (m/r) o - (1 + a + b)`. -/
theorem le_ediv_sub_of_le_mul {m r o a b Q N : ℕ} (hQ : 0 < Q)
    (hN : (m : ℝ) / r * Q ≤ N) :
    (m : ℝ) / r * o - ((1 + a + b : ℕ) : ℝ) ≤
      ((((N * o : ℕ) - (b : ℤ) + a) / (Q : ℤ) - a : ℤ) : ℝ) := by
  set x : ℤ := (N * o : ℕ) - (b : ℤ) + a
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have h1 := Int.lt_ediv_add_one_mul_self x hQ'
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h2 : (x : ℝ) < ((x / (Q : ℤ) : ℤ) + 1) * Q := by exact_mod_cast h1
  have h3 : (x : ℝ) / Q - 1 < ((x / (Q : ℤ) : ℤ) : ℝ) := by
    rw [div_sub_one hQr.ne', div_lt_iff₀ hQr]
    linarith
  have h4 : (m : ℝ) / r * o ≤ (N * o : ℝ) / Q := by
    rw [le_div_iff₀ hQr]
    have := mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg o)
    linarith
  have h5 : (x : ℝ) / Q = (N * o : ℝ) / Q + ((a : ℝ) - b) / Q := by
    simp only [x]
    push_cast
    ring
  have h6 : -(b : ℝ) ≤ ((a : ℝ) - b) / Q := by
    rw [le_div_iff₀ hQr]
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  push_cast
  linarith

/-- If `ord_{R'}(g) = ν` and `ord(g) ≥ n` in the sense of `OrdGE`, then `n ≤ ν`. -/
theorem le_of_ordGE_of_ord_eq {R' : BirationalDVR k X.ConeRing} {ϖ : R'.ring} (hϖ : Irreducible ϖ)
    {g : X.ConeRing} {ν : ℕ} (hg : R'.ord g = ν) {n : ℤ}
    (hn : OrdGE ϖ n (algebraMap X.ConeRing (FractionRing X.ConeRing) g)) : n ≤ ν := by
  have : IsFractionRing R'.ring (FractionRing X.ConeRing) := R'.isFractionRing
  have hg0 : R'.toRing g ≠ 0 := by
    intro h0
    rw [BirationalDVR.ord, h0, addVal_zero] at hg
    exact ENat.top_ne_natCast ν hg
  obtain ⟨n', w, hw⟩ := eq_unit_mul_pow_irreducible hg0 hϖ
  have hn' : n' = ν := by
    have h1 := addVal_def _ w hϖ n' hw
    rw [← BirationalDVR.ord, hg] at h1
    exact_mod_cast h1.symm
  subst hn'
  have h2 : algebraMap X.ConeRing (FractionRing X.ConeRing) g =
      algebraMap R'.ring (FractionRing X.ConeRing) w *
        algebraMap R'.ring (FractionRing X.ConeRing) ϖ ^ (n' : ℤ) := by
    change algebraMap R'.ring (FractionRing X.ConeRing) (R'.toRing g) = _
    rw [hw, map_mul, map_pow, zpow_natCast]
  rw [h2] at hn
  exact (ordGE_unit_mul_zpow_iff hϖ w).1 hn

/-- `ord_{R'}(μ_c) ≥ -b` for a common bound `b` of the `ord_{R'}(ι_c)`: `μ_c ι_c = s_c^{2N₁}`. -/
theorem exists_ordGE_mu (R' : BirationalDVR k X.ConeRing) {ϖ : R'.ring} (hϖ : Irreducible ϖ) :
    ∃ b : ℕ, ∀ c, OrdGE ϖ (-(b : ℤ)) (D.mu c) := by
  have : IsFractionRing R'.ring (FractionRing X.ConeRing) := R'.isFractionRing
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := FractionRing X.ConeRing) hϖ
  have H : ∀ c, ∃ n : ℕ, OrdGE ϖ (-(n : ℤ)) (D.mu c) := by
    intro c
    have hι : algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) ≠ 0 := by
      rw [D.algebraMap_iota]
      exact mul_ne_zero (pow_ne_zero _ (D.sK_ne_zero c)) (D.jac_ne_zero c)
    have hι0 : R'.toRing (D.iota c) ≠ 0 := fun h0 =>
      hι (by rw [← BirationalDVR.coe_toRing R' (D.iota c), h0, ZeroMemClass.coe_zero])
    obtain ⟨n, w, hw⟩ := eq_unit_mul_pow_irreducible hι0 hϖ
    refine ⟨n, ((w⁻¹ : R'.ringˣ) : R'.ring) * R'.toRing ((D.chart c).s ^ (2 * D.N1)), ?_⟩
    have h1 : algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) =
        algebraMap R'.ring (FractionRing X.ConeRing) w *
          algebraMap R'.ring (FractionRing X.ConeRing) ϖ ^ n := by
      change algebraMap R'.ring (FractionRing X.ConeRing) (R'.toRing (D.iota c)) = _
      rw [hw, map_mul, map_pow]
    have h2 : D.mu c = D.sK c ^ (2 * D.N1) /
        algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) := by
      rw [eq_div_iff hι, D.mu_mul_iota]
    have hw0 : algebraMap R'.ring (FractionRing X.ConeRing) w ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R'.ring (FractionRing X.ConeRing))).2
        w.ne_zero
    have h3 : algebraMap R'.ring (FractionRing X.ConeRing) ((w⁻¹ : R'.ringˣ) : R'.ring) *
        algebraMap R'.ring (FractionRing X.ConeRing) w = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h4 : algebraMap R'.ring (FractionRing X.ConeRing)
        (R'.toRing ((D.chart c).s ^ (2 * D.N1))) = D.sK c ^ (2 * D.N1) := by
      change algebraMap X.ConeRing (FractionRing X.ConeRing) _ = _
      rw [map_pow]
    rw [h2, h1, map_mul, h4, zpow_neg, zpow_natCast]
    field_simp
    rw [mul_assoc, mul_comm (algebraMap R'.ring (FractionRing X.ConeRing) (w : R'.ring)), h3,
      mul_one]
  choose n hn using H
  refine ⟨Finset.univ.sup n, fun c => (hn c).mono hϖ0 ?_⟩
  have := Finset.le_sup (f := n) (Finset.mem_univ c)
  omega

variable [PerfectRing k p]

/-- **`prop:sg-valuative-bound`**: let `T ⊆ R' ⊆ K` be a discrete valuation ring essentially of
finite type over `k` in which `x̄ⱼ` is a unit. There is `A ∈ ℕ` such that for every graded
sequence `J_•` of nonzero ideals of `T` and every `m` there is `r₀ > 0` such that
`ord_{R'}(f) ≥ (m/r) o - A` for every `r > 0` divisible by `r₀`, every `o` with
`ord_{R'} ≥ o` on `J_r`, and every `f ∈ B_m` (with `ord_{R'}(f) = ν ∈ ℕ`). -/
theorem exists_ord_testSeq_ge (R' : BirationalDVR k X.ConeRing) {j : Fin (M + 1)}
    (hj : R'.ord (X.coneS (MvPolynomial.X j)) = 0) :
    ∃ A : ℕ, ∀ J : ℕ → Ideal X.ConeRing, (∀ m r, J m * J r ≤ J (m + r)) →
      (∀ q, 0 < q → J q ≠ ⊥) → ∀ m : ℕ, ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, 0 < r → r₀ ∣ r →
        ∀ o : ℕ, (∀ g ∈ J r, (o : ℕ∞) ≤ R'.ord g) → ∀ f ∈ D.testSeq J m, ∀ ν : ℕ,
          R'.ord f = ν → (m : ℝ) / r * o - A ≤ ν := by
  have : CharP R'.ring p := charP_of_injective_algebraMap (algebraMap k R'.ring).injective p
  have : IsFractionRing R'.ring (FractionRing X.ConeRing) := R'.isFractionRing
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R'.ring
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := FractionRing X.ConeRing) hϖ
  have hy : IsPBasis p (algebraMap R'.ring (FractionRing X.ConeRing) ∘
      fun o => R'.toRing (X.coneZ D.idx o)) := D.isPBasis_z
  obtain ⟨-, -, a, -, -, htr⟩ := exists_logDiscrepancy (p := p) k hy hϖ
  obtain ⟨b, hb⟩ := D.exists_ordGE_mu R' hϖ
  have hT : ∀ t : X.ConeRing, OrdGE ϖ 0 (algebraMap X.ConeRing (FractionRing X.ConeRing) t) :=
    fun t => ordGE_algebraMap (R'.toRing t)
  refine ⟨1 + a + b, fun J hJ hne m => ?_⟩
  obtain ⟨r₀, hr₀, h⟩ := D.exists_theta_le_testSeq hJ hne m
  refine ⟨r₀, hr₀, fun r hr hdvd o ho f hf ν hν => ?_⟩
  obtain ⟨e, he⟩ := h r hr hdvd
  obtain ⟨-, hsat, -⟩ := he e le_rfl
  set N := ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊
  have ho' : ∀ g ∈ J r, OrdGE ϖ o (algebraMap X.ConeRing (FractionRing X.ConeRing) g) :=
    fun g hg => (ordGE_algebraMap_iff_addVal hϖ o (R'.toRing g)).2 (ho g hg)
  obtain ⟨l, hl⟩ := ProjSubvariety.mem_saturation_iff.1 (hsat hf)
  have hxl : X.coneS (MvPolynomial.X j) ^ l ∈ X.coneIrrelevant ^ l :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self
      (f := fun i => Polynomial.C (X.coordMk (MvPolynomial.X i))) j)) l
  have hmem := hl _ hxl
  have hord : R'.ord (X.coneS (MvPolynomial.X j) ^ l * f) = ν := by
    rw [BirationalDVR.ord_mul, BirationalDVR.ord_pow, hj, smul_zero, zero_add, hν]
  have h1 := le_of_ordGE_of_ord_eq hϖ hord
    (D.ordGE_of_mem_thetaK hϖ0 hT (fun e n f hf => htr e n f hf) hb ho' (D.mem_theta.1 hmem))
  have hQ : 0 < p ^ e := pow_pos hp.out.pos e
  have hN : (m : ℝ) / r * ((p ^ e : ℕ) : ℝ) ≤ N := by
    have h2 := Nat.le_ceil ((m : ℚ) / r * (p : ℚ) ^ e)
    have h3 := (Rat.cast_le (K := ℝ)).2 h2
    push_cast at h3 ⊢
    exact h3
  have h4 := le_ediv_sub_of_le_mul (o := o) (a := a) (b := b) hQ hN
  have h5 : ((((N * o : ℕ) - (b : ℤ) + a) / ((p ^ e : ℕ) : ℤ) - a : ℤ) : ℝ) ≤ ν := by
    exact_mod_cast h1
  exact (le_trans h4 h5).trans_eq' (by push_cast; ring)

/-- **`prop:sg-valuative-bound` at divisorial points** (step (c) of `thm:sg-ep-charp`): for a
divisorial point `v ∈ X^an` there is `A ≥ 0` such that for every graded sequence `J_•` of nonzero
ideals of `T` and every `m` there is `r₀ > 0` with `φ_{B_m}(v) ≤ (m/r) φ_{J_r}(v) + A` for every
`r > 0` divisible by `r₀`; here `φ_𝔟 = φ_{𝔟 ∩ R_M[t]}`, and `A = c (1 + a + b)` for the constant
`c` of `v`. -/
theorem exists_phiIdeal_testSeq_le {v : X.an} (hv : X.IsDivisorial v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J : ℕ → Ideal X.ConeRing, (∀ m r, J m * J r ≤ J (m + r)) →
      (∀ q, 0 < q → J q ≠ ⊥) → ∀ m : ℕ, ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, 0 < r → r₀ ∣ r →
        phiIdeal ((D.testSeq J m).comap X.coneMk) v.1 ≤
          (((m : ℝ) / r : ℝ) : EReal) * phiIdeal ((J r).comap X.coneMk) v.1 + (A : EReal) := by
  classical
  obtain ⟨R', c, hc, hlog⟩ := hv
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  -- `log|g|_{σ(v)} = -c ν` when `ord_{R'}(ḡ) = ν`
  have hlogν : ∀ (g : (MvPolynomial (Fin (M + 1)) k)[X]) (ν : ℕ), R'.ord (X.coneMk g) = ν →
      Berk.logAbs g (gaussExt v.1) = ((-((c : ℝ) * ν) : ℝ) : EReal) := by
    intro g ν hν
    rw [hlog, hν, show ((ν : ℕ∞) : EReal) = ((ν : ℝ) : EReal) by norm_cast, ← EReal.coe_neg,
      ← EReal.coe_mul, neg_mul]
  -- a coordinate with `ord_{R'}(x̄ⱼ) = 0`
  obtain ⟨j, hj⟩ := ProjBerk.exists_val_X_eq_one v.1
  have hj' : R'.ord (X.coneS (MvPolynomial.X j)) = 0 := by
    have h := hlog (Polynomial.C (MvPolynomial.X j))
    rw [ProjBerk.logAbs_C_gaussExt, ProjBerk.logAbs_def, hj, ENNReal.coe_one, ENNReal.log_one,
      coneMk_C] at h
    change (0 : EReal) = -((c : ℝ) : EReal) * (R'.ord (X.coneS (MvPolynomial.X j)) : EReal) at h
    induction h' : R'.ord (X.coneS (MvPolynomial.X j)) using ENat.recTopCoe with
    | top =>
      rw [h'] at h
      simp [← EReal.coe_neg, EReal.coe_mul_top_of_neg (neg_neg_of_pos hc')] at h
    | coe ν =>
      rw [h', show ((ν : ℕ∞) : EReal) = ((ν : ℝ) : EReal) by norm_cast, ← EReal.coe_neg,
        ← EReal.coe_mul, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at h
      have : (ν : ℝ) = 0 := by
        rcases mul_eq_zero.1 h.symm with h1 | h1
        · exact absurd (neg_eq_zero.1 h1) hc'.ne'
        · exact h1
      exact_mod_cast this
  obtain ⟨A, hA⟩ := D.exists_ord_testSeq_ge R' hj'
  refine ⟨c * A, by positivity, fun J hJ hne m => ?_⟩
  obtain ⟨r₀, hr₀, h⟩ := hA J hJ hne m
  refine ⟨r₀, hr₀, fun r hr hdvd => ?_⟩
  -- the order `o` of `J_r`, attained at `f₀`
  have hex : ∃ o : ℕ, ∃ f ∈ J r, R'.ord f = o := by
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne r hr)
    obtain ⟨o, ho⟩ := ENat.ne_top_iff_exists.1 (mt R'.ord_eq_top_iff.1 hf0)
    exact ⟨o, f, hf, ho.symm⟩
  obtain ⟨f₀, hf₀, hf₀o⟩ := Nat.find_spec hex
  have ho : ∀ g ∈ J r, ((Nat.find hex : ℕ) : ℕ∞) ≤ R'.ord g := by
    intro g hg
    by_cases hg0 : g = 0
    · rw [hg0, BirationalDVR.ord_zero]
      exact le_top
    · obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.1 (mt R'.ord_eq_top_iff.1 hg0)
      rw [← hν]
      exact_mod_cast Nat.find_min' hex ⟨g, hg, hν.symm⟩
  set o := Nat.find hex
  have hL : ((-((c : ℝ) * o) : ℝ) : EReal) ≤ phiIdeal ((J r).comap X.coneMk) v.1 := by
    obtain ⟨g₀, rfl⟩ := coneMk_surjective (X := X) f₀
    rw [← hlogν g₀ o hf₀o]
    exact ProjBerk.le_phiIdeal _ v.1 (Ideal.mem_comap.2 hf₀)
  have hmr : (0 : ℝ) ≤ (m : ℝ) / r := by positivity
  have hbound : (((m : ℝ) / r * (-((c : ℝ) * o)) + c * A : ℝ) : EReal) ≤
      (((m : ℝ) / r : ℝ) : EReal) * phiIdeal ((J r).comap X.coneMk) v.1 +
        ((c * A : ℝ) : EReal) := by
    rw [EReal.coe_add, EReal.coe_mul]
    exact add_le_add (ProjBerk.ereal_coe_mul_monotone hmr hL) le_rfl
  refine le_trans (iSup₂_le fun g hg => ?_) hbound
  by_cases hg0 : X.coneMk g = 0
  · rw [Berk.logAbs, gaussExt_val_eq_zero_of_coneMk_eq_zero v hg0, ENNReal.coe_zero,
      ENNReal.log_zero]
    exact bot_le
  · obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.1 (mt R'.ord_eq_top_iff.1 hg0)
    have h1 := h r hr hdvd o ho _ (Ideal.mem_comap.1 hg) ν hν.symm
    rw [hlogν g ν hν.symm, EReal.coe_le_coe_iff]
    nlinarith

end ConeTraceData

end ProjSubvariety

end EnvelopeProperty
