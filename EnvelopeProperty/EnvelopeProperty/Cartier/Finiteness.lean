import EnvelopeProperty.Cartier.Order

/-!
# Finiteness over `p`-th powers and a uniform Frobenius trace estimate

Let `k` be a perfect field of characteristic `p` and `R` a `k`-algebra essentially of finite type.
Then `R` is generated as a module over its subring `R^p` of `p`-th powers by finitely many
elements: if `R` is a localization of `k[s_1, …, s_n]`, the monomials `s^a`, `a ∈ [0,p)^n`, generate
(`exists_surjective_pSum`); `k = k^p` is used for the coefficients and `t⁻¹ = t^{p-1} (t⁻¹)^p` for the
denominators.

Consequently, if `R` is moreover a DVR with fraction field `F` and `y` is any `p`-basis of `F`, the
Frobenius trace `Φ_y` maps `R` into `ϖ^{-D} R` for some `D` (finitely many generators), and the
estimates of `EnvelopeProperty.Cartier.Order` give a constant `a ≥ 0` with
`ord_R(Φ_y^e f) ≥ ⌊(ord_R f + a)/p^e⌋ - a ≥ (ord_R f - (p^e - 1)(a + 1))/p^e`
for all `e` and all `f ∈ F` (`exists_ordGE_traceIter`). This is FHX (3.11)
(`eq:divisorial-trace-bound`, proof of Lemma 3.3 `lem:divisorial-trace-estimate`) for `w = ord_R`
with *some* constant `a` in place of the log discrepancy `A_S(ord_R) - 1`; for the downstream
use in FHX only the finiteness of this constant matters.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

variable (p : ℕ) [hp : Fact p.Prime]

section Span

variable {R : Type*} [CommRing R] [CharP R p] {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem pow_mul_mem_range_pSum (s : σ → R) (g : R) {x : R} (hx : x ∈ AddMonoidHom.mrange (pSum p s)) :
    g ^ p * x ∈ AddMonoidHom.mrange (pSum p s) := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨g • c, pSum_smul p s g c⟩

theorem mono_mem_range_pSum (s : σ → R) (n : σ → ℕ) : mono s n ∈ AddMonoidHom.mrange (pSum p s) := by
  refine ⟨Pi.single (Box.ofNat n) (mono s fun i => n i / p), ?_⟩
  rw [pSum_single, ← mono_eq_pow_mul]

theorem mul_mem_range_pSum (s : σ → R) {x y : R} (hx : x ∈ AddMonoidHom.mrange (pSum p s))
    (hy : y ∈ AddMonoidHom.mrange (pSum p s)) : x * y ∈ AddMonoidHom.mrange (pSum p s) := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  rw [pSum_apply, sum_mul]
  refine (AddMonoidHom.mrange (pSum p s)).sum_mem fun a _ => ?_
  rw [pSum_apply, mul_sum]
  refine (AddMonoidHom.mrange (pSum p s)).sum_mem fun b _ => ?_
  rw [show c a ^ p * mono s a.toNat * (d b ^ p * mono s b.toNat) =
    (c a * d b) ^ p * mono s (a.toNat + b.toNat) by rw [mono_add, mul_pow]; ring]
  exact pow_mul_mem_range_pSum p s _ (mono_mem_range_pSum p s _)

/-- The subalgebra `∑_a R^p s^a` (it is all of the elements of the form `∑_a (c_a)^p s^a`). -/
def pSumSubalgebra (s : σ → R) (k : Type*) [Field k] [CharP k p] [PerfectRing k p] [Algebra k R] :
    Subalgebra k R where
  carrier := AddMonoidHom.mrange (pSum p s)
  mul_mem' hx hy := mul_mem_range_pSum p s hx hy
  add_mem' := (AddMonoidHom.mrange (pSum p s)).add_mem
  algebraMap_mem' r := by
    have h : algebraMap k R r = (algebraMap k R ((frobeniusEquiv k p).symm r)) ^ p * mono s 0 := by
      rw [mono_zero, mul_one, ← map_pow, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact pow_mul_mem_range_pSum p s _ (mono_mem_range_pSum p s 0)

theorem adjoin_le_pSumSubalgebra (s : σ → R) (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
    [Algebra k R] : Algebra.adjoin k (Set.range s) ≤ pSumSubalgebra p s k := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  have : s i = mono s (Pi.single i 1) := by rw [mono_single, pow_one]
  rw [this]
  exact mono_mem_range_pSum p s _

end Span

/-- A `k`-algebra essentially of finite type over a perfect field `k` of characteristic `p` is
generated over its `p`-th powers by finitely many monomials: there are `s : Fin n → R` with
`R = {∑_{a ∈ [0,p)^n} (c_a)^p s^a}`. -/
theorem exists_surjective_pSum (k R : Type*) [Field k] [CharP k p] [PerfectRing k p] [CommRing R]
    [CharP R p] [Algebra k R] [Algebra.EssFiniteType k R] :
    ∃ (n : ℕ) (s : Fin n → R), Function.Surjective (pSum p s) := by
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff k R).1 ‹Algebra.EssFiniteType k R›
  let s : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  have hs : Set.range s = (σ : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [s]⟩
  refine ⟨σ.card, s, fun r => ?_⟩
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [← hs] at ht hrt
  have hmem : ∀ x ∈ Algebra.adjoin k (Set.range s), x ∈ AddMonoidHom.mrange (pSum p s) :=
    fun x hx => adjoin_le_pSumSubalgebra p s k hx
  -- `r = (r t) t^{p-1} (t⁻¹)^p`
  obtain ⟨u, rfl⟩ := htu
  have h1 : r * u * u ^ (p - 1) ∈ AddMonoidHom.mrange (pSum p s) :=
    hmem _ (Subalgebra.mul_mem _ hrt (Subalgebra.pow_mem _ ht _))
  have h2 := pow_mul_mem_range_pSum p s (↑u⁻¹ : R) h1
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  have : (↑u⁻¹ : R) ^ p * (r * ↑u * ↑u ^ (p - 1)) = r := by
    conv_lhs => rw [hp1]
    rw [pow_succ]
    calc (↑u⁻¹ : R) ^ (p - 1) * ↑u⁻¹ * (r * ↑u * ↑u ^ (p - 1))
        = r * ((↑u⁻¹ : R) * ↑u) * ((↑u⁻¹ : R) * ↑u) ^ (p - 1) := by ring
      _ = r := by rw [Units.inv_mul, one_pow, mul_one, mul_one]
  rw [this] at h2
  exact h2

/-! ### The uniform trace estimate at a DVR essentially of finite type -/

section Estimate

variable {k R F : Type*} [Field k] [CharP k p] [PerfectRing k p] [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra k R] [Algebra.EssFiniteType k R] [Field F] [Algebra R F]
  [IsFractionRing R F] [CharP F p] {σ : Type*} [Fintype σ] [DecidableEq σ] {y : σ → F}
  (hy : IsPBasis p y) {ϖ : R} (hϖ : Irreducible ϖ)

include hy hϖ

/-- The Frobenius trace `Φ_y` maps `R` into `ϖ^{-D} R` for some `D`. -/
theorem exists_ordGE_trace_of_mem (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
    [Algebra k R] [Algebra.EssFiniteType k R] :
    ∃ D : ℕ, ∀ f : F, OrdGE ϖ 0 f → OrdGE ϖ (-(D : ℤ)) (hy.trace f) := by
  have : CharP R p := charP_of_injective_algebraMap (algebraMap k R).injective p
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := F) hϖ
  obtain ⟨n, s, hs⟩ := exists_surjective_pSum p k R
  choose d hd using fun a : Box (Fin n) p =>
    exists_ordGE hϖ (hy.trace (algebraMap R F (mono s a.toNat)))
  refine ⟨univ.sup fun a => (-d a).toNat, fun f hf => ?_⟩
  obtain ⟨r, rfl⟩ := ordGE_zero_iff.1 hf
  obtain ⟨c, rfl⟩ := hs r
  rw [map_pSum, pSum_apply, map_sum]
  refine OrdGE.sum _ fun a _ => ?_
  rw [← map_mono, hy.trace_pow_mul]
  refine ((hd a).algebraMap_mul hϖ0 (c a)).mono hϖ0 ?_
  have : (-d a).toNat ≤ univ.sup fun a => (-d a).toNat :=
    le_sup (f := fun a => (-d a).toNat) (mem_univ a)
  omega

/-- **Uniform trace estimate (FHX (3.11) with an unspecified constant).** Let `k` be a perfect
field of characteristic `p`, `R` a DVR essentially of finite type over `k` with uniformizer `ϖ`
and fraction field `F`, and `y` a `p`-basis of `F`. There is `a : ℕ` such that for all `e` and all
`f ∈ F`, `ord_R f ≥ n` implies `ord_R(Φ_y^e f) ≥ ⌊(n + a)/p^e⌋ - a`. -/
theorem exists_ordGE_traceIter (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
    [Algebra k R] [Algebra.EssFiniteType k R] :
    ∃ a : ℕ, ∀ (e : ℕ) (n : ℤ) (f : F), OrdGE ϖ n f →
      OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a) (hy.traceIter e f) := by
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := F) hϖ
  obtain ⟨D, hD⟩ := exists_ordGE_trace_of_mem p hy hϖ k
  refine ⟨p * D, fun e n f hf => ordGE_traceIter_of_step p hy (a := ((p * D : ℕ) : ℤ))
    (fun n f hf => ?_) e hf⟩
  have h1 := ordGE_trace_of_bound p hy hϖ0 (c := 0) (d := -(D : ℤ)) hD hf
  refine h1.mono hϖ0 ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp0 : (p : ℤ) ≠ 0 := by positivity
  rw [Nat.cast_mul, mul_comm, Int.add_mul_ediv_right _ _ hp0, sub_zero]
  nlinarith [show (0 : ℤ) ≤ D from by positivity]

end Estimate

end EnvelopeProperty.Cartier
