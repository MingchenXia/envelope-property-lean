/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NormalizationDescentCharP

/-!
# The additive-power sandwich on a unibranch model in characteristic `0`

This file implements the blueprint node `lem:nn-additive-sandwich` of `nonnef.tex` (subsection
`subsec:nn-main`; the claim in the characteristic-`0` part of the proof of
`thm:gl-normalization-reflection` in `global.tex`) for the formalization of Fang–Han–Xia, *The
envelope property for unibranch projective varieties* (FHX, §8, proof of
Theorem 8.3 `thm:normalization-reflection`, `eq:normalization-global-sandwich`).

Let `𝒳` be a unibranch model over an algebraically closed field `k` of characteristic `0`,
`𝒴 = 𝒳^ν` its normalization and `ν^an : 𝒴^an ≃ₜ 𝒳^an` (`MultiModel.IsUnibranch.anHomeomorph`).

## Main results

* `EnvelopeProperty.exists_pow_smul_mem_one_of_finite`: for a finite algebra `B` over a
  noetherian ring `A` and `ρ ∈ A` there is a **uniform** `N` such that every `y ∈ B` with some
  `ρ^M y ∈ A` has `ρ^N y ∈ A` (the `ρ`-power torsion of `B / A` is killed by `ρ^N`; condition (ii)
  of the blueprint, at chart level: `MultiModel.exists_pow_mul_mem_chartAlg_normalization`).
* `MultiModel.IsUnibranch.exists_uniform_addPow`: the additive powers of
  `thm:gl-additive-powers` for the chart quotients `f_j = s / z̃_j^a` of a section `s ∈ R_a(𝒴)`,
  with `N, d` common to all charts (`EnvelopeProperty.addPowSeq`, padded with zero coefficients,
  `EnvelopeProperty.addPowSeq_padCoeff`).
* `MultiModel.IsUnibranch.exists_isHomFS_sandwich` (**`lem:nn-additive-sandwich`**): for
  `a ∈ ℤ^r` and `0 ≠ s ∈ R_a(𝒴)`, with `u = log |s|`, there are `d, R, n₀` such that for every
  `n ≥ n₀` some `F_n ∈ 𝓗_hom(𝒳, a + 3R/(n + 2d) 𝟙)` satisfies `u ≤ F_n ∘ ν^an ≤ n/(n + 2d) u`.

## The construction

For each chart `j`, `f_j = s / z̃_j^a ∈ B_j` and `a_{jm} = f_j^m + ∑_i binom(m, i) c_{ji} f_j^{m-i}
∈ A_j` for `m ≥ N`. With `e_n = (n + 2d) a + 3R 𝟙` the terms of `F_n` are
`T_{j,l} = z̃_j^{e_n} a_{j, n+d+l}` (`0 ≤ l ≤ d`), sections of `𝒳` of degree `e_n`:

* `T_{j,l} = s^n G_{j,l}` with `G_{j,l} ∈ R_{e_n - n a}(𝒴)` a polynomial in `s`, the
  `ĉ_{ji} = c_{ji} z̃_j^{ia + R𝟙} ∈ R_{ia + R𝟙}(𝒴)` (condition (i)) and chart monomials of
  nonnegative degree (condition (iii)), so `|T_{j,l}| ≤ |s|^n`;
* `T_{j,l} ∈ R_{e_n}(𝒳)` by the chart criterion `mem_sections_of_forall_div_chartDenZ`: on a chart
  `j'`, `T_{j,l} / z̃_{j'}^{e_n} = ρ^R y` with `ρ = z̃_j^𝟙 / z̃_{j'}^𝟙 ∈ A_{j'}`, `y ∈ B_{j'}` and
  `ρ^M y ∈ A_{j'}` for large `M`; the uniform torsion bound (condition (ii)) gives `ρ^R y ∈ A_{j'}`;
* at `w` with `|z_{j_c}|_w = 1`, Lagrange interpolation (`lem:gl-lagrange`,
  `EnvelopeProperty.pow_mem_span_addPow`) in `B_j` gives `|s|_w^{n + 2d} ≤ max_l |T_{j,l}|_w`.

## Deviations from the blueprint proof

* Condition (ii) ("`z̃_j^{R𝟙}` kills the `z_j`-power torsion of the finite `S`-module `S^ν/S`") is
  used at chart level: for each pair of charts `j, j'`, the `ρ`-power torsion of the finite
  `A_{j'}`-module `B_{j'}/A_{j'}` is killed by a uniform power of `ρ = z̃_j^𝟙 / z̃_{j'}^𝟙`
  (noetherianity of `A_{j'}`), and the sections of `𝒳` are recognized by the chart criterion.
  The terms are written `T_{j,l} = z̃_j^{e_n} a_{j,n+d+l}`; this is the blueprint's
  `t_{jm} z̃_j^γ` with the monomial `z̃_j^γ = z̃_j^{R𝟙 + (n+2d-m)a}` of the chart `j`.
* The statement records the degree of `F_n` as `a + 3R/(n+2d) 𝟙` and requires `n ≥ n₀` with
  `n₀ = N + 1` (so that `n ≥ 1` and `n + d ≥ N`).
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Additive power sequences -/

/-- The additive power sequence `aₘ = fᵐ + ∑_{i=1}^d binom(m, i) cᵢ f^{m-i}` of FHX Lemma 8.2
(here `c i = c_{i+1}`). -/
def addPowSeq {F : Type*} [CommSemiring F] (f : F) {d : ℕ} (c : Fin d → F) (m : ℕ) : F :=
  f ^ m + ∑ i : Fin d, (m.choose (i + 1) : F) * c i * f ^ (m - (i + 1))

/-- Padding a coefficient family `Fin d → F` by zeros to `Fin D → F`. -/
def padCoeff {F : Type*} [Zero F] {d D : ℕ} (c : Fin d → F) : Fin D → F :=
  fun i => if h : (i : ℕ) < d then c ⟨i, h⟩ else 0

/-- Padding by zero coefficients does not change the additive power sequence. -/
theorem addPowSeq_padCoeff {F : Type*} [CommSemiring F] (f : F) {d D : ℕ} (hdD : d ≤ D)
    (c : Fin d → F) (m : ℕ) : addPowSeq f (padCoeff (D := D) c) m = addPowSeq f c m := by
  unfold addPowSeq
  congr 1
  set g : ℕ → F := fun i => if h : i < d then (m.choose (i + 1) : F) * c ⟨i, h⟩ *
    f ^ (m - (i + 1)) else 0 with hg
  have h1 : ∑ i : Fin D, (m.choose (i + 1) : F) * padCoeff c i * f ^ (m - (i + 1)) =
      ∑ i : Fin D, g i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [padCoeff, hg]
    split_ifs <;> simp
  have h2 : ∑ i : Fin d, (m.choose (i + 1) : F) * c i * f ^ (m - (i + 1)) =
      ∑ i : Fin d, g i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, dif_pos i.isLt]
  rw [h1, h2, Fin.sum_univ_eq_sum_range g D, Fin.sum_univ_eq_sum_range g d]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hdD) fun i _ hi => ?_
  have hid : ¬i < d := fun h => hi (Finset.mem_range.2 h)
  simp only [hg, dif_neg hid]

/-- **The additive powers of a chart quotient, times a chart monomial** (the identity
`z̃_j^{ma + R𝟙} a_{jm} = s^n g` of the proof of `lem:nn-additive-sandwich`, `m = n + d + l`):
for `A ≠ 0` and `f = s / A`,
`A^m Q aₘ = s^n (Q s^{d+l} + ∑_i binom(m, i+1) (cᵢ A^{i+1} Q) s^{d+l-(i+1)})`. -/
theorem pow_mul_addPowSeq_div {F : Type*} [Field F] {A : F} (hA : A ≠ 0) (Q s : F) (n D l : ℕ)
    (c : Fin D → F) :
    A ^ (n + D + l) * Q * addPowSeq (s / A) c (n + D + l) =
      s ^ n * (Q * s ^ (D + l) + ∑ i : Fin D, ((n + D + l).choose (i + 1) : F) *
        (c i * (A ^ ((i : ℕ) + 1) * Q)) * s ^ (D + l - (i + 1))) := by
  rw [addPowSeq, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · rw [div_pow]
    field_simp
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    obtain ⟨q, hq⟩ : ∃ q, D + l = q + (i + 1) := ⟨D + l - (i + 1), by omega⟩
    rw [show n + D + l = n + q + (i + 1) by omega, hq, Nat.add_sub_cancel, Nat.add_sub_cancel,
      div_pow]
    field_simp
    ring

/-! ### Uniform torsion bounds -/

/-- **Uniform torsion bound.** Let `B` be a finite algebra over a noetherian ring `A` and `ρ ∈ A`.
There is `N` such that every `y ∈ B` with `ρ^M y ∈ A` for some `M` has `ρ^N y ∈ A`: the
submodules `{y : ρⁿ y ∈ A}` of the noetherian `A`-module `B` stabilize. -/
theorem exists_pow_smul_mem_one_of_finite {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B] (ρ : A) :
    ∃ N : ℕ, ∀ y : B, (∃ M : ℕ, ρ ^ M • y ∈ (1 : Submodule A B)) →
      ρ ^ N • y ∈ (1 : Submodule A B) := by
  have : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B
  let P : ℕ →o Submodule A B :=
    { toFun := fun n => (1 : Submodule A B).comap (LinearMap.lsmul A B (ρ ^ n))
      monotone' := fun n n' hnn' y hy => by
        simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hy ⊢
        rw [← Nat.sub_add_cancel hnn', pow_add, mul_smul]
        exact Submodule.smul_mem _ _ hy }
  have hP : ∀ n y, y ∈ P n ↔ ρ ^ n • y ∈ (1 : Submodule A B) := fun _ _ => Iff.rfl
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance P
  refine ⟨N, fun y ⟨M, hM⟩ => ?_⟩
  have hy : y ∈ P (max N M) := P.monotone (le_max_right N M) ((hP M y).2 hM)
  rw [← hN _ (le_max_left N M)] at hy
  exact (hP N y).1 hy

/-- Every finite family of integers is bounded by a natural number. -/
theorem exists_nat_ge_of_finite_int {ι : Type*} [Finite ι] (f : ι → ℤ) :
    ∃ R : ℕ, ∀ i, f i ≤ R := by
  cases nonempty_fintype ι
  refine ⟨∑ i, (f i).toNat, fun i => ?_⟩
  have h1 : f i ≤ (f i).toNat := Int.self_le_toNat (f i)
  have h2 : (f i).toNat ≤ ∑ i, (f i).toNat :=
    Finset.single_le_sum (f := fun i => (f i).toNat) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2' : ((f i).toNat : ℤ) ≤ ((∑ i, (f i).toNat : ℕ) : ℤ) := by exact_mod_cast h2
  exact h1.trans h2'

/-- A seminorm bounded by `1` on a ring is bounded on an ideal by its bound on generators. -/
theorem valuation_le_of_mem_span_of_le_one {A : Type*} [CommRing A] (v : Valuation A ℝ≥0)
    (h1 : ∀ x, v x ≤ 1) {S : Set A} {M : ℝ≥0} (hS : ∀ x ∈ S, v x ≤ M) {x : A}
    (hx : x ∈ Ideal.span S) : v x ≤ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => exact (v.map_add x y).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, v.map_mul]
    exact (mul_le_of_le_one_left zero_le (h1 c)).trans hx

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-- `|s|_v^n ≤ |t|_v` gives `n log |s|_v ≤ log |t|_v`. -/
theorem natCast_mul_logSecAbs_le_of_pow_le {Y : MultiModel k K r} {v : Berk k Y.S}
    {a e : Fin r → ℤ} {s t : K} {n : ℕ} (h : Y.secAbs v a s ^ n ≤ Y.secAbs v e t) :
    ((n : ℝ) : EReal) * Y.logSecAbs v a s ≤ Y.logSecAbs v e t := by
  rw [logSecAbs, logSecAbs, EReal.coe_natCast, ← ENNReal.log_pow, ← ENNReal.coe_pow]
  exact ENNReal.log_monotone (ENNReal.coe_le_coe.2 h)

section Normalization

variable (X : MultiModel k K r) [Infinite k] [PerfectField k]

/-- **Uniform torsion bound on a chart of the normalization**: for `ρ ∈ A_j` there is `N` such
that every `y ∈ B_j` with some `ρ^M y ∈ A_j` has `ρ^N y ∈ A_j` (`A_j` is noetherian and `B_j` is
a finite `A_j`-module). -/
theorem exists_pow_mul_mem_chartAlg_normalization (j : X.ChartIndex) {ρ : K}
    (hρ : ρ ∈ X.chartAlg j) :
    ∃ N : ℕ, ∀ y ∈ X.normalization.chartAlg j, (∃ M : ℕ, ρ ^ M * y ∈ X.chartAlg j) →
      ρ ^ N * y ∈ X.chartAlg j := by
  let : Algebra (X.chartAlg j) (X.normalization.chartAlg j) :=
    (FiniteHom.ofNormalization X).chartAlgebra j
  have : Module.Finite (X.chartAlg j) (X.normalization.chartAlg j) :=
    (FiniteHom.ofNormalization X).finite_chartAlgebra j
  have : IsNoetherianRing (X.chartAlg j) := Algebra.FiniteType.isNoetherianRing k _
  have hone : ∀ z : X.normalization.chartAlg j,
      z ∈ (1 : Submodule (X.chartAlg j) (X.normalization.chartAlg j)) ↔ (z : K) ∈ X.chartAlg j := by
    intro z
    rw [Submodule.mem_one]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  have hsmul : ∀ (M : ℕ) (z : X.normalization.chartAlg j),
      (((⟨ρ, hρ⟩ : X.chartAlg j) ^ M • z : X.normalization.chartAlg j) : K) = ρ ^ M * (z : K) := by
    intro M z
    rw [Algebra.smul_def, Subalgebra.coe_mul]
    rfl
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_one_of_finite
    (A := X.chartAlg j) (B := X.normalization.chartAlg j) ⟨ρ, hρ⟩
  refine ⟨N, fun y hy ⟨M, hM⟩ => ?_⟩
  have h := hN ⟨y, hy⟩ ⟨M, (hone _).2 (by rw [hsmul]; exact hM)⟩
  rw [hone, hsmul] at h
  exact h

end Normalization

section Unibranch

variable {X : MultiModel k K r} [Infinite k] [PerfectField k]

namespace IsUnibranch

variable (hX : X.IsUnibranch)

include hX

/-- **Uniform additive powers** (`thm:gl-additive-powers` on all charts at once): for a section
`s ∈ R_a(𝒴)` there are `N, d` and coefficients `c_{ji} ∈ B_j` with
`a_{jm} = f_j^m + ∑_{i=1}^d binom(m, i) c_{ji} f_j^{m-i} ∈ A_j` for all charts `j` and `m ≥ N`,
where `f_j = s / z̃_j^a`. -/
theorem exists_uniform_addPow [IsAlgClosed k] [CharZero k] {a : Fin r → ℤ} {s : K}
    (hs : s ∈ X.normalization.sections a) :
    ∃ (N D : ℕ) (c : X.ChartIndex → Fin D → K), ∀ j : X.ChartIndex,
      (∀ c', X.coord c' (j c') ≠ 0) → (∀ i, c j i ∈ X.normalization.chartAlg j) ∧
        ∀ m, N ≤ m → addPowSeq (s / X.chartDenZ j a) (c j) m ∈ X.chartAlg j := by
  classical
  have h1 : ∀ j : X.ChartIndex, ∃ (N d : ℕ) (c : Fin d → K), (∀ c', X.coord c' (j c') ≠ 0) →
      (∀ i, c i ∈ X.normalization.chartAlg j) ∧
        ∀ m, N ≤ m → addPowSeq (s / X.chartDenZ j a) c m ∈ X.chartAlg j := by
    intro j
    by_cases hj : ∀ c', X.coord c' (j c') ≠ 0
    · obtain ⟨N, d, c, hc, -, hm⟩ := hX.exists_addPow_mem_chartAlg hj
        (X.normalization.div_chartDenZ_mem_chartAlg (j := j) hj hs)
      exact ⟨N, d, c, fun _ => ⟨hc, hm⟩⟩
    · exact ⟨0, 0, Fin.elim0, fun h => absurd h hj⟩
  choose N d c hc using h1
  refine ⟨Finset.univ.sup N, Finset.univ.sup d, fun j => padCoeff (c j), fun j hj =>
    ⟨fun i => ?_, fun m hm => ?_⟩⟩
  · simp only [padCoeff]
    split_ifs
    · exact (hc j hj).1 _
    · exact Subalgebra.zero_mem _
  · rw [addPowSeq_padCoeff _ (Finset.le_sup (f := d) (Finset.mem_univ j))]
    exact (hc j hj).2 m ((Finset.le_sup (f := N) (Finset.mem_univ j)).trans hm)

/-- **The additive-power sandwich** (`lem:nn-additive-sandwich`; the claim in the
characteristic-`0` part of the proof of `thm:gl-normalization-reflection`, FHX
`eq:normalization-global-sandwich`). Let `𝒳` be unibranch over an algebraically closed field of
characteristic `0`, `a ∈ ℤ^r` and `0 ≠ s ∈ R_a(𝒴)`, `u = log |s|` on `𝒴^an`. There are
`d, R, n₀ ∈ ℕ` such that for every `n ≥ n₀` there is `F_n ∈ 𝓗_hom(𝒳, a + 3R/(n + 2d) 𝟙)` with
`u ≤ F_n ∘ ν^an ≤ n/(n + 2d) u`. -/
theorem exists_isHomFS_sandwich [IsAlgClosed k] [CharZero k] {a : Fin r → ℤ} {s : K}
    (hs : s ∈ X.normalization.sections a) (hs0 : s ≠ 0) :
    ∃ D R n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ F : X.an → EReal,
      X.IsHomFS (fun c => (a c : ℚ) + 3 * R / (n + 2 * D)) F ∧
      ∀ w : X.normalization.an, X.normalization.logSecAbs w.1 a s ≤ F (hX.anHomeomorph w) ∧
        F (hX.anHomeomorph w) ≤
          (((n : ℝ) / (n + 2 * D) : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s := by
  classical
  obtain ⟨N, D, c, hc⟩ := hX.exists_uniform_addPow hs
  -- `ρ_{jj'} = z̃_j^𝟙 / z̃_{j'}^𝟙 ∈ A_{j'}`
  have hρ : ∀ j j' : X.ChartIndex, (∀ c', X.coord c' (j' c') ≠ 0) →
      X.chartDenZ j 1 / X.chartDenZ j' 1 ∈ X.chartAlg j' := fun j j' hj' =>
    div_chartDenZ_mem_chartAlg hj' (chartDenZ_mem_sections j fun _ => zero_le_one)
  -- data for condition (i)
  have hβ : ∀ (j : X.ChartIndex) (i : Fin D), ∃ β : Fin r →₀ ℕ, (∀ c', X.coord c' (j c') ≠ 0) →
      ∀ e' : Fin r → ℤ, (∀ c', (β c' : ℤ) ≤ e' c') →
        c j i * X.normalization.chartDenZ j e' ∈ X.normalization.sections e' := by
    intro j i
    by_cases hj : ∀ c', X.coord c' (j c') ≠ 0
    · obtain ⟨β, hβ⟩ := exists_mul_chartDenZ_mem_sections (Y := X.normalization) (j := j) hj
        ((hc j hj).1 i)
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose β hβ using hβ
  -- data for condition (ii)
  have hNt : ∀ j j' : X.ChartIndex, ∃ Nt : ℕ, (∀ c', X.coord c' (j' c') ≠ 0) →
      ∀ y ∈ X.normalization.chartAlg j',
        (∃ M : ℕ, (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ M * y ∈ X.chartAlg j') →
          (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ Nt * y ∈ X.chartAlg j' := by
    intro j j'
    by_cases hj' : ∀ c', X.coord c' (j' c') ≠ 0
    · obtain ⟨Nt, hNt⟩ := X.exists_pow_mul_mem_chartAlg_normalization j' (hρ j j' hj')
      exact ⟨Nt, fun _ => hNt⟩
    · exact ⟨0, fun h => absurd h hj'⟩
  choose Nt hNt using hNt
  obtain ⟨R₁, hR₁⟩ := exists_nat_ge_of_finite_int fun p : X.ChartIndex × Fin D × Fin r =>
    (β p.1 p.2.1 p.2.2 : ℤ) - (((p.2.1 : ℕ) + 1 : ℕ) : ℤ) * a p.2.2
  obtain ⟨R₂, hR₂⟩ := exists_nat_ge_of_finite_int fun p : Fin (D + 1) × Fin r =>
    -(((D - p.1 : ℕ) : ℤ) * a p.2)
  obtain ⟨R₃, hR₃⟩ := exists_nat_ge_of_finite_int fun p : X.ChartIndex × X.ChartIndex =>
    (Nt p.1 p.2 : ℤ)
  set R : ℕ := R₁ + R₂ + R₃ with hRdef
  -- condition (i): `ĉ_{ji} = c_{ji} z̃_j^{(i+1)a + R𝟙} ∈ R_{(i+1)a + R𝟙}(𝒴)`
  have hP1 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ i : Fin D,
      c j i * X.chartDenZ j (((i : ℕ) + 1) • a + R • 1) ∈
        X.normalization.sections (((i : ℕ) + 1) • a + R • 1) := by
    intro j hj i
    refine hβ j i hj _ fun c' => ?_
    have h := hR₁ (j, i, c')
    have e : ((((i : ℕ) + 1) • a + R • (1 : Fin r → ℤ)) c' : ℤ) =
        (((i : ℕ) + 1 : ℕ) : ℤ) * a c' + R := by
      simp [Pi.add_apply]
    rw [e]
    simp only at h
    have : (R₁ : ℤ) ≤ R := by simp only [hRdef]; push_cast; omega
    linarith
  -- condition (ii)
  have hP2 : ∀ j j' : X.ChartIndex, (∀ c', X.coord c' (j' c') ≠ 0) →
      ∀ y ∈ X.normalization.chartAlg j',
        (∃ M : ℕ, (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ M * y ∈ X.chartAlg j') →
          (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ R * y ∈ X.chartAlg j' := by
    intro j j' hj' y hy hM
    have h := hNt j j' hj' y hy hM
    have hle : Nt j j' ≤ R := by
      have := hR₃ (j, j')
      simp only at this
      have : (Nt j j' : ℤ) ≤ R := by simp only [hRdef]; push_cast; omega
      exact_mod_cast this
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hρ j j' hj') _) h
  -- condition (iii)
  have hP3 : ∀ l ≤ D, ∀ c', 0 ≤ ((D - l) • a + R • (1 : Fin r → ℤ)) c' := by
    intro l hl c'
    have h := hR₂ (⟨l, Nat.lt_succ_of_le hl⟩, c')
    simp only at h
    have e : (((D - l) • a + R • (1 : Fin r → ℤ)) c' : ℤ) = ((D - l : ℕ) : ℤ) * a c' + R := by
      simp [Pi.add_apply]
    rw [e]
    have : (R₂ : ℤ) ≤ R := by simp only [hRdef]; push_cast; omega
    linarith
  refine ⟨D, R, N + 1, fun n hn => ?_⟩
  have hnN : N ≤ n + D := by omega
  set e : Fin r → ℤ := (n + 2 * D) • a + (3 * R) • 1 with hedef
  set E1 : Fin r → ℤ := (n + 2 * D) • a + (2 * R) • 1 with hE1def
  set A : X.ChartIndex → ℕ → K := fun j m => addPowSeq (s / X.chartDenZ j a) (c j) m with hAdef
  set g : X.ChartIndex → ℕ → K := fun j l => X.chartDenZ j (R • 1) * s ^ (D + l) +
    ∑ i : Fin D, ((n + D + l).choose (i + 1) : K) *
      (c j i * X.chartDenZ j (((i : ℕ) + 1) • a + R • 1)) * s ^ (D + l - (i + 1)) with hgdef
  set T : X.ChartIndex → ℕ → K := fun j l => X.chartDenZ j e * A j (n + D + l) with hTdef
  -- `z̃_j^{ma + R𝟙} a_{jm} = s^n g_{jl}` (`m = n + d + l`)
  have hF1 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l : ℕ,
      X.chartDenZ j ((n + D + l) • a + R • 1) * A j (n + D + l) = s ^ n * g j l := by
    intro j hj l
    have h := pow_mul_addPowSeq_div (chartDenZ_ne_zero hj a) (X.chartDenZ j (R • 1)) s n D l
      (c j)
    have e1 : X.chartDenZ j ((n + D + l) • a + R • 1) =
        X.chartDenZ j a ^ (n + D + l) * X.chartDenZ j (R • 1) := by
      rw [chartDenZ_add hj ((n + D + l) • a) (R • 1), chartDenZ_nsmul]
    have e2 : ∀ i : Fin D, X.chartDenZ j (((i : ℕ) + 1) • a + R • 1) =
        X.chartDenZ j a ^ ((i : ℕ) + 1) * X.chartDenZ j (R • 1) := fun i => by
      rw [chartDenZ_add hj (((i : ℕ) + 1) • a) (R • 1), chartDenZ_nsmul]
    simp only [hAdef, hgdef, e1, e2]
    exact h
  -- `g_{jl} ∈ R_{(d+l)a + R𝟙}(𝒴)`
  have hF2 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l : ℕ,
      g j l ∈ X.normalization.sections ((D + l) • a + R • 1) := by
    intro j hj l
    simp only [hgdef]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · have h := mul_mem_sections (chartDenZ_mem_sections (Y := X.normalization) j (e := R • 1)
        fun c' => by simp) (pow_mem_sections hs (D + l))
      rw [add_comm (R • (1 : Fin r → ℤ))] at h
      exact h
    · have hi := i.isLt
      have h := mul_mem_sections (hP1 j hj i) (pow_mem_sections hs (D + l - (i + 1)))
      have hdeg : ((i : ℕ) + 1) • a + R • (1 : Fin r → ℤ) + (D + l - (i + 1)) • a =
          (D + l) • a + R • 1 := by
        funext c'
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply]
        simp only [nsmul_eq_mul, mul_one]
        push_cast [show (i : ℕ) + 1 ≤ D + l by omega]
        ring
      rw [hdeg] at h
      rw [mul_assoc, ← nsmul_eq_mul]
      exact nsmul_mem h _
  have hE1split : ∀ l ≤ D, E1 = ((D - l) • a + R • 1) + ((n + D + l) • a + R • 1) := by
    intro l hl
    funext c'
    simp only [hE1def, Pi.add_apply, Pi.smul_apply, Pi.one_apply]
    simp only [nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub hl]
    ring
  have hF3 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l ≤ D,
      X.chartDenZ j E1 * A j (n + D + l) =
        X.chartDenZ j ((D - l) • a + R • 1) * (s ^ n * g j l) := by
    intro j hj l hl
    rw [hE1split l hl, chartDenZ_add hj ((D - l) • a + R • 1) ((n + D + l) • a + R • 1),
      mul_assoc, hF1 j hj l]
  have hF3' : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l ≤ D,
      X.chartDenZ j E1 * A j (n + D + l) ∈ X.normalization.sections E1 := by
    intro j hj l hl
    rw [hF3 j hj l hl]
    have h := mul_mem_sections (chartDenZ_mem_sections (Y := X.normalization) j (hP3 l hl))
      (mul_mem_sections (pow_mem_sections hs n) (hF2 j hj l))
    have hdeg : ((D - l) • a + R • (1 : Fin r → ℤ)) + (n • a + ((D + l) • a + R • 1)) = E1 := by
      funext c'
      simp only [hE1def, Pi.add_apply, Pi.smul_apply, Pi.one_apply]
      simp only [nsmul_eq_mul, mul_one]
      push_cast [Nat.cast_sub hl]
      ring
    rw [hdeg] at h
    exact h
  have he_split : e = R • 1 + E1 := by
    funext c'
    simp only [hedef, hE1def, Pi.add_apply, Pi.smul_apply, Pi.one_apply]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hT_eq : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l : ℕ,
      T j l = X.chartDenZ j (R • 1) * (X.chartDenZ j E1 * A j (n + D + l)) := by
    intro j hj l
    simp only [hTdef]
    rw [he_split, chartDenZ_add hj (R • 1) E1, mul_assoc]
  -- `T_{jl} = s^n G_{jl}` with `G_{jl}` a section of `𝒴`
  have hF4 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l ≤ D,
      ∃ (e' : Fin r → ℤ) (G : K), G ∈ X.normalization.sections e' ∧ e = n • a + e' ∧
        T j l = s ^ n * G := by
    intro j hj l hl
    refine ⟨R • 1 + (((D - l) • a + R • 1) + ((D + l) • a + R • 1)),
      X.chartDenZ j (R • 1) * (X.chartDenZ j ((D - l) • a + R • 1) * g j l),
      mul_mem_sections (chartDenZ_mem_sections (Y := X.normalization) j fun c' => by simp)
        (mul_mem_sections (chartDenZ_mem_sections (Y := X.normalization) j (hP3 l hl))
          (hF2 j hj l)), ?_, ?_⟩
    · funext c'
      simp only [hedef, Pi.add_apply, Pi.smul_apply, Pi.one_apply]
      simp only [nsmul_eq_mul, mul_one]
      push_cast [Nat.cast_sub hl]
      ring
    · rw [hT_eq j hj l, hF3 j hj l hl]
      ring
  -- `T_{jl} ∈ R_{e_n}(𝒳)`: the chart criterion and the uniform torsion bound
  have hF5 : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l ≤ D,
      T j l ∈ X.sections e := by
    intro j hj l hl
    refine mem_sections_of_forall_div_chartDenZ fun j' hj' => ?_
    have hAm : A j (n + D + l) ∈ X.chartAlg j := (hc j hj).2 _ (by omega)
    obtain ⟨β', hβ'⟩ := exists_mul_chartDenZ_mem_sections hj hAm
    obtain ⟨M, hM⟩ := exists_nat_ge_of_finite_int fun c' => (β' c' : ℤ) - E1 c'
    set y := X.chartDenZ j E1 * A j (n + D + l) / X.chartDenZ j' E1 with hydef
    have hy : y ∈ X.normalization.chartAlg j' :=
      X.normalization.div_chartDenZ_mem_chartAlg (j := j') hj' (hF3' j hj l hl)
    have hyM : (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ M * y ∈ X.chartAlg j' := by
      have hsec := hβ' (E1 + M • 1) fun c' => by
        have := hM c'
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply]
        simp only [nsmul_eq_mul, mul_one]
        linarith
      have hdiv := div_chartDenZ_mem_chartAlg hj' hsec
      have hid : (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ M * y =
          A j (n + D + l) * X.chartDenZ j (E1 + M • 1) / X.chartDenZ j' (E1 + M • 1) := by
        rw [hydef, chartDenZ_add hj E1 (M • 1), chartDenZ_add hj' E1 (M • 1),
          chartDenZ_nsmul j, chartDenZ_nsmul j', div_pow]
        have h1 := chartDenZ_ne_zero hj' (1 : Fin r → ℤ)
        have h2 := chartDenZ_ne_zero hj' E1
        field_simp
      rw [hid]
      exact hdiv
    have hR := hP2 j j' hj' y hy ⟨M, hyM⟩
    have hid : T j l / X.chartDenZ j' e = (X.chartDenZ j 1 / X.chartDenZ j' 1) ^ R * y := by
      rw [hT_eq j hj l, hydef, he_split, chartDenZ_add hj' (R • 1) E1, chartDenZ_nsmul j,
        chartDenZ_nsmul j', div_pow]
      have h1 := chartDenZ_ne_zero hj' (1 : Fin r → ℤ)
      have h2 := chartDenZ_ne_zero hj' E1
      field_simp
    rw [hid]
    exact hR
  have hTY : ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) → ∀ l ≤ D,
      T j l ∈ X.normalization.sections e := fun j hj l hl => by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (FiniteHom.ofNormalization X).mem_sections (hF5 j hj l hl)
  -- the lower bound, by Lagrange interpolation on a chart with `|z_{j_c}|_w = 1`
  have hF6 : ∀ w : X.normalization.an, ∃ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) ∧
      ∃ l ≤ D, X.normalization.secAbs w.1 a s ^ (n + 2 * D) ≤
        X.normalization.secAbs w.1 e (T j l) := by
    intro w
    obtain ⟨j, hj, hw1⟩ := X.normalization.exists_chartIndex w
    have hjX : ∀ c', X.coord c' (j c') ≠ 0 := hj
    refine ⟨j, hjX, ?_⟩
    let : Algebra ℚ (X.normalization.chartAlg j) :=
      ((algebraMap k (X.normalization.chartAlg j)).comp (algebraMap ℚ k)).toAlgebra
    have hf : s / X.chartDenZ j a ∈ X.normalization.chartAlg j :=
      X.normalization.div_chartDenZ_mem_chartAlg hj hs
    set b : X.normalization.chartAlg j := ⟨s / X.chartDenZ j a, hf⟩ with hbdef
    set c' : Fin D → X.normalization.chartAlg j := fun i => ⟨c j i, (hc j hjX).1 i⟩ with hc'def
    have hspan := pow_mem_span_addPow b D c' n
    set yv := X.normalization.chartMap hj w.1 (val_coordElem_ne_zero_of_eq_one hw1) with hyv
    have h1 : ∀ x, yv.val x ≤ 1 := chartMap_val_le_one_of_eq_one hj hw1
    set L : ℕ → X.normalization.chartAlg j := fun m => b ^ m + ∑ i : Fin D,
      (m.choose (i + 1) : X.normalization.chartAlg j) * c' i * b ^ (m - (i + 1)) with hLdef
    have hcoe : ∀ m, (L m : K) = A j m := fun m => by
      simp only [hLdef, hAdef, addPowSeq, hbdef, hc'def, Subalgebra.coe_add,
        SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
        SubringClass.coe_natCast]
    have hle : yv.val (b ^ (n + 2 * D)) ≤
        (Finset.Icc (n + D) (n + 2 * D)).sup fun m => yv.val (L m) := by
      refine valuation_le_of_mem_span_of_le_one yv.val h1 ?_ hspan
      rintro x ⟨m, hm, rfl⟩
      exact Finset.le_sup (f := fun m => yv.val (L m)) (Finset.mem_Icc.2 hm)
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup (Finset.Icc (n + D) (n + 2 * D))
      ⟨n + D, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩ fun m => yv.val (L m)
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    refine ⟨m - (n + D), by omega, ?_⟩
    have hml : n + D + (m - (n + D)) = m := by omega
    have hsb : X.normalization.secAbs w.1 a s = yv.val b :=
      X.normalization.secAbs_eq_chartMap_of_eq_one hj hw1 ⟨s, hs⟩
    have hTL : X.normalization.secAbs w.1 e (T j (m - (n + D))) = yv.val (L m) := by
      rw [X.normalization.secAbs_eq_chartMap_of_eq_one hj hw1
        ⟨_, hTY j hjX (m - (n + D)) (by omega)⟩]
      congr 1
      apply Subtype.ext
      change T j (m - (n + D)) / X.chartDenZ j e = (L m : K)
      rw [hcoe m]
      simp only [hTdef]
      rw [hml, mul_div_cancel_left₀ _ (chartDenZ_ne_zero hjX e)]
    rw [hsb, hTL, ← map_pow, ← hmeq]
    exact hle
  -- the upper bound
  have hF7 : ∀ w : X.normalization.an, ∀ j : X.ChartIndex, (∀ c', X.coord c' (j c') ≠ 0) →
      ∀ l ≤ D, X.normalization.logSecAbs w.1 e (T j l) ≤
        ((n : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s := by
    intro w j hj l hl
    obtain ⟨e', G, hG, he', hTG⟩ := hF4 j hj l hl
    rw [hTG, he', logSecAbs_mul w.2.2 (pow_mem_sections hs n) hG, logSecAbs_pow w.2.2 hs,
      EReal.coe_natCast]
    exact add_le_of_nonpos_right (logSecAbs_le_zero w.2.2 _ _)
  -- the Fubini–Study data `F_n = (n + 2d)⁻¹ max_{j,l} log |T_{jl}|`
  set good := Finset.univ.filter fun j : X.ChartIndex => ∀ c', X.coord c' (j c') ≠ 0
    with hgood
  have hmem : ∀ p ∈ good ×ˢ Finset.range (D + 1),
      (∀ c', X.coord c' (p.1 c') ≠ 0) ∧ p.2 ≤ D := fun p hp => by
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact ⟨(Finset.mem_filter.1 hp1).2, Nat.lt_succ_iff.1 (Finset.mem_range.1 hp2)⟩
  have hm₀ : 0 < n + 2 * D := by omega
  let Dn : X.FSData (fun c' => (a c' : ℚ) + 3 * R / (n + 2 * D)) :=
    { m := n + 2 * D
      m_pos := hm₀
      deg := e
      deg_eq := fun c' => by
        have hne : (n : ℚ) + 2 * D ≠ 0 := by
          have : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
          positivity
        simp only [hedef, Pi.add_apply, Pi.smul_apply, Pi.one_apply]
        simp only [nsmul_eq_mul, mul_one]
        push_cast
        field_simp
      terms := (good ×ˢ Finset.range (D + 1)).image fun p => (T p.1 p.2, (0 : ℝ))
      mem_sections := fun t ht => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
        exact hF5 p.1 (hmem p hp).1 p.2 (hmem p hp).2 }
  have heval : ∀ w : X.normalization.an, Dn.eval (hX.anHomeomorph w) =
      ((((n + 2 * D : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (good ×ˢ Finset.range (D + 1)).sup
        fun p => X.normalization.logSecAbs w.1 e (T p.1 p.2) := by
    intro w
    rw [FSData.eval_def]
    change _ * ((good ×ˢ Finset.range (D + 1)).image fun p => (T p.1 p.2, (0 : ℝ))).sup
      (fun t => X.termVal e t (hX.anHomeomorph w)) = _
    rw [Finset.sup_image]
    congr 1
    refine Finset.sup_congr rfl fun p hp => ?_
    simp only [Function.comp_apply, termVal_def, EReal.coe_zero, add_zero]
    exact hX.logSecAbs_anHomeomorph w (hF5 p.1 (hmem p hp).1 p.2 (hmem p hp).2)
  have hmR : ((n + 2 * D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  refine ⟨Dn.eval, ⟨Dn, ?_, ?_, fun v => rfl⟩, fun w => ⟨?_, ?_⟩⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
    rfl
  · obtain ⟨j, hj, l, hl, hle⟩ := hF6 X.normalization.triv
    refine ⟨(T j l, 0), Finset.mem_image.2 ⟨(j, l), Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, Finset.mem_range.2 (by omega)⟩, rfl⟩, ?_⟩
    intro h0
    change T j l = 0 at h0
    rw [secAbs_triv hs hs0, one_pow, h0, secAbs_zero] at hle
    exact absurd hle (not_le.2 zero_lt_one)
  · obtain ⟨j, hj, l, hl, hle⟩ := hF6 w
    have hp : (j, l) ∈ good ×ˢ Finset.range (D + 1) :=
      Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩,
        Finset.mem_range.2 (by omega)⟩
    have key : ((((n + 2 * D : ℕ) : ℝ) : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s ≤
        X.normalization.logSecAbs w.1 e (T j l) := natCast_mul_logSecAbs_le_of_pow_le hle
    rw [heval]
    calc X.normalization.logSecAbs w.1 a s
        = ((((n + 2 * D : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
            ((((n + 2 * D : ℕ) : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s) :=
          (ProjBerk.ereal_inv_mul_mul hmR _).symm
      _ ≤ _ := ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
          (key.trans (Finset.le_sup (f := fun p : X.ChartIndex × ℕ =>
            X.normalization.logSecAbs w.1 e (T p.1 p.2)) (b := (j, l)) hp))
  · rw [heval]
    have hsup : ((good ×ˢ Finset.range (D + 1)).sup
        fun p => X.normalization.logSecAbs w.1 e (T p.1 p.2)) ≤
          ((n : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s :=
      Finset.sup_le fun p hp => hF7 w p.1 (hmem p hp).1 p.2 (hmem p hp).2
    calc ((((n + 2 * D : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * _
        ≤ ((((n + 2 * D : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
            (((n : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s) :=
          ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) hsup
      _ = (((n : ℝ) / (n + 2 * D) : ℝ) : EReal) * X.normalization.logSecAbs w.1 a s := by
          rw [ProjBerk.ereal_coe_mul_coe_mul]
          congr 2
          push_cast
          ring

end IsUnibranch

end Unibranch

end MultiModel

end EnvelopeProperty
