/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelCharts
import EnvelopeProperty.Global.FSSystemC

/-!
# Sections of the line bundles `L(a)` on a model, and the cones `C(𝒳)`, `N(𝒳)`

Let `𝒳 = (K, S, z)` be an integral multiprojective model (`EnvelopeProperty.MultiModel`,
`def:gl-model`). This file implements the blueprint nodes `def:gl-sections`, `lem:gl-sections`,
`def:gl-cones` and `lem:gl-cones` of the global chapter `global.tex` of the formalization of
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX, revision
`832e086`, §2, `eq:FS-function`; Boucksom–Jonsson BJ22 `defi:FS`), following plan PLAN-68 §2
items 2–4 and decision D-M1.

## Sections (`def:gl-sections`)

For `a ∈ ℤ^r` the sections `R_a ⊆ K` of `L(a) = ∑_c a_c L_c` are the `f ∈ K` for which there is
`b ∈ ℕ^r` with `a + b ∈ ℕ^r` and `f z̃^β ∈ S_{a+b}` for all `β ∈ Mon(b)`
(`MultiModel.IsAdmissible a b f`, `MultiModel.sections a`, a `k`-submodule of `K`). The degree
`a + b ∈ ℕ^r` is `MultiModel.addDeg a b`. For `v ∈ (Spec S)^an` and an admissible `b`,
`|f|_v = max_{β ∈ Mon(b)} |f z̃^β T^{a+b}|_v` (`MultiModel.secAbsAt`); `MultiModel.secAbs v a f` is
this value for a chosen admissible `b` (and `0` for `f ∉ R_a`), and
`MultiModel.logSecAbs v a f = log |f|_v ∈ [-∞, 0]`.

## Properties of sections (`lem:gl-sections`)

At normalized points (in particular on `𝒳^an`):

1. `MultiModel.secAbs_eq`: `|f|_v` does not depend on the admissible `b` (via the splitting
   `Mon(b + e) = Mon(b) + Mon(e)`, `MultiModel.exists_add_of_monDeg_eq_add`);
   `MultiModel.piece_le_sections`, `MultiModel.secAbs_of_mem_piece`: `S_a ⊆ R_a` and
   `|f|_v = |f T^a|_v` for `a ∈ ℕ^r`.
2. `MultiModel.mul_mem_sections`, `MultiModel.secAbs_mul`, `MultiModel.pow_mem_sections`,
   `MultiModel.secAbs_pow`, `MultiModel.secAbs_add_le`, `MultiModel.secAbs_smul`.
3. `MultiModel.secAbs_le_one`, `MultiModel.secAbs_triv` (`|f|_⋆ = 1` for `f ≠ 0`),
   `MultiModel.continuous_secAbs`, `MultiModel.secAbs_ne_zero` (at points with generic support).
4. `MultiModel.div_chartDenZ_mem_chartAlg`, `MultiModel.secAbs_eq_chartMap`: for a chart `j`,
   `f / z̃_j^a ∈ A_j` (`z̃_j^a = ∏_c (f^{(c)}_{j_c})^{a_c}`, `MultiModel.chartDenZ`) and
   `|f|_v = |f / z̃_j^a|_{ι_j(v)} ∏_c |z^{(c)}_{j_c}|_v^{a_c}` on `U_j`; also the chart-free form
   `MultiModel.secAbs_eq_div_chartMono`: `|f|_v = |f z̃_j^b T^{a+b}|_v / |z_j^b|_v`.

## Cones (`def:gl-cones`, `lem:gl-cones`)

* `MultiModel.semiampleCone : ConvexCone ℚ (Fin r → ℚ)`, the **model-semiample cone** `C(𝒳)`: the
  `a ∈ ℚ^r` with `m a ∈ ℤ^r` for some `m ≥ 1` and finitely many `f_t ∈ R_{m a}` without common
  zero on `𝒳^an` (`MultiModel.IsBasePointFree`). The cone axioms are `lem:gl-cones`(1)
  (products and powers of base point free families), with
  `MultiModel.nonneg_mem_semiampleCone`: `ℚ^r_{≥0} ⊆ C(𝒳)` (monomials in the coordinates) and
  `MultiModel.mem_semiampleCone_of_le`: `C(𝒳) + ℚ^r_{≥0} ⊆ C(𝒳)`.
* `MultiModel.nefCone`, the **model-nef cone** `N(𝒳) = C̄(𝒳) ⊆ ℝ^r`, a closed convex cone containing
  `ℝ^r_{≥0}` (`MultiModel.isClosed_nefCone`, `MultiModel.add_mem_nefCone`,
  `MultiModel.smul_mem_nefCone`, `MultiModel.mem_nefCone_of_nonneg`); rational `a > θ ∈ N(𝒳)` lie in
  `C(𝒳)` (`MultiModel.mem_semiampleCone_of_lt`), and `lem:gl-cones`(3) is
  `EnvelopeProperty.exists_mem_ge_tendsto_of_mem_ratClosure`.
* `MultiModel.IsBasePointFree.sup_secAbs_eq_one` (`lem:gl-cones`(2)): if `f_t ∈ R_a` have no
  common zero on `𝒳^an`, then `max_t |f_t|_v = 1` for every `v ∈ 𝒳^an`. The proof is the
  blueprint's: on a chart `A_j` with `|z^{(c)}_{j_c}|_v = 1`, the `f_t / z̃_j^a` have no common
  zero on `(Spec A_j)^an`, hence generate the unit ideal
  (`EnvelopeProperty.Berk.span_eq_top_of_forall_exists_val_ne_zero`: the trivial point of
  `A_j / 𝔪` is a common zero otherwise), and elements of `A_j` have norm `≤ 1` at `ι_j(v)`.

A class is *model-ample* (`def:gl-cones`) if all its coordinates are positive; no definition is
introduced for this condition.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### A Nullstellensatz for `(Spec A)^an` -/

namespace Berk

/-- If finitely or infinitely many elements of a `k`-algebra `A` have no common zero on
`(Spec A)^an`, they generate the unit ideal: otherwise a maximal ideal `𝔪` contains them, and the
trivial point of `A / 𝔪`, pulled back to `A`, is a common zero. -/
theorem span_eq_top_of_forall_exists_val_ne_zero {k : Type*} [Field k] {A : Type*} [CommRing A]
    [Algebra k A] (s : Set A) (h : ∀ y : Berk k A, ∃ g ∈ s, y.val g ≠ 0) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
  have := hm.isPrime
  obtain ⟨g, hg, hy⟩ := h (Berk.comap (Ideal.Quotient.mkₐ k m) Berk.triv)
  apply hy
  rw [comap_val_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 (hsm (Ideal.subset_span hg)), map_zero]

end Berk

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-! ### Monomials in the coordinates -/

/-- `Mon(0) = {0}`. -/
theorem monSet_zero : X.monSet 0 = {0} := by
  ext β
  rw [mem_monSet, Finset.mem_singleton]
  refine ⟨fun h => ?_, fun h => by rw [h, monDeg_zero]⟩
  have h' := congrArg Finsupp.degree h
  rw [monDeg, Finsupp.degree_mapDomain, map_zero] at h'
  exact (Finsupp.degree_eq_zero_iff β).1 h'

variable {X}

/-- One step of the splitting: if `deg β = e_c + e`, then `β = e_{(c, j)} + γ` with
`deg γ = e`. -/
theorem exists_eq_single_add_of_monDeg_eq {β : X.CoordIndex →₀ ℕ} {c : Fin r}
    {e : Fin r →₀ ℕ} (h : X.monDeg β = Finsupp.single c 1 + e) :
    ∃ (j : Fin (X.M c + 1)) (γ : X.CoordIndex →₀ ℕ),
      β = Finsupp.single ⟨c, j⟩ 1 + γ ∧ X.monDeg γ = e := by
  classical
  have hc : X.monDeg β c ≠ 0 := by
    rw [h, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  obtain ⟨i, hi, hic⟩ : ∃ i ∈ β.support, i.1 = c := by
    have := Finsupp.mapDomain_support (f := Sigma.fst) (s := β)
      (show c ∈ (Finsupp.mapDomain Sigma.fst β).support from Finsupp.mem_support_iff.2 hc)
    simpa using this
  obtain ⟨c', j⟩ := i
  simp only at hic
  subst hic
  have hle : Finsupp.single (⟨c', j⟩ : X.CoordIndex) 1 ≤ β :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
  refine ⟨j, β - Finsupp.single ⟨c', j⟩ 1, (add_tsub_cancel_of_le hle).symm, ?_⟩
  have h2 := X.monDeg_add (Finsupp.single ⟨c', j⟩ 1) (β - Finsupp.single ⟨c', j⟩ 1)
  rw [add_tsub_cancel_of_le hle, h, monDeg_single] at h2
  exact (add_left_cancel h2).symm

/-- **Splitting of monomials**: `Mon(b + e) = Mon(b) + Mon(e)`; every `β` of degree `b + e` is
`β₁ + β₂` with `deg β₁ = b` and `deg β₂ = e`. -/
theorem exists_add_of_monDeg_eq_add {β : X.CoordIndex →₀ ℕ} {b e : Fin r →₀ ℕ}
    (h : X.monDeg β = b + e) :
    ∃ β₁ β₂ : X.CoordIndex →₀ ℕ, β = β₁ + β₂ ∧ X.monDeg β₁ = b ∧ X.monDeg β₂ = e := by
  induction b using Finsupp.induction_linear generalizing β e with
  | zero => exact ⟨0, β, by simp, by simp, by simpa using h⟩
  | add f g hf hg =>
    obtain ⟨β₁, β', rfl, h₁, h'⟩ := hf (β := β) (e := g + e) (by rw [h, add_assoc])
    obtain ⟨β₂, β₃, rfl, h₂, h₃⟩ := hg h'
    exact ⟨β₁ + β₂, β₃, by rw [add_assoc], by rw [X.monDeg_add, h₁, h₂], h₃⟩
  | single c n =>
    induction n generalizing β e with
    | zero => exact ⟨0, β, by simp, by simp, by simpa using h⟩
    | succ n ih =>
      have h' : X.monDeg β = Finsupp.single c 1 + (Finsupp.single c n + e) := by
        rw [h, Finsupp.single_add]
        abel
      obtain ⟨j, γ, rfl, hγ⟩ := exists_eq_single_add_of_monDeg_eq h'
      obtain ⟨γ₁, γ₂, rfl, h₁, h₂⟩ := ih hγ
      refine ⟨Finsupp.single ⟨c, j⟩ 1 + γ₁, γ₂, by rw [add_assoc], ?_, h₂⟩
      rw [X.monDeg_add, monDeg_single, h₁, ← Finsupp.single_add, Nat.add_comm]

theorem zCoeff_mem_piece_of_mem_monSet {β : X.CoordIndex →₀ ℕ} {b : Fin r →₀ ℕ}
    (hβ : β ∈ X.monSet b) : X.zCoeff β ∈ X.piece b :=
  X.mem_monSet.1 hβ ▸ X.zCoeff_mem_piece β

theorem ofPiece_zCoeff_of_mem_monSet {β : X.CoordIndex →₀ ℕ} {b : Fin r →₀ ℕ}
    (hβ : β ∈ X.monSet b) : X.ofPiece (zCoeff_mem_piece_of_mem_monSet hβ) = X.zMon β :=
  X.ofPiece_congr _ _ (X.mem_monSet.1 hβ).symm rfl

theorem ofPiece_eq_zero_iff {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    X.ofPiece hf = 0 ↔ f = 0 := by
  constructor
  · intro h
    have := congrArg (fun p : X.S => (p : MvPolynomial (Fin r) K)) h
    simpa only [coe_ofPiece, ZeroMemClass.coe_zero, monomial_eq_zero] using this
  · rintro rfl
    exact X.ofPiece_zero a

/-- A monomial `z^β` that does not vanish at some point has a nonzero coefficient `z̃^β`. -/
theorem zCoeff_ne_zero_of_val_ne_zero {v : Berk k X.S} {β : X.CoordIndex →₀ ℕ}
    (h : v.val (X.zMon β) ≠ 0) : X.zCoeff β ≠ 0 := by
  intro h0
  apply h
  rw [show X.zMon β = 0 from (ofPiece_eq_zero_iff _).2 h0, map_zero]

variable (X)

/-- The monomial `z_j^b = ∏_c (z^{(c)}_{j_c})^{b_c}` of a chart index, as a multi-index. -/
def chartMultiIndex (j : X.ChartIndex) (b : Fin r →₀ ℕ) : X.CoordIndex →₀ ℕ :=
  ∑ c, Finsupp.single ⟨c, j c⟩ (b c)

theorem monDeg_chartMultiIndex (j : X.ChartIndex) (b : Fin r →₀ ℕ) :
    X.monDeg (X.chartMultiIndex j b) = b := by
  rw [chartMultiIndex, monDeg, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  exact Finsupp.univ_sum_single b

theorem chartMultiIndex_mem_monSet (j : X.ChartIndex) (b : Fin r →₀ ℕ) :
    X.chartMultiIndex j b ∈ X.monSet b :=
  X.mem_monSet.2 (X.monDeg_chartMultiIndex j b)

theorem zCoeff_chartMultiIndex (j : X.ChartIndex) (b : Fin r →₀ ℕ) :
    X.zCoeff (X.chartMultiIndex j b) = X.chartDen j b := by
  rw [chartMultiIndex, zCoeff, ← Finsupp.prod_finsetSum_index (fun _ => pow_zero _)
    fun _ _ _ => pow_add _ _ _, chartDen]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact Finsupp.prod_single_index (pow_zero _)

theorem zMon_chartMultiIndex (j : X.ChartIndex) (b : Fin r →₀ ℕ) :
    X.zMon (X.chartMultiIndex j b) = X.chartMono j b :=
  X.ofPiece_congr _ _ (X.monDeg_chartMultiIndex j b) (X.zCoeff_chartMultiIndex j b)

/-! ### Values on homogeneous elements -/

variable {X}

theorem homNorm_of_notMem (v : Berk k X.S) {a : Fin r →₀ ℕ} {f : K} (hf : f ∉ X.piece a) :
    X.homNorm v a f = 0 :=
  dif_neg hf

theorem homNorm_apply_zero (v : Berk k X.S) (a : Fin r →₀ ℕ) : X.homNorm v a 0 = 0 := by
  rw [X.homNorm_of_mem v (Submodule.zero_mem _), X.ofPiece_zero, map_zero]

theorem homNorm_mul (v : Berk k X.S) {a b : Fin r →₀ ℕ} {f g : K} (hf : f ∈ X.piece a)
    (hg : g ∈ X.piece b) : X.homNorm v (a + b) (f * g) = X.homNorm v a f * X.homNorm v b g := by
  rw [X.homNorm_of_mem v (mul_mem_piece hf hg), X.homNorm_of_mem v hf, X.homNorm_of_mem v hg,
    X.ofPiece_mul, map_mul]

theorem homNorm_add_le_max (v : Berk k X.S) {a : Fin r →₀ ℕ} {f g : K}
    (hf : f ∈ X.piece a) (hg : g ∈ X.piece a) :
    X.homNorm v a (f + g) ≤ max (X.homNorm v a f) (X.homNorm v a g) := by
  rw [X.homNorm_of_mem v (Submodule.add_mem _ hf hg), X.homNorm_of_mem v hf,
    X.homNorm_of_mem v hg, X.ofPiece_add]
  exact v.val.map_add _ _

theorem ofPiece_smul {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) (c : k) :
    X.ofPiece (Submodule.smul_mem _ c hf) = c • X.ofPiece hf :=
  Subtype.ext (by rw [coe_ofPiece, Subalgebra.coe_smul, coe_ofPiece, smul_monomial])

theorem homNorm_smul (v : Berk k X.S) {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) {c : k}
    (hc : c ≠ 0) : X.homNorm v a (c • f) = X.homNorm v a f := by
  rw [X.homNorm_of_mem v (Submodule.smul_mem _ c hf), X.homNorm_of_mem v hf, ofPiece_smul,
    Algebra.smul_def, map_mul, v.val_algebraMap c hc, one_mul]

theorem homNorm_le_one {v : Berk k X.S} (hv : X.IsNormalized v) (a : Fin r →₀ ℕ) (f : K) :
    X.homNorm v a f ≤ 1 := by
  by_cases hf : f ∈ X.piece a
  · rw [X.homNorm_of_mem v hf]
    exact hv.val_le_one _
  · rw [homNorm_of_notMem v hf]
    exact zero_le_one

variable (X) in
theorem continuous_homNorm (a : Fin r →₀ ℕ) (f : K) :
    Continuous fun v : Berk k X.S => X.homNorm v a f := by
  by_cases hf : f ∈ X.piece a
  · simp only [X.homNorm_of_mem _ hf]
    exact Berk.continuous_val_apply _
  · simp only [homNorm_of_notMem _ hf]
    exact continuous_const

/-! ### Degrees `a + b` -/

/-- The degree `a + b ∈ ℕ^r` of `f z̃^β T^{a + b}`, for `a ∈ ℤ^r` and `b ∈ ℕ^r` with `a + b ≥ 0`
(the coordinates are truncated at `0`). -/
def addDeg (a : Fin r → ℤ) (b : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c => (a c + b c).toNat

theorem addDeg_apply (a : Fin r → ℤ) (b : Fin r →₀ ℕ) (c : Fin r) :
    addDeg a b c = (a c + b c).toNat :=
  rfl

theorem addDeg_add {a : Fin r → ℤ} {b : Fin r →₀ ℕ} (hb : ∀ c, 0 ≤ a c + b c)
    (e : Fin r →₀ ℕ) : addDeg a (b + e) = addDeg a b + e := by
  ext c
  have := hb c
  simp only [addDeg_apply, Finsupp.add_apply, Nat.cast_add]
  omega

theorem addDeg_add_add {a a' : Fin r → ℤ} {b b' : Fin r →₀ ℕ} (hb : ∀ c, 0 ≤ a c + b c)
    (hb' : ∀ c, 0 ≤ a' c + b' c) : addDeg (a + a') (b + b') = addDeg a b + addDeg a' b' := by
  ext c
  have := hb c
  have := hb' c
  simp only [addDeg_apply, Finsupp.add_apply, Nat.cast_add, Pi.add_apply]
  omega

theorem addDeg_zero_of_eq {a : Fin r → ℤ} {d : Fin r →₀ ℕ} (had : ∀ c, a c = d c) :
    addDeg a 0 = d := by
  ext c
  rw [addDeg_apply, had c]
  simp

/-- For every `a ∈ ℤ^r` some `b ∈ ℕ^r` has `a + b ≥ 0`. -/
theorem exists_nonneg_add (a : Fin r → ℤ) : ∃ b : Fin r →₀ ℕ, ∀ c, 0 ≤ a c + b c :=
  ⟨Finsupp.equivFunOnFinite.symm fun c => (-a c).toNat, fun c => by
    change 0 ≤ a c + ((-a c).toNat : ℤ)
    omega⟩

/-- `∏_c x_c^{(a + b)_c} = ∏_c x_c^{a_c} ∏_c x_c^{b_c}` for nonzero `x_c` (`a_c ∈ ℤ`). -/
theorem prod_pow_addDeg {G : Type*} [CommGroupWithZero G] {x : Fin r → G} (hx : ∀ c, x c ≠ 0)
    {a : Fin r → ℤ} {b : Fin r →₀ ℕ} (hb : ∀ c, 0 ≤ a c + b c) :
    ∏ c, x c ^ addDeg a b c = (∏ c, x c ^ a c) * ∏ c, x c ^ b c := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← zpow_natCast, ← zpow_natCast (x c) (b c), addDeg_apply, Int.toNat_of_nonneg (hb c),
    zpow_add₀ (hx c)]

/-! ### Admissible degrees and sections (`def:gl-sections`) -/

variable (X) in
/-- `b ∈ ℕ^r` is **admissible** for `f ∈ K` in degree `a ∈ ℤ^r` (`def:gl-sections`):
`a + b ≥ 0` and `f z̃^β ∈ S_{a+b}` for all `β ∈ Mon(b)`. -/
def IsAdmissible (a : Fin r → ℤ) (b : Fin r →₀ ℕ) (f : K) : Prop :=
  (∀ c, 0 ≤ a c + b c) ∧ ∀ β ∈ X.monSet b, f * X.zCoeff β ∈ X.piece (addDeg a b)

variable {a a' : Fin r → ℤ} {b b' e : Fin r →₀ ℕ} {f g : K}

theorem IsAdmissible.nonneg (h : X.IsAdmissible a b f) (c : Fin r) : 0 ≤ a c + b c :=
  h.1 c

theorem IsAdmissible.mul_zCoeff_mem (h : X.IsAdmissible a b f) {β : X.CoordIndex →₀ ℕ}
    (hβ : β ∈ X.monSet b) : f * X.zCoeff β ∈ X.piece (addDeg a b) :=
  h.2 β hβ

/-- `f z̃_j^b ∈ S_{a+b}` for an admissible `b` (the monomial `z_j^b`). -/
theorem IsAdmissible.mul_chartDen_mem (h : X.IsAdmissible a b f) (j : X.ChartIndex) :
    f * X.chartDen j b ∈ X.piece (addDeg a b) := by
  have := h.mul_zCoeff_mem (X.chartMultiIndex_mem_monSet j b)
  rwa [zCoeff_chartMultiIndex] at this

/-- If `b` is admissible, so is `b + e`: `f z̃^{β + γ} = (f z̃^β) z̃^γ`. -/
theorem IsAdmissible.add_right (h : X.IsAdmissible a b f) (e : Fin r →₀ ℕ) :
    X.IsAdmissible a (b + e) f := by
  refine ⟨fun c => ?_, fun β hβ => ?_⟩
  · have := h.nonneg c
    simp only [Finsupp.add_apply, Nat.cast_add]
    omega
  · obtain ⟨β₁, β₂, rfl, h₁, h₂⟩ := exists_add_of_monDeg_eq_add (X.mem_monSet.1 hβ)
    rw [addDeg_add h.1, X.zCoeff_add, ← mul_assoc, ← h₂]
    exact mul_mem_piece (h.mul_zCoeff_mem (X.mem_monSet.2 h₁)) (X.zCoeff_mem_piece β₂)

/-- Admissibility is inherited by larger degrees. -/
theorem IsAdmissible.mono (h : X.IsAdmissible a b f) (hbb' : b ≤ b') : X.IsAdmissible a b' f := by
  rw [← add_tsub_cancel_of_le hbb']
  exact h.add_right _

variable (X) in
theorem isAdmissible_zero (hb : ∀ c, 0 ≤ a c + b c) : X.IsAdmissible a b 0 :=
  ⟨hb, fun _ _ => by rw [zero_mul]; exact Submodule.zero_mem _⟩

theorem IsAdmissible.add (hf : X.IsAdmissible a b f) (hg : X.IsAdmissible a b g) :
    X.IsAdmissible a b (f + g) :=
  ⟨hf.1, fun β hβ => by
    rw [add_mul]
    exact Submodule.add_mem _ (hf.2 β hβ) (hg.2 β hβ)⟩

theorem IsAdmissible.smul (hf : X.IsAdmissible a b f) (c : k) : X.IsAdmissible a b (c • f) :=
  ⟨hf.1, fun β hβ => by
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c (hf.2 β hβ)⟩

/-- Products: if `b`, `b'` are admissible for `f ∈ R_a`, `g ∈ R_{a'}`, then `b + b'` is admissible
for `f g ∈ R_{a + a'}` (`lem:gl-sections`(2)). -/
theorem IsAdmissible.mul (hf : X.IsAdmissible a b f) (hg : X.IsAdmissible a' b' g) :
    X.IsAdmissible (a + a') (b + b') (f * g) := by
  refine ⟨fun c => ?_, fun β hβ => ?_⟩
  · have := hf.nonneg c
    have := hg.nonneg c
    simp only [Pi.add_apply, Finsupp.add_apply, Nat.cast_add]
    omega
  · obtain ⟨β₁, β₂, rfl, h₁, h₂⟩ := exists_add_of_monDeg_eq_add (X.mem_monSet.1 hβ)
    rw [addDeg_add_add hf.1 hg.1, X.zCoeff_add,
      show f * g * (X.zCoeff β₁ * X.zCoeff β₂) = (f * X.zCoeff β₁) * (g * X.zCoeff β₂) by ring]
    exact mul_mem_piece (hf.mul_zCoeff_mem (X.mem_monSet.2 h₁))
      (hg.mul_zCoeff_mem (X.mem_monSet.2 h₂))

/-- For `f ∈ S_d` (`d ∈ ℕ^r`) the degree `b = 0` is admissible in degree `d`. -/
theorem isAdmissible_zero_of_mem_piece {d : Fin r →₀ ℕ} (had : ∀ c, a c = d c)
    (hf : f ∈ X.piece d) : X.IsAdmissible a 0 f :=
  ⟨fun c => by simp [had c], fun β hβ => by
    rw [X.monSet_zero, Finset.mem_singleton] at hβ
    rw [hβ, zCoeff_zero, mul_one, addDeg_zero_of_eq had]
    exact hf⟩

variable (X) in
/-- The **sections** `R_a ⊆ K` of `L(a)`, `a ∈ ℤ^r` (`def:gl-sections`): the `f ∈ K` with an
admissible `b ∈ ℕ^r`. -/
def sections (a : Fin r → ℤ) : Submodule k K where
  carrier := {f | ∃ b, X.IsAdmissible a b f}
  add_mem' := by
    rintro f g ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b + b', (hb.mono le_self_add).add (hb'.mono le_add_self)⟩
  zero_mem' := by
    obtain ⟨b, hb⟩ := exists_nonneg_add a
    exact ⟨b, X.isAdmissible_zero hb⟩
  smul_mem' c f := by
    rintro ⟨b, hb⟩
    exact ⟨b, hb.smul c⟩

theorem mem_sections : f ∈ X.sections a ↔ ∃ b, X.IsAdmissible a b f :=
  Iff.rfl

theorem IsAdmissible.mem_sections (h : X.IsAdmissible a b f) : f ∈ X.sections a :=
  ⟨b, h⟩

/-- `S_d ⊆ R_d` for `d ∈ ℕ^r` (`lem:gl-sections`(1)). -/
theorem mem_sections_of_mem_piece {d : Fin r →₀ ℕ} (had : ∀ c, a c = d c) (hf : f ∈ X.piece d) :
    f ∈ X.sections a :=
  (isAdmissible_zero_of_mem_piece had hf).mem_sections

variable (X) in
/-- `S_d ⊆ R_d` for `d ∈ ℕ^r` (`lem:gl-sections`(1)). -/
theorem piece_le_sections (d : Fin r →₀ ℕ) : X.piece d ≤ X.sections fun c => (d c : ℤ) :=
  fun _ hf => mem_sections_of_mem_piece (fun _ => rfl) hf

/-- `R_a R_{a'} ⊆ R_{a + a'}` (`lem:gl-sections`(2)). -/
theorem mul_mem_sections (hf : f ∈ X.sections a) (hg : g ∈ X.sections a') :
    f * g ∈ X.sections (a + a') := by
  obtain ⟨b, hb⟩ := hf
  obtain ⟨b', hb'⟩ := hg
  exact (hb.mul hb').mem_sections

variable (X) in
theorem one_mem_sections_zero : (1 : K) ∈ X.sections 0 :=
  mem_sections_of_mem_piece (d := 0) (fun _ => rfl) X.one_mem_piece_zero

/-- `R_a^n ⊆ R_{n a}`. -/
theorem pow_mem_sections (hf : f ∈ X.sections a) (n : ℕ) : f ^ n ∈ X.sections (n • a) := by
  induction n with
  | zero => simpa using X.one_mem_sections_zero
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_sections ih hf

/-! ### The absolute value of a section -/

variable (X) in
/-- `max_{β ∈ Mon(b)} |f z̃^β T^{a+b}|_v` (`def:gl-sections`), for a degree `b`. -/
def secAbsAt (v : Berk k X.S) (a : Fin r → ℤ) (b : Fin r →₀ ℕ) (f : K) : ℝ≥0 :=
  (X.monSet b).sup fun β => X.homNorm v (addDeg a b) (f * X.zCoeff β)

open Classical in
variable (X) in
/-- The **absolute value `|f|_v` of a section** `f ∈ R_a` at `v ∈ (Spec S)^an`
(`def:gl-sections`): `max_{β ∈ Mon(b)} |f z̃^β T^{a+b}|_v` for a chosen admissible `b` (`0` for
`f ∉ R_a`). At normalized points the value does not depend on `b` (`secAbs_eq`). -/
def secAbs (v : Berk k X.S) (a : Fin r → ℤ) (f : K) : ℝ≥0 :=
  if h : f ∈ X.sections a then X.secAbsAt v a (mem_sections.1 h).choose f else 0

variable (X) in
/-- `log |f|_v ∈ [-∞, +∞)` for a section `f ∈ R_a` (`def:gl-sections`). -/
def logSecAbs (v : Berk k X.S) (a : Fin r → ℤ) (f : K) : EReal :=
  ENNReal.log (X.secAbs v a f : ℝ≥0∞)

theorem secAbs_of_notMem (v : Berk k X.S) (h : f ∉ X.sections a) : X.secAbs v a f = 0 :=
  dif_neg h

/-- Each term `|f z̃^β T^{a+b}|_v`, `β ∈ Mon(b)`, is at most `secAbsAt v a b f`. -/
theorem le_secAbsAt (v : Berk k X.S) {β : X.CoordIndex →₀ ℕ} (hβ : β ∈ X.monSet b) :
    X.homNorm v (addDeg a b) (f * X.zCoeff β) ≤ X.secAbsAt v a b f :=
  Finset.le_sup (f := fun β => X.homNorm v (addDeg a b) (f * X.zCoeff β)) hβ

/-- The term `f z̃^{β + γ}` of degree `b + e`. -/
theorem homNorm_mul_zCoeff_add (v : Berk k X.S) (h : X.IsAdmissible a b f)
    {β : X.CoordIndex →₀ ℕ} (hβ : β ∈ X.monSet b) (γ : X.CoordIndex →₀ ℕ) :
    X.homNorm v (addDeg a (b + X.monDeg γ)) (f * X.zCoeff (β + γ)) =
      X.homNorm v (addDeg a b) (f * X.zCoeff β) * v.val (X.zMon γ) := by
  rw [addDeg_add h.1, X.zCoeff_add, ← mul_assoc,
    homNorm_mul v (h.mul_zCoeff_mem hβ) (X.zCoeff_mem_piece γ),
    X.homNorm_of_mem v (X.zCoeff_mem_piece γ)]
  rfl

/-- `|f|` does not change when `b` is replaced by `b + e` (`lem:gl-sections`(1)): by
multiplicativity, `max_{β + γ} |f z̃^{β+γ} T^{a+b+e}| = max_β |f z̃^β T^{a+b}| · max_γ |z^γ|`, and
`max_{γ ∈ Mon(e)} |z^γ|_v = 1` at a normalized point. -/
theorem secAbsAt_add_right {v : Berk k X.S} (hv : X.IsNormalized v) (h : X.IsAdmissible a b f)
    (e : Fin r →₀ ℕ) : X.secAbsAt v a (b + e) f = X.secAbsAt v a b f := by
  apply le_antisymm
  · refine Finset.sup_le fun β hβ => ?_
    obtain ⟨β₁, β₂, rfl, h₁, h₂⟩ := exists_add_of_monDeg_eq_add (X.mem_monSet.1 hβ)
    have hβ₁ : β₁ ∈ X.monSet b := X.mem_monSet.2 h₁
    have := homNorm_mul_zCoeff_add v h hβ₁ β₂
    rw [h₂] at this
    rw [this]
    calc X.homNorm v (addDeg a b) (f * X.zCoeff β₁) * v.val (X.zMon β₂)
        ≤ X.homNorm v (addDeg a b) (f * X.zCoeff β₁) * 1 :=
          mul_le_mul_right (hv.val_zMon_le_one β₂) _
      _ ≤ X.secAbsAt v a b f := by
          rw [mul_one]
          exact le_secAbsAt v hβ₁
  · obtain ⟨γ, hγ, hγ1⟩ := hv.exists_val_zMon_eq_one e
    refine Finset.sup_le fun β hβ => ?_
    have hmem : β + γ ∈ X.monSet (b + e) :=
      X.mem_monSet.2 (by rw [X.monDeg_add, X.mem_monSet.1 hβ, X.mem_monSet.1 hγ])
    have := homNorm_mul_zCoeff_add v h hβ γ
    rw [X.mem_monSet.1 hγ, hγ1, mul_one] at this
    rw [← this]
    exact le_secAbsAt v hmem

/-- **Independence of the admissible degree** (`lem:gl-sections`(1)). -/
theorem secAbsAt_eq_secAbsAt {v : Berk k X.S} (hv : X.IsNormalized v) (h : X.IsAdmissible a b f)
    (h' : X.IsAdmissible a b' f) : X.secAbsAt v a b f = X.secAbsAt v a b' f := by
  rw [← secAbsAt_add_right hv h b', ← secAbsAt_add_right hv h' b, add_comm]

/-- **`lem:gl-sections`(1)**: at a normalized point, `|f|_v = max_{β ∈ Mon(b)} |f z̃^β T^{a+b}|_v`
for **every** admissible `b`. -/
theorem secAbs_eq {v : Berk k X.S} (hv : X.IsNormalized v) (h : X.IsAdmissible a b f) :
    X.secAbs v a f = X.secAbsAt v a b f := by
  rw [secAbs, dif_pos h.mem_sections]
  exact secAbsAt_eq_secAbsAt hv (mem_sections.1 h.mem_sections).choose_spec h

/-- **`lem:gl-sections`(1)**: for `f ∈ S_d`, `d ∈ ℕ^r`, `|f|_v = |f T^d|_v`. -/
theorem secAbs_of_mem_piece {v : Berk k X.S} (hv : X.IsNormalized v) {d : Fin r →₀ ℕ}
    (had : ∀ c, a c = d c) (hf : f ∈ X.piece d) : X.secAbs v a f = v.val (X.ofPiece hf) := by
  rw [secAbs_eq hv (isAdmissible_zero_of_mem_piece had hf), secAbsAt, X.monSet_zero,
    Finset.sup_singleton, zCoeff_zero, mul_one, addDeg_zero_of_eq had, X.homNorm_of_mem v hf]

theorem secAbs_zero (v : Berk k X.S) (a : Fin r → ℤ) : X.secAbs v a 0 = 0 := by
  rw [secAbs, dif_pos (Submodule.zero_mem _), secAbsAt]
  simp only [zero_mul, homNorm_apply_zero]
  exact le_antisymm (Finset.sup_le fun _ _ => le_rfl) zero_le

/-- **`lem:gl-sections`(2)**: `|f g|_v = |f|_v |g|_v` for `f ∈ R_a`, `g ∈ R_{a'}`. -/
theorem secAbs_mul {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a)
    (hg : g ∈ X.sections a') : X.secAbs v (a + a') (f * g) = X.secAbs v a f * X.secAbs v a' g := by
  obtain ⟨b, hb⟩ := hf
  obtain ⟨b', hb'⟩ := hg
  rw [secAbs_eq hv (hb.mul hb'), secAbs_eq hv hb, secAbs_eq hv hb']
  have key : ∀ β₁ ∈ X.monSet b, ∀ β₂ ∈ X.monSet b',
      X.homNorm v (addDeg (a + a') (b + b')) (f * g * X.zCoeff (β₁ + β₂)) =
        X.homNorm v (addDeg a b) (f * X.zCoeff β₁) * X.homNorm v (addDeg a' b') (g * X.zCoeff β₂) :=
    fun β₁ hβ₁ β₂ hβ₂ => by
      rw [addDeg_add_add hb.1 hb'.1, ← homNorm_mul v (hb.mul_zCoeff_mem hβ₁)
        (hb'.mul_zCoeff_mem hβ₂), X.zCoeff_add,
        show f * g * (X.zCoeff β₁ * X.zCoeff β₂) = f * X.zCoeff β₁ * (g * X.zCoeff β₂) by ring]
  apply le_antisymm
  · refine Finset.sup_le fun β hβ => ?_
    obtain ⟨β₁, β₂, rfl, h₁, h₂⟩ := exists_add_of_monDeg_eq_add (X.mem_monSet.1 hβ)
    rw [key β₁ (X.mem_monSet.2 h₁) β₂ (X.mem_monSet.2 h₂)]
    exact mul_le_mul' (le_secAbsAt v (X.mem_monSet.2 h₁)) (le_secAbsAt v (X.mem_monSet.2 h₂))
  · rw [secAbsAt, NNReal.finset_sup_mul]
    refine Finset.sup_le fun β₁ hβ₁ => ?_
    rw [secAbsAt, NNReal.mul_finset_sup]
    refine Finset.sup_le fun β₂ hβ₂ => ?_
    rw [← key β₁ hβ₁ β₂ hβ₂]
    exact le_secAbsAt v
      (X.mem_monSet.2 (by rw [X.monDeg_add, X.mem_monSet.1 hβ₁, X.mem_monSet.1 hβ₂]))

/-- `|1|_v = 1` at a normalized point. -/
theorem secAbs_one {v : Berk k X.S} (hv : X.IsNormalized v) : X.secAbs v 0 1 = 1 := by
  rw [secAbs_of_mem_piece (a := 0) hv (d := 0) (fun _ => by simp) X.one_mem_piece_zero,
    X.ofPiece_one, map_one]

/-- `|f^n|_v = |f|_v^n`. -/
theorem secAbs_pow {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a) (n : ℕ) :
    X.secAbs v (n • a) (f ^ n) = X.secAbs v a f ^ n := by
  induction n with
  | zero => simpa using secAbs_one hv
  | succ n ih =>
    rw [succ_nsmul, pow_succ, secAbs_mul hv (pow_mem_sections hf n) hf, ih, pow_succ]

/-- **`lem:gl-sections`(2)**: the ultrametric inequality `|f + g|_v ≤ max(|f|_v, |g|_v)` for
`f, g ∈ R_a`. -/
theorem secAbs_add_le {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a)
    (hg : g ∈ X.sections a) :
    X.secAbs v a (f + g) ≤ max (X.secAbs v a f) (X.secAbs v a g) := by
  obtain ⟨b, hb⟩ := hf
  obtain ⟨b', hb'⟩ := hg
  have h₁ : X.IsAdmissible a (b + b') f := hb.mono le_self_add
  have h₂ : X.IsAdmissible a (b + b') g := hb'.mono le_add_self
  rw [secAbs_eq hv (h₁.add h₂), secAbs_eq hv h₁, secAbs_eq hv h₂]
  refine Finset.sup_le fun β hβ => ?_
  rw [add_mul]
  exact (homNorm_add_le_max v (h₁.mul_zCoeff_mem hβ) (h₂.mul_zCoeff_mem hβ)).trans
    (max_le_max (le_secAbsAt v hβ) (le_secAbsAt v hβ))

/-- **`lem:gl-sections`(2)**: `|λ f|_v = |f|_v` for `λ ∈ k^×`. -/
theorem secAbs_smul {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a) {c : k}
    (hc : c ≠ 0) : X.secAbs v a (c • f) = X.secAbs v a f := by
  obtain ⟨b, hb⟩ := hf
  rw [secAbs_eq hv (hb.smul c), secAbs_eq hv hb, secAbsAt, secAbsAt]
  refine Finset.sup_congr rfl fun β hβ => ?_
  rw [smul_mul_assoc, homNorm_smul v (hb.mul_zCoeff_mem hβ) hc]

/-- **`lem:gl-sections`(3)**: `|f|_v ≤ 1` on `𝒳^an`. -/
theorem secAbs_le_one {v : Berk k X.S} (hv : X.IsNormalized v) (a : Fin r → ℤ) (f : K) :
    X.secAbs v a f ≤ 1 := by
  by_cases h : f ∈ X.sections a
  · rw [secAbs, dif_pos h]
    exact Finset.sup_le fun β _ => homNorm_le_one hv _ _
  · rw [secAbs_of_notMem v h]
    exact zero_le_one

/-- At a normalized point, some `β ∈ Mon(b)` has `|f z̃^β T^{a+b}|_v ≠ 0` as soon as `f ≠ 0` and
`v` has generic support; at `⋆` such a term has absolute value `1`. -/
theorem exists_mem_monSet_ne_zero {v : Berk k X.S} (hv : X.IsNormalized v) (b : Fin r →₀ ℕ) :
    ∃ β ∈ X.monSet b, X.zCoeff β ≠ 0 ∧ v.val (X.zMon β) = 1 := by
  obtain ⟨β, hβ, h1⟩ := hv.exists_val_zMon_eq_one b
  exact ⟨β, hβ, zCoeff_ne_zero_of_val_ne_zero (h1 ▸ one_ne_zero), h1⟩

/-- **`lem:gl-sections`(3)**: `|f|_⋆ = 1` for `0 ≠ f ∈ R_a`. -/
theorem secAbs_triv (hf : f ∈ X.sections a) (hf0 : f ≠ 0) :
    X.secAbs (X.triv : Berk k X.S) a f = 1 := by
  obtain ⟨b, hb⟩ := hf
  refine le_antisymm (secAbs_le_one X.triv.2.2 a f) ?_
  rw [secAbs_eq X.triv.2.2 hb]
  obtain ⟨β, hβ, hz, -⟩ := exists_mem_monSet_ne_zero X.triv.2.2 b
  refine le_trans (le_of_eq ?_) (le_secAbsAt (X.triv : Berk k X.S) hβ)
  rw [X.homNorm_of_mem _ (hb.mul_zCoeff_mem hβ), X.triv_val_of_ne_zero]
  rw [Ne, ofPiece_eq_zero_iff]
  exact mul_ne_zero hf0 hz

/-- **`lem:gl-sections`(3)**: `|f|_v ≠ 0` for `0 ≠ f ∈ R_a` at a point `v ∈ 𝒳^an` with generic
support. -/
theorem secAbs_ne_zero {v : Berk k X.S} (hv : X.IsNormalized v) (hg : X.HasGenericSupport v)
    (hf : f ∈ X.sections a) (hf0 : f ≠ 0) : X.secAbs v a f ≠ 0 := by
  obtain ⟨b, hb⟩ := hf
  rw [secAbs_eq hv hb]
  obtain ⟨β, hβ, hz, -⟩ := exists_mem_monSet_ne_zero hv b
  refine ne_of_gt (lt_of_lt_of_le ?_ (le_secAbsAt v hβ))
  rw [X.homNorm_of_mem _ (hb.mul_zCoeff_mem hβ)]
  refine pos_iff_ne_zero.2 (hg _ ?_)
  rw [Ne, ofPiece_eq_zero_iff]
  exact mul_ne_zero hf0 hz

variable (X) in
/-- **`lem:gl-sections`(3)**: `v ↦ |f|_v` is continuous on `(Spec S)^an`. -/
theorem continuous_secAbs (a : Fin r → ℤ) (f : K) :
    Continuous fun v : Berk k X.S => X.secAbs v a f := by
  by_cases h : f ∈ X.sections a
  · simp only [secAbs, dif_pos h, secAbsAt]
    exact Continuous.finset_sup_apply fun β _ => X.continuous_homNorm _ _
  · simp only [secAbs_of_notMem _ h]
    exact continuous_const

variable (X) in
theorem continuous_logSecAbs (a : Fin r → ℤ) (f : K) :
    Continuous fun v : Berk k X.S => X.logSecAbs v a f :=
  ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp (X.continuous_secAbs a f))

/-! ### `log |f|` -/

theorem logSecAbs_ne_top (v : Berk k X.S) (a : Fin r → ℤ) (f : K) : X.logSecAbs v a f ≠ ⊤ := by
  rw [logSecAbs, Ne, ENNReal.log_eq_top_iff]
  exact ENNReal.coe_ne_top

theorem logSecAbs_eq_bot_iff (v : Berk k X.S) (a : Fin r → ℤ) (f : K) :
    X.logSecAbs v a f = ⊥ ↔ X.secAbs v a f = 0 := by
  rw [logSecAbs, ENNReal.log_eq_bot_iff, ENNReal.coe_eq_zero]

theorem logSecAbs_le_zero {v : Berk k X.S} (hv : X.IsNormalized v) (a : Fin r → ℤ) (f : K) :
    X.logSecAbs v a f ≤ 0 := by
  rw [logSecAbs, ENNReal.log_le_zero_iff]
  exact ENNReal.coe_le_one_iff.2 (secAbs_le_one hv a f)

theorem logSecAbs_triv (hf : f ∈ X.sections a) (hf0 : f ≠ 0) :
    X.logSecAbs (X.triv : Berk k X.S) a f = 0 := by
  rw [logSecAbs, secAbs_triv hf hf0, ENNReal.coe_one, ENNReal.log_one]

theorem logSecAbs_zero (v : Berk k X.S) (a : Fin r → ℤ) : X.logSecAbs v a 0 = ⊥ := by
  rw [logSecAbs_eq_bot_iff, secAbs_zero]

theorem logSecAbs_mul {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a)
    (hg : g ∈ X.sections a') :
    X.logSecAbs v (a + a') (f * g) = X.logSecAbs v a f + X.logSecAbs v a' g := by
  rw [logSecAbs, secAbs_mul hv hf hg, ENNReal.coe_mul, ENNReal.log_mul_add]
  rfl

theorem logSecAbs_pow {v : Berk k X.S} (hv : X.IsNormalized v) (hf : f ∈ X.sections a) (n : ℕ) :
    X.logSecAbs v (n • a) (f ^ n) = (n : EReal) * X.logSecAbs v a f := by
  rw [logSecAbs, secAbs_pow hv hf, ENNReal.coe_pow, ENNReal.log_pow]
  rfl

/-! ### Charts (`lem:gl-sections`(4)) -/

variable (X) in
/-- `z̃_j^a = ∏_c (f^{(c)}_{j_c})^{a_c} ∈ K` for `a ∈ ℤ^r`. -/
def chartDenZ (j : X.ChartIndex) (a : Fin r → ℤ) : K :=
  ∏ c, X.coord c (j c) ^ a c

theorem chartDen_addDeg {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hb : ∀ c, 0 ≤ a c + b c) : X.chartDen j (addDeg a b) = X.chartDenZ j a * X.chartDen j b :=
  prod_pow_addDeg hj hb

/-- **`lem:gl-sections`(4)**: `f / z̃_j^a ∈ A_j` for `f ∈ R_a`. -/
theorem div_chartDenZ_mem_chartAlg {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hf : f ∈ X.sections a) : f / X.chartDenZ j a ∈ X.chartAlg j := by
  obtain ⟨b, hb⟩ := hf
  have h := div_chartDen_mem_chartAlg (j := j) (hb.mul_chartDen_mem j)
  rwa [chartDen_addDeg hj hb.1, mul_div_mul_right _ _ (chartDen_ne_zero hj b)] at h

/-- **`lem:gl-sections`(4)**, chart-free form: if `|z^{(c)}_{j_c}|_v ≠ 0` for all `c`, then
`|f|_v = |f z̃_j^b T^{a+b}|_v / |z_j^b|_v` for every admissible `b`. Indeed
`(f z̃^β T^{a+b}) z_j^b = (f z̃_j^b T^{a+b}) z^β` in `S`, and `max_β |z^β|_v = 1`. -/
theorem secAbs_eq_div_chartMono {v : Berk k X.S} (hv : X.IsNormalized v) {j : X.ChartIndex}
    (hvj : ∀ c, v.val (X.coordElem ⟨c, j c⟩) ≠ 0) (h : X.IsAdmissible a b f) :
    X.secAbs v a f = X.homNorm v (addDeg a b) (f * X.chartDen j b) / v.val (X.chartMono j b) := by
  have hz := val_chartMono_ne_zero hvj b
  have key : ∀ β ∈ X.monSet b, X.homNorm v (addDeg a b) (f * X.zCoeff β) * v.val (X.chartMono j b) =
      X.homNorm v (addDeg a b) (f * X.chartDen j b) * v.val (X.zMon β) := fun β hβ => by
    have e₁ := homNorm_mul v (h.mul_zCoeff_mem hβ) (X.chartDen_mem_piece j b)
    have e₂ := homNorm_mul v (h.mul_chartDen_mem j) (zCoeff_mem_piece_of_mem_monSet hβ)
    rw [X.homNorm_of_mem v (X.chartDen_mem_piece j b)] at e₁
    rw [X.homNorm_of_mem v (zCoeff_mem_piece_of_mem_monSet hβ),
      ofPiece_zCoeff_of_mem_monSet hβ] at e₂
    change _ = X.homNorm v (addDeg a b) (f * X.zCoeff β) * v.val (X.chartMono j b) at e₁
    rw [← e₁, ← e₂, mul_right_comm]
  rw [secAbs_eq hv h]
  apply le_antisymm
  · refine Finset.sup_le fun β hβ => ?_
    rw [le_div_iff₀ (pos_iff_ne_zero.2 hz), key β hβ]
    exact mul_le_of_le_one_right zero_le (hv.val_zMon_le_one β)
  · obtain ⟨β, hβ, -, h1⟩ := exists_mem_monSet_ne_zero hv b
    rw [div_le_iff₀ (pos_iff_ne_zero.2 hz)]
    calc X.homNorm v (addDeg a b) (f * X.chartDen j b)
        = X.homNorm v (addDeg a b) (f * X.zCoeff β) * v.val (X.chartMono j b) := by
          rw [key β hβ, h1, mul_one]
      _ ≤ X.secAbsAt v a b f * v.val (X.chartMono j b) :=
          mul_le_mul_of_nonneg_right
            (le_secAbsAt v hβ) zero_le

/-- **`lem:gl-sections`(4)**: on the chart domain `U_j`,
`|f|_v = |f / z̃_j^a|_{ι_j(v)} ∏_c |z^{(c)}_{j_c}|_v^{a_c}` for `f ∈ R_a`. -/
theorem secAbs_eq_chartMap {v : Berk k X.S} (hv : X.IsNormalized v) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) (hvj : ∀ c, v.val (X.coordElem ⟨c, j c⟩) ≠ 0)
    (hf : f ∈ X.sections a) :
    X.secAbs v a f =
      (X.chartMap hj v hvj).val ⟨f / X.chartDenZ j a, div_chartDenZ_mem_chartAlg hj hf⟩ *
        ∏ c, v.val (X.coordElem ⟨c, j c⟩) ^ a c := by
  obtain ⟨b, hb⟩ := hf
  have hx : f / X.chartDenZ j a = f * X.chartDen j b / X.chartDen j (addDeg a b) := by
    rw [chartDen_addDeg hj hb.1, mul_div_mul_right _ _ (chartDen_ne_zero hj b)]
  rw [X.chartMap_val_eq hj hvj _ (hb.mul_chartDen_mem j) hx, secAbs_eq_div_chartMono hv hvj hb,
    X.homNorm_of_mem v (hb.mul_chartDen_mem j), val_chartMono, val_chartMono,
    prod_pow_addDeg hvj hb.1]
  have hP : ∏ c, v.val (X.coordElem ⟨c, j c⟩) ^ a c ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (hvj c)
  have hQ : ∏ c, v.val (X.coordElem ⟨c, j c⟩) ^ b c ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (hvj c)
  field_simp

/-! ### The semiample and nef cones (`def:gl-cones`, `lem:gl-cones`) -/

variable (X) in
/-- A finite family `s ⊆ R_a` is **base point free** if it has no common zero on `𝒳^an`. -/
def IsBasePointFree (a : Fin r → ℤ) (s : Finset K) : Prop :=
  (∀ f ∈ s, f ∈ X.sections a) ∧ ∀ v : X.an, ∃ f ∈ s, X.secAbs v.1 a f ≠ 0

/-- **`lem:gl-cones`(2)**: if `f_t ∈ R_a` have no common zero on `𝒳^an`, then
`max_t |f_t|_v = 1` for every `v ∈ 𝒳^an`. -/
theorem IsBasePointFree.sup_secAbs_eq_one {s : Finset K} (hs : X.IsBasePointFree a s)
    (v : X.an) : s.sup (fun f => X.secAbs v.1 a f) = 1 := by
  refine le_antisymm (Finset.sup_le fun f _ => secAbs_le_one v.2.2 a f) ?_
  obtain ⟨j, hj, hv1⟩ := X.exists_chartIndex v
  have hvj : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) ≠ 0 := fun c => by
    rw [hv1 c]; exact one_ne_zero
  let g : s → X.chartAlg j := fun f =>
    ⟨f.1 / X.chartDenZ j a, div_chartDenZ_mem_chartAlg hj (hs.1 f.1 f.2)⟩
  -- the `g_t` generate the unit ideal of `A_j`
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    refine Berk.span_eq_top_of_forall_exists_val_ne_zero (k := k) _ fun y => ?_
    obtain ⟨f, hf, hne⟩ := hs.2 (X.chartInv j hj y)
    refine ⟨g ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, fun h0 => hne ?_⟩
    have e := secAbs_eq_chartMap (X.chartInv j hj y).2.2 hj
      (chartInv_val_coordElem_ne_zero hj y) (hs.1 f hf)
    rw [chartMap_chartInv] at e
    rw [e]
    change y.val (g ⟨f, hf⟩) * _ = 0
    rw [h0, zero_mul]
  obtain ⟨cf, hcf⟩ := Ideal.mem_span_range_iff_exists_fun.1
    ((Ideal.eq_top_iff_one _).1 hspan)
  set y := X.chartMap hj v.1 hvj
  -- elements of `A_j` have norm `≤ 1` at `ι_j(v)`, since `|z_j|_v = 1`
  have hle : ∀ x : X.chartAlg j, y.val x ≤ 1 := fun x => by
    obtain ⟨d, p, hp, hx⟩ := (mem_chartAlg_iff hj).1 x.2
    rw [X.chartMap_val_eq hj hvj x hp hx, val_chartMono]
    simp only [hv1, one_pow, Finset.prod_const_one, div_one]
    exact val_le_one v.2 _
  have hg : ∀ f : s, y.val (g f) = X.secAbs v.1 a f.1 := fun f => by
    rw [secAbs_eq_chartMap v.2.2 hj hvj (hs.1 f.1 f.2)]
    simp only [hv1, one_zpow, Finset.prod_const_one, mul_one]
    rfl
  calc (1 : ℝ≥0) = y.val (∑ i, cf i * g i) := by rw [hcf, map_one]
    _ ≤ s.sup fun f => X.secAbs v.1 a f := by
      refine y.val.map_sum_le fun i _ => ?_
      rw [map_mul, hg i]
      exact (mul_le_of_le_one_left zero_le (hle (cf i))).trans
        (Finset.le_sup (f := fun f => X.secAbs v.1 a f) i.2)

/-- A vector `a ∈ ℚ^r` with `0 ≤ a` has a positive integral multiple `m a ∈ ℕ^r`. -/
theorem _root_.EnvelopeProperty.exists_nat_mul_rat_vec_eq_nat_of_nonneg {r : ℕ}
    {a : Fin r → ℚ} (ha : 0 ≤ a) :
    ∃ m : ℕ, 0 < m ∧ ∃ d : Fin r → ℕ, ∀ c, (d c : ℚ) = m * a c := by
  have hm : 0 < ∏ c, (a c).den := Finset.prod_pos fun c _ => (a c).den_pos
  refine ⟨∏ c, (a c).den, hm, ?_⟩
  have key : ∀ c, ∃ z : ℕ, (z : ℚ) = ((∏ c, (a c).den : ℕ) : ℚ) * a c := by
    intro c
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun c => (a c).den) (Finset.mem_univ c)
    have hnum : 0 ≤ (a c).num := Rat.num_nonneg.2 (ha c)
    refine ⟨k * (a c).num.toNat, ?_⟩
    rw [hk]
    have h1 : (((a c).num.toNat : ℕ) : ℚ) = ((a c).num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum]
    push_cast
    rw [h1, ← Rat.mul_den_eq_num]
    ring
  choose d hd using key
  exact ⟨d, hd⟩

variable (X) in
/-- The **model-semiample cone** `C(𝒳) ⊆ ℚ^r` (`def:gl-cones`): the classes `a` for which there are
`m ≥ 1` with `m a ∈ ℤ^r` and finitely many `f_t ∈ R_{m a}` without common zero on `𝒳^an`. It is a
convex cone (`lem:gl-cones`(1)): products `f_t^{m'} f'^{m}_u` of base point free families have no
common zero, and so have powers `f_t^p`. -/
def semiampleCone : ConvexCone ℚ (Fin r → ℚ) where
  carrier := {a | ∃ (m : ℕ) (d : Fin r → ℤ) (s : Finset K), 0 < m ∧ (∀ c, (d c : ℚ) = m * a c) ∧
    X.IsBasePointFree d s}
  smul_mem' := by
    rintro q hq a ⟨m, d, s, hm, hd, hs⟩
    classical
    refine ⟨q.den * m, q.num.toNat • d, s.image fun f => f ^ q.num.toNat,
      Nat.mul_pos q.den_pos hm, fun c => ?_, ⟨fun f hf => ?_, fun v => ?_⟩⟩
    · have h : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq.le)
      have key : (((q.num.toNat • d) c : ℤ) : ℚ) = (q.num : ℚ) * (d c : ℚ) := by
        rw [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, h]
      rw [key, hd c, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, ← Rat.den_mul_eq_num]
      ring
    · obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.1 hf
      exact pow_mem_sections (hs.1 f₀ hf₀) _
    · obtain ⟨f, hf, hne⟩ := hs.2 v
      refine ⟨f ^ q.num.toNat, Finset.mem_image.2 ⟨f, hf, rfl⟩, ?_⟩
      rw [secAbs_pow v.2.2 (hs.1 f hf)]
      exact pow_ne_zero _ hne
  add_mem' := by
    rintro a ⟨m, d, s, hm, hd, hs⟩ a' ⟨m', d', s', hm', hd', hs'⟩
    classical
    refine ⟨m * m', m' • d + m • d', (s ×ˢ s').image fun p => p.1 ^ m' * p.2 ^ m,
      Nat.mul_pos hm hm', fun c => ?_, ⟨fun f hf => ?_, fun v => ?_⟩⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, Int.cast_add,
        Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, hd c, hd' c,
        Pi.add_apply, Nat.cast_mul]
      ring
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hf
      rw [Finset.mem_product] at hp
      exact mul_mem_sections (pow_mem_sections (hs.1 _ hp.1) _) (pow_mem_sections (hs'.1 _ hp.2) _)
    · obtain ⟨f, hf, hne⟩ := hs.2 v
      obtain ⟨f', hf', hne'⟩ := hs'.2 v
      refine ⟨f ^ m' * f' ^ m, Finset.mem_image.2 ⟨(f, f'), Finset.mem_product.2 ⟨hf, hf'⟩, rfl⟩,
        ?_⟩
      rw [secAbs_mul v.2.2 (pow_mem_sections (hs.1 f hf) _) (pow_mem_sections (hs'.1 f' hf') _),
        secAbs_pow v.2.2 (hs.1 f hf), secAbs_pow v.2.2 (hs'.1 f' hf')]
      exact mul_ne_zero (pow_ne_zero _ hne) (pow_ne_zero _ hne')

theorem mem_semiampleCone {a : Fin r → ℚ} : a ∈ X.semiampleCone ↔
    ∃ (m : ℕ) (d : Fin r → ℤ) (s : Finset K), 0 < m ∧ (∀ c, (d c : ℚ) = m * a c) ∧
      X.IsBasePointFree d s :=
  Iff.rfl

variable (X) in
/-- **`lem:gl-cones`(1)**: `ℚ^r_{≥0} ⊆ C(𝒳)`: the monomials `z̃^β`, `β ∈ Mon(m a)`, have no common
zero on `𝒳^an`, since `max_β |z^β|_v = 1`. -/
theorem nonneg_mem_semiampleCone {a : Fin r → ℚ} (ha : 0 ≤ a) : a ∈ X.semiampleCone := by
  classical
  obtain ⟨m, hm, d, hd⟩ := exists_nat_mul_rat_vec_eq_nat_of_nonneg ha
  set dN : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm d with hdN
  have hdN' : ∀ c, ((fun c => (d c : ℤ)) c : ℤ) = dN c := fun c => rfl
  refine ⟨m, fun c => (d c : ℤ), (X.monSet dN).image X.zCoeff, hm, fun c => ?_,
    ⟨fun f hf => ?_, fun v => ?_⟩⟩
  · simpa using hd c
  · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hf
    exact mem_sections_of_mem_piece hdN' (zCoeff_mem_piece_of_mem_monSet hβ)
  · obtain ⟨β, hβ, h1⟩ := v.2.2.exists_val_zMon_eq_one dN
    refine ⟨X.zCoeff β, Finset.mem_image_of_mem _ hβ, ?_⟩
    rw [secAbs_of_mem_piece v.2.2 hdN' (zCoeff_mem_piece_of_mem_monSet hβ),
      ofPiece_zCoeff_of_mem_monSet hβ, h1]
    exact one_ne_zero

/-- **`lem:gl-cones`(1)**: `C(𝒳) + ℚ^r_{≥0} ⊆ C(𝒳)`. -/
theorem mem_semiampleCone_of_le {a b : Fin r → ℚ} (ha : a ∈ X.semiampleCone) (hab : a ≤ b) :
    b ∈ X.semiampleCone := by
  have := X.semiampleCone.add_mem ha (X.nonneg_mem_semiampleCone (sub_nonneg.2 hab))
  rwa [add_sub_cancel] at this

variable (X) in
/-- The **model-nef cone** `N(𝒳) ⊆ ℝ^r` (`def:gl-cones`): the closure of `C(𝒳)`. -/
def nefCone : Set (Fin r → ℝ) :=
  ratClosure (X.semiampleCone : Set (Fin r → ℚ))

variable (X) in
/-- **`lem:gl-cones`(1)**: `N(𝒳)` is closed. -/
theorem isClosed_nefCone : IsClosed X.nefCone :=
  isClosed_ratClosure _

/-- **`lem:gl-cones`(1)**: `N(𝒳) + N(𝒳) ⊆ N(𝒳)`. -/
theorem add_mem_nefCone {θ θ' : Fin r → ℝ} (hθ : θ ∈ X.nefCone) (hθ' : θ' ∈ X.nefCone) :
    θ + θ' ∈ X.nefCone :=
  add_mem_ratClosure hθ hθ'

/-- **`lem:gl-cones`(1)**: `t N(𝒳) ⊆ N(𝒳)` for `t > 0`. -/
theorem smul_mem_nefCone {θ : Fin r → ℝ} (hθ : θ ∈ X.nefCone) {t : ℝ} (ht : 0 < t) :
    t • θ ∈ X.nefCone :=
  smul_mem_ratClosure hθ ht

variable (X) in
/-- **`lem:gl-cones`(1)**: `ℝ^r_{≥0} ⊆ N(𝒳)`. -/
theorem mem_nefCone_of_nonneg {θ : Fin r → ℝ} (hθ : 0 ≤ θ) : θ ∈ X.nefCone :=
  mem_ratClosure_of_nonneg (fun _ ha => X.nonneg_mem_semiampleCone ha) hθ

/-- `C(𝒳) ⊆ N(𝒳)`. -/
theorem coe_mem_nefCone {a : Fin r → ℚ} (ha : a ∈ X.semiampleCone) :
    (fun c => (a c : ℝ)) ∈ X.nefCone :=
  coe_mem_ratClosure ha

/-- Rational classes `a > θ` with `θ ∈ N(𝒳)` are semiample (used for `lem:gl-cones`(3)). -/
theorem mem_semiampleCone_of_lt {θ : Fin r → ℝ} (hθ : θ ∈ X.nefCone) {a : Fin r → ℚ}
    (ha : ∀ c, θ c < a c) : a ∈ X.semiampleCone :=
  mem_of_lt_of_mem_ratClosure (fun _ ha => X.nonneg_mem_semiampleCone ha) hθ ha

end MultiModel

end EnvelopeProperty
