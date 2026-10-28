/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.FS
import EnvelopeProperty.Local.Hull
import EnvelopeProperty.Local.Imports
import EnvelopeProperty.Berkovich.Gauss

/-!
# The Hartogs radius criterion for regularizability

Let `Y = Spec A` be a normal affine variety over the algebraically closed, countable, trivially
valued field `k`, let `Ỹ = Y × 𝔸¹ = Spec A[w]` (we write `A[X]`, `w = X`) and
`p : Ỹ^an → Y^an` the projection (`Berk.proj`). This file proves Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Lemma 5.16 (`lem:hartogs`):

> Let `u : Y^an → [-∞, ∞)` be upper semicontinuous, of logarithmic growth and not identically
> `-∞`. If `D = {u ∘ p + log|w| < 0} ⊆ Ỹ^an` is Runge, then `u ∈ ℛ(Y)`.

## Proof

`D` is open. By FHX Lemma 5.14(2) (`IsRunge.exists_fs_exhaustion`, on `Ỹ`) there are
`g_j ∈ FS(Ỹ)` with `{g_j < 1}` increasing to `D`; put `W_j = {g_j < 1} ∩ {log|w| < j}`, which
increase to `D`. Writing `g_j = max{b₀, max_t (a_t log|F_t| + b_t)}`, the condition `g_j < 1` is
`b₀ < 1` and `log|F_t| < c_t := (1 - b_t)/a_t` for all terms `t`. Put
`Ω_j = {y | η_{y,0} ∈ W_j}` (open, increasing, covering `Y^an` since `η_{y,0} ∈ D`), and
`φ_j = max{-j, max_{t, ℓ ≥ 1} (log|a_{tℓ}| - c_t)/ℓ}` where `F_t = ∑_ℓ a_{tℓ} w^ℓ`
(`Hartogs.radiusFun`); this is `-log` of the Hartogs radius of `W_j`. It is convex PL on `Y^an`
(near a point, the terms whose coefficient vanishes there are dominated by `-j`). For `y ∈ Ω_j` and
`s ∈ ℝ`, the coefficientwise description of strict inequalities at Gauss points
(`Berk.logAbs_gauss_lt_iff_of_ne_zero`) gives `η_{y,e^{-s}} ∈ W_j ↔ φ_j(y) < s`
(`Hartogs.gauss_rad_mem_iff`), while `η_{y,e^{-s}} ∈ D ↔ u(y) < s`. Hence `φ_j ≥ φ_{j+1} ≥ u` on
`Ω_j`, and `φ_j ↓ u` on `Ω_j` because `D = ⋃_j W_j`. Every compact set lies in some `Ω_{j₀}`, on
which `u` is the decreasing limit of the convex PL functions `φ_{j₀+m}`; the imported FHX
Lemma 5.11(6) (`WuRegularization.localToGlobal`) concludes.

## Main definitions

* `EnvelopeProperty.Hartogs.threshold t`: the threshold `c_t = (1 - b)/a` of a term `(F, a, b)`.
* `EnvelopeProperty.Hartogs.radiusTerms s`: the terms `((1/ℓ) log|a_ℓ| - c_t/ℓ)`, `ℓ ≥ 1`.
* `EnvelopeProperty.Hartogs.radiusFun G N`: the function `φ = max{-N, max (radius terms)}` on
  `Y^an`, `-log` of the Hartogs radius of `{G < 1} ∩ {log|w| < N}` over `{y | G(η_{y,0}) < 1}`.
* `EnvelopeProperty.Hartogs.rad s`: the radius `e^{-s}`.

## Main results

* `EnvelopeProperty.isConvexPLOn_univ_max_sup_fsTerm`: a maximum of a rational constant and terms
  `a log|f| + b` with `a > 0` is convex PL on the whole analytification.
* `EnvelopeProperty.Hartogs.gauss_rad_mem_iff`: `η_{y,e^{-s}} ∈ {G < 1} ∩ {log|w| < N}` iff
  `φ(y) < s`, for `y` with `G(η_{y,0}) < 1`.
* `EnvelopeProperty.IsRegularizable.of_isRunge_hartogs`: FHX Lemma 5.16.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Polynomial

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

section General

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- A maximum `max{c, max_t (a_t log|f_t| + b_t)}` of a rational constant and finitely many terms
with positive coefficients `a_t` is convex PL on the whole analytification. This is the argument
of `FSData.isConvexPLOn_univ` ("the argument following (5.2)" in FHX), which does not use that the
`f_t` generate `A`: near a point `x`, the terms whose function vanishes at `x` are below the
constant `c` and may be dropped. -/
theorem isConvexPLOn_univ_max_sup_fsTerm (c : ℚ) (s : Finset (A × ℚ × ℚ))
    (hs : ∀ t ∈ s, 0 < t.2.1) :
    IsConvexPLOn univ fun y : Berk k A => max ((c : ℝ) : EReal) (s.sup fun t => fsTerm t y) := by
  classical
  refine isConvexPLOn_of_local fun x _ => ?_
  let V : Set (Berk k A) := {y | ∀ t ∈ s.filter (fun t => x.val t.1 ≠ 0), y.val t.1 ≠ 0} ∩
    ⋂ t ∈ s.filter (fun t => ¬ x.val t.1 ≠ 0), {y | fsTerm t y < ((c : ℝ) : EReal)}
  have hV : IsOpen V := (isOpen_setOf_forall_abs_ne_zero _).inter
    (isOpen_biInter_finset fun t _ => isOpen_lt (continuous_fsTerm t) continuous_const)
  have hxV : x ∈ V := by
    refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, Set.mem_iInter₂.2 fun t ht => ?_⟩
    have ht' := Finset.mem_filter.1 ht
    show fsTerm t x < _
    rw [fsTerm_eq_bot (hs t ht'.1) (not_not.1 ht'.2)]
    exact EReal.bot_lt_coe _
  refine ⟨V, hV, hxV, Set.subset_univ _,
    ((isConvexPLOn_max_sup_fsTerm c _).mono hV Set.inter_subset_left).congr fun y hy => ?_⟩
  show max _ _ = max _ _
  rw [max_sup_eq_max_sup_filter s (fun t => x.val t.1 ≠ 0)]
  intro t ht hxt
  exact (Set.mem_iInter₂.1 hy.2 t (Finset.mem_filter.2 ⟨ht, hxt⟩)).le

/-- `(∀ s ∈ ℝ, a < s → b < s) → b ≤ a` in `EReal`. -/
private theorem ereal_le_of_forall_lt {a b : EReal} (h : ∀ s : ℝ, a < s → b < s) : b ≤ a :=
  EReal.le_of_forall_lt_iff_le.1 fun s hs => (h s hs).le

/-- `a - s < 0 ↔ a < s` in `EReal`, for real `s`. -/
private theorem ereal_add_neg_lt_zero_iff (a : EReal) (s : ℝ) :
    a + ((-s : ℝ) : EReal) < 0 ↔ a < (s : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith
  | top => simp

/-- `⊥ < 1` in `EReal`. -/
private theorem ereal_bot_lt_one : (⊥ : EReal) < 1 := EReal.bot_lt_coe 1

end General

namespace Hartogs

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### The threshold of a term -/

/-- The **threshold** `c_t = (1 - b)/a` of a term `t = (F, a, b)`: for `a > 0`,
`a log|F| + b < 1 ↔ log|F| < c_t` (`Hartogs.fsTerm_lt_one_iff`). -/
def threshold {B : Type*} (t : B × ℚ × ℚ) : ℚ := (1 - t.2.2) / t.2.1

/-- `a log|F| + b < 1 ↔ log|F| < (1 - b)/a` for `a > 0`. -/
theorem fsTerm_lt_one_iff {B : Type*} [CommRing B] [Algebra k B] {t : B × ℚ × ℚ}
    (ht : 0 < t.2.1) (z : Berk k B) :
    fsTerm t z < 1 ↔ logAbs t.1 z < (((threshold t : ℚ) : ℝ) : EReal) := by
  have ha : (0 : ℝ) < t.2.1 := by exact_mod_cast ht
  have hc : (((threshold t : ℚ) : ℝ)) = (1 - (t.2.2 : ℝ)) / t.2.1 := by
    simp [threshold]
  rw [fsTerm_def, hc]
  induction logAbs t.1 z using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos ha, EReal.bot_add]
    exact ⟨fun _ => EReal.bot_lt_coe _, fun _ => ereal_bot_lt_one⟩
  | coe L =>
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_one, EReal.coe_lt_coe_iff,
      EReal.coe_lt_coe_iff, lt_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  | top => simp [EReal.coe_mul_top_of_pos ha]

/-- `g < 1` for FS data `g` means `b₀ < 1` and `log|F_t| < c_t` for every term `t`. -/
theorem eval_lt_one_iff {B : Type*} [CommRing B] [Algebra k B] (G : FSData k B) (z : Berk k B) :
    G.eval z < 1 ↔ ((G.const : ℝ) : EReal) < 1 ∧
      ∀ t ∈ G.terms, logAbs t.1 z < (((threshold t : ℚ) : ℝ) : EReal) := by
  rw [FSData.eval_def, max_lt_iff, Finset.sup_lt_iff ereal_bot_lt_one]
  refine and_congr Iff.rfl (forall₂_congr fun t ht => fsTerm_lt_one_iff (G.pos t ht) z)

/-! ### The terms of the Hartogs radius -/

open Classical in
/-- The **radius terms** of a finite set `s` of terms on `Y × 𝔸¹`: for each `t = (F, a, b) ∈ s`
with `F = ∑_ℓ a_ℓ w^ℓ` and each `ℓ ≥ 1` with `a_ℓ ≠ 0`, the term `(a_ℓ, 1/ℓ, -c_t/ℓ)`, i.e. the
function `(log|a_ℓ| - c_t)/ℓ` on `Y^an`. -/
def radiusTerms (s : Finset (A[X] × ℚ × ℚ)) : Finset (A × ℚ × ℚ) :=
  s.biUnion fun t => (t.1.support.erase 0).image fun ℓ =>
    (t.1.coeff ℓ, 1 / (ℓ : ℚ), -threshold t / ℓ)

theorem radiusTerms_pos (s : Finset (A[X] × ℚ × ℚ)) : ∀ t ∈ radiusTerms s, 0 < t.2.1 := by
  classical
  intro t ht
  simp only [radiusTerms, Finset.mem_biUnion, Finset.mem_image] at ht
  obtain ⟨t', -, ℓ, hℓ, rfl⟩ := ht
  have : (0 : ℚ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (Finset.mem_erase.1 hℓ).1
  exact one_div_pos.2 this

/-- The function `φ = max{-N, max_{t ∈ G, ℓ ≥ 1} (log|a_{tℓ}| - c_t)/ℓ}` on `Y^an` attached to
FS data `G` on `Y × 𝔸¹` and `N ∈ ℕ`: on `{y | G(η_{y,0}) < 1}` it is `-log` of the Hartogs radius
of `{G < 1} ∩ {log|w| < N}` (`Hartogs.gauss_rad_mem_iff`). -/
def radiusFun (G : FSData k A[X]) (N : ℕ) (y : Berk k A) : EReal :=
  max (((-(N : ℚ) : ℚ) : ℝ) : EReal) ((radiusTerms G.terms).sup fun t => fsTerm t y)

/-- `φ` is convex PL on the whole analytification. -/
theorem isConvexPLOn_radiusFun (G : FSData k A[X]) (N : ℕ) :
    IsConvexPLOn univ (radiusFun G N) :=
  isConvexPLOn_univ_max_sup_fsTerm _ _ (radiusTerms_pos _)

/-- `φ(y) < s` iff `-N < s` and every radius term is `< s` at `y`. -/
theorem radiusFun_lt_iff (G : FSData k A[X]) (N : ℕ) (y : Berk k A) (s : ℝ) :
    radiusFun G N y < s ↔ -(N : ℝ) < s ∧ ∀ t ∈ G.terms, ∀ ℓ ∈ t.1.support.erase 0,
      fsTerm (t.1.coeff ℓ, 1 / (ℓ : ℚ), -threshold t / ℓ) y < (s : EReal) := by
  classical
  rw [radiusFun, max_lt_iff, Finset.sup_lt_iff (EReal.bot_lt_coe s), EReal.coe_lt_coe_iff]
  push_cast
  refine and_congr Iff.rfl ⟨fun h t ht ℓ hℓ => h _ ?_, fun h t' ht' => ?_⟩
  · simp only [radiusTerms, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨t, ht, ℓ, hℓ, rfl⟩
  · simp only [radiusTerms, Finset.mem_biUnion, Finset.mem_image] at ht'
    obtain ⟨t, ht, ℓ, hℓ, rfl⟩ := ht'
    exact h t ht ℓ hℓ

/-! ### Gauss points of radius `e^{-s}` -/

/-- The radius `e^{-s} > 0`. -/
def rad (s : ℝ) : ℝ≥0 := ⟨Real.exp (-s), (Real.exp_pos _).le⟩

theorem rad_ne_zero (s : ℝ) : rad s ≠ 0 := by
  rw [← NNReal.coe_ne_zero]
  exact (Real.exp_pos _).ne'

theorem log_rad (s : ℝ) : Real.log (rad s : ℝ) = -s :=
  Real.log_exp _

theorem logAbs_X_gauss_rad (y : Berk k A) (s : ℝ) :
    logAbs (X : A[X]) (gauss y (rad s)) = ((-s : ℝ) : EReal) := by
  rw [logAbs_X_gauss_of_ne_zero _ _ (rad_ne_zero s), log_rad]

/-- `log|F|(η_{y,0}) = log|F(0)|(y)`. -/
theorem logAbs_gauss_zero (F : A[X]) (y : Berk k A) :
    logAbs F (gauss y 0) = logAbs (F.coeff 0) y := by
  rw [logAbs, logAbs, gauss_zero_val_apply]

/-- The condition of a coefficient of degree `ℓ ≥ 1`: `L + ℓ log r < c ↔ (L - c)/ℓ < -log r`. -/
private theorem coeff_cond_iff {L : EReal} (hL : L ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (c : ℚ) (s : ℝ) :
    L + (ℓ : EReal) * ((-s : ℝ) : EReal) < ((c : ℝ) : EReal) ↔
      (((1 / (ℓ : ℚ) : ℚ) : ℝ) : EReal) * L + (((-c / ℓ : ℚ) : ℝ) : EReal) < (s : EReal) := by
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  induction L using EReal.rec with
  | bot =>
    have h1 : (0 : ℝ) < ((1 / (ℓ : ℚ) : ℚ) : ℝ) := by push_cast; positivity
    rw [EReal.bot_add, EReal.coe_mul_bot_of_pos h1, EReal.bot_add]
    exact ⟨fun _ => EReal.bot_lt_coe _, fun _ => EReal.bot_lt_coe _⟩
  | coe L =>
    rw [← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    push_cast
    have e : 1 / (ℓ : ℝ) * L + -(c : ℝ) / ℓ = (L - c) / ℓ := by
      field_simp
      ring
    rw [e, div_lt_iff₀ hℓ']
    constructor <;> intro h <;> linarith
  | top => exact absurd rfl hL

/-- **Strict inequalities at Gauss points of radius `e^{-s}`.** If `log|F(0)|(y) < c`, then
`log|F|(η_{y,e^{-s}}) < c` iff `(log|a_ℓ|(y) - c)/ℓ < s` for every `ℓ ≥ 1` with `a_ℓ ≠ 0`. -/
theorem logAbs_gauss_rad_lt_iff {F : A[X]} {c : ℚ} {y : Berk k A}
    (h0 : logAbs (F.coeff 0) y < ((c : ℝ) : EReal)) (s : ℝ) :
    logAbs F (gauss y (rad s)) < ((c : ℝ) : EReal) ↔
      ∀ ℓ ∈ F.support.erase 0, fsTerm (F.coeff ℓ, 1 / (ℓ : ℚ), -c / ℓ) y < (s : EReal) := by
  rw [logAbs_gauss_lt_iff_of_ne_zero _ _ _ (rad_ne_zero s), log_rad]
  constructor
  · intro h ℓ hℓ
    exact (coeff_cond_iff (logAbs_ne_top _ _) (Finset.mem_erase.1 hℓ).1 c s).1 (h ℓ)
  · intro h ℓ
    by_cases hℓ0 : ℓ = 0
    · subst hℓ0
      simpa using h0
    by_cases hs : ℓ ∈ F.support
    · exact (coeff_cond_iff (logAbs_ne_top _ _) hℓ0 c s).2 (h ℓ (Finset.mem_erase.2 ⟨hℓ0, hs⟩))
    · rw [notMem_support_iff.1 hs, logAbs_zero, EReal.bot_add]
      exact EReal.bot_lt_coe _

/-- **The Hartogs radius of `{G < 1} ∩ {log|w| < N}`** (proof of FHX Lemma 5.16). For `y` with
`G(η_{y,0}) < 1` and `s ∈ ℝ`: `η_{y,e^{-s}} ∈ {G < 1} ∩ {log|w| < N}` iff `φ(y) < s`, where
`φ = Hartogs.radiusFun G N`. -/
theorem gauss_rad_mem_iff (G : FSData k A[X]) (N : ℕ) {y : Berk k A}
    (hy : G.eval (gauss y 0) < 1) (s : ℝ) :
    (G.eval (gauss y (rad s)) < 1 ∧ logAbs (X : A[X]) (gauss y (rad s)) < ((N : ℝ) : EReal)) ↔
      radiusFun G N y < s := by
  rw [eval_lt_one_iff] at hy ⊢
  rw [radiusFun_lt_iff, logAbs_X_gauss_rad, EReal.coe_lt_coe_iff]
  obtain ⟨hc, h0⟩ := hy
  have h0' : ∀ t ∈ G.terms, logAbs (t.1.coeff 0) y < (((threshold t : ℚ) : ℝ) : EReal) :=
    fun t ht => by rw [← logAbs_gauss_zero]; exact h0 t ht
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨by linarith, fun t ht => (logAbs_gauss_rad_lt_iff (h0' t ht) s).1 (h1 t ht)⟩
  · rintro ⟨h2, h1⟩
    exact ⟨⟨hc, fun t ht => (logAbs_gauss_rad_lt_iff (h0' t ht) s).2 (h1 t ht)⟩, by linarith⟩

end Hartogs

open Hartogs

/-- **The Hartogs radius criterion** (FHX Lemma 5.16, `lem:hartogs`). Let `Y = Spec A` be a
normal affine variety over the algebraically closed, countable, trivially valued field `k`, and
`u : Y^an → [-∞, ∞)` upper semicontinuous, of logarithmic growth and not identically `-∞`. If
`D = {u ∘ p + log|w| < 0} ⊆ (Y × 𝔸¹)^an` is Runge, then `u` is regularizable. -/
theorem IsRegularizable.of_isRunge_hartogs {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [WuRegularization.{u, v} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    (u : Berk k A → EReal) (husc : UpperSemicontinuous u) (hlog : HasLogGrowth u)
    (hne : ∃ x, u x ≠ ⊥)
    (hR : IsRunge {z : Berk k A[X] | u (Berk.proj z) + Berk.logAbs Polynomial.X z < 0}) :
    IsRegularizable u := by
  classical
  set D : Set (Berk k A[X]) := {z | u (proj z) + logAbs X z < 0} with hD
  -- `u` never takes the value `⊤`.
  have hutop : ∀ y, u y ≠ ⊤ := by
    obtain ⟨g, C, hg⟩ := hlog
    intro y h
    have := hg y
    rw [h, top_le_iff] at this
    exact EReal.add_ne_top (g.eval_ne_top y) (EReal.coe_ne_top C) this
  -- `D` is open.
  have hDo : IsOpen D := by
    have h1 : UpperSemicontinuous fun z : Berk k A[X] => u (proj z) :=
      husc.comp continuous_proj
    have h2 : UpperSemicontinuous fun z : Berk k A[X] => logAbs (X : A[X]) z :=
      (continuous_logAbs _).upperSemicontinuous
    exact (h1.add' h2 fun z => EReal.continuousAt_add (Or.inl (hutop _))
      (Or.inr (logAbs_ne_top _ _))).isOpen_preimage 0
  -- The exhaustion of `D` by FS sublevel sets on `Y × 𝔸¹`.
  obtain ⟨g, hgmono, hgD⟩ := hR.exists_fs_exhaustion hDo
  have hgmono' : Monotone fun j => {z : Berk k A[X] | (g j).eval z < 1} :=
    monotone_nat_of_le_succ hgmono
  -- The sets `W_j = {g_j < 1} ∩ {log|w| < j}`.
  set W : ℕ → Set (Berk k A[X]) :=
    fun j => {z | (g j).eval z < 1 ∧ logAbs (X : A[X]) z < ((j : ℝ) : EReal)} with hW
  have hWmono : Monotone W := fun i j hij z hz =>
    ⟨hgmono' hij hz.1, hz.2.trans_le (EReal.coe_le_coe_iff.2 (by exact_mod_cast hij))⟩
  have hWD : ∀ j, W j ⊆ D := fun j z hz => hgD ▸ mem_iUnion.2 ⟨j, hz.1⟩
  have hDW : ∀ z ∈ D, ∃ j, z ∈ W j := by
    intro z hz
    rw [← hgD] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    obtain ⟨n, hn⟩ : ∃ n : ℕ, logAbs (X : A[X]) z < ((n : ℝ) : EReal) := by
      induction h : logAbs (X : A[X]) z using EReal.rec with
      | bot => exact ⟨0, EReal.bot_lt_coe _⟩
      | coe r =>
        obtain ⟨n, hn⟩ := exists_nat_gt r
        exact ⟨n, EReal.coe_lt_coe_iff.2 hn⟩
      | top => exact absurd h (logAbs_ne_top _ _)
    refine ⟨max i n, hgmono' (le_max_left i n) hi, hn.trans_le ?_⟩
    exact EReal.coe_le_coe_iff.2 (by exact_mod_cast le_max_right i n)
  -- The sets `Ω_j = {y | η_{y,0} ∈ W_j} = {y | g_j(η_{y,0}) < 1}`.
  set Ω : ℕ → Set (Berk k A) := fun j => {y | (g j).eval (gauss y 0) < 1} with hΩ
  have hΩW : ∀ j y, y ∈ Ω j ↔ gauss y 0 ∈ W j := fun j y => by
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    rw [logAbs_X_gauss, ENNReal.coe_zero, ENNReal.log_zero]
    exact EReal.bot_lt_coe _
  have hΩo : ∀ j, IsOpen (Ω j) := fun j =>
    isOpen_lt ((g j).continuous_eval.comp (continuous_gauss 0)) continuous_const
  have hΩmono : Monotone Ω := fun i j hij y hy =>
    (hΩW j y).2 (hWmono hij ((hΩW i y).1 hy))
  have hΩcover : ∀ y, ∃ j, y ∈ Ω j := by
    intro y
    have hy : gauss y 0 ∈ D := by
      show u (proj (gauss y 0)) + logAbs (X : A[X]) (gauss y 0) < 0
      rw [logAbs_X_gauss, ENNReal.coe_zero, ENNReal.log_zero, EReal.add_bot]
      exact EReal.bot_lt_zero
    obtain ⟨j, hj⟩ := hDW _ hy
    exact ⟨j, (hΩW j y).2 hj⟩
  -- The functions `φ_j` and the key computations.
  set φ : ℕ → Berk k A → EReal := fun j => radiusFun (g j) j with hφ
  have hkey : ∀ j, ∀ y ∈ Ω j, ∀ s : ℝ, gauss y (rad s) ∈ W j ↔ φ j y < s :=
    fun j y hy s => gauss_rad_mem_iff (g j) j hy s
  have hkeyD : ∀ y (s : ℝ), gauss y (rad s) ∈ D ↔ u y < s := fun y s => by
    show u (proj (gauss y (rad s))) + logAbs (X : A[X]) (gauss y (rad s)) < 0 ↔ _
    rw [proj_gauss, logAbs_X_gauss_rad]
    exact ereal_add_neg_lt_zero_iff _ _
  -- `u ≤ φ_j` on `Ω_j`.
  have hle : ∀ j, ∀ y ∈ Ω j, u y ≤ φ j y := fun j y hy =>
    ereal_le_of_forall_lt fun s hs => (hkeyD y s).1 (hWD j ((hkey j y hy s).2 hs))
  -- `φ_{j+1} ≤ φ_j` on `Ω_j`.
  have hanti : ∀ j, ∀ y ∈ Ω j, φ (j + 1) y ≤ φ j y := fun j y hy =>
    ereal_le_of_forall_lt fun s hs => (hkey (j + 1) y (hΩmono j.le_succ hy) s).1
      (hWmono j.le_succ ((hkey j y hy s).2 hs))
  -- Conclusion via the imported local-to-global principle.
  refine WuRegularization.localToGlobal A u hne hlog fun K hK => ?_
  obtain ⟨j₀, hj₀⟩ := hK.elim_directed_cover Ω hΩo
    (fun y _ => mem_iUnion.2 (hΩcover y)) hΩmono.directed_le
  refine ⟨Ω j₀, hΩo j₀, hj₀, fun m => φ (j₀ + m),
    fun m => (isConvexPLOn_radiusFun (g (j₀ + m)) (j₀ + m)).mono (hΩo j₀) (subset_univ _),
    fun y hy => antitone_nat_of_succ_le fun m =>
      hanti (j₀ + m) y (hΩmono (Nat.le_add_right j₀ m) hy), fun y hy => ?_⟩
  refine le_antisymm (le_iInf fun m => hle (j₀ + m) y (hΩmono (Nat.le_add_right j₀ m) hy)) ?_
  refine ereal_le_of_forall_lt fun s hs => ?_
  obtain ⟨i, hi⟩ := hDW _ ((hkeyD y s).2 hs)
  have hy' : y ∈ Ω (j₀ + i) := hΩmono (Nat.le_add_right j₀ i) hy
  exact (iInf_le _ i).trans_lt ((hkey (j₀ + i) y hy' s).1 (hWmono (Nat.le_add_left i j₀) hi))

end EnvelopeProperty
