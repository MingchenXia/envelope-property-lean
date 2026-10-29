/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Regularization
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma

/-!
# Density of rational PL functions on `(ℙⁿ)^an`

This file proves, on the model `ProjBerk k n` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`),
the density of rational PL functions of Boucksom–Jonsson, *Global pluripotential theory over a
trivially valued field* (BJ22), Lemma 2.3 (FSdense) and Theorem 2.2 (PLdense), and the
approximation of usc functions from above by PL functions used in Fang–Han–Xia, *The envelope
property for unibranch projective varieties* (FHX), §3, and in the BJ addendum
(arXiv:2206.07183v2), Lemma 1.3 (contenv). The blueprint nodes are `lem:bj-pl-lattice`,
`thm:bj-pl-dense` and `lem:bj-usc-pl` of `bj22.tex`.

Rational PL functions are `ProjBerk.IsRatPL` (`EnvelopeProperty.Projective.FS`): differences
`φ - ψ` of finite-valued rational Fubini–Study functions `φ ∈ H_ℚ(a)`, `ψ ∈ H_ℚ(b)`.

## Main results

* `lem:bj-pl-lattice`: rational PL functions form a `ℚ`-vector space of continuous functions
  containing the rational constants (`ProjBerk.IsRatPL.add`, `ProjBerk.IsRatPL.smul`,
  `ProjBerk.isRatPL_const`, `ProjBerk.IsRatPL.continuous`, all in `FS`), stable under finite maxima
  and minima (`ProjBerk.IsRatPL.max`, `ProjBerk.IsRatPL.min`), which separates the points of
  `(ℙⁿ)^an` (`ProjBerk.exists_isRatPL_ne`). For the maximum,
  `max(φ₁ - ψ₁, φ₂ - ψ₂) = max(φ₁ + ψ₂, φ₂ + ψ₁) - (ψ₁ + ψ₂)`, the two functions in the maximum
  being moved into a common class by `ProjBerk.IsFiniteRatFS.mono_class`. For the separation, two
  distinct graded points differ on some form `s` of degree `d`
  (`ProjBerk.exists_isHomogeneous_val_ne`), and `max(log|s|, c) ∈ H_ℚ(d)` separates them for a
  suitable rational `c`.
* `thm:bj-pl-dense`: rational PL functions are uniformly dense in `C⁰((ℙⁿ)^an, ℝ)`
  (`ProjBerk.exists_isRatPL_abs_sub_lt`, `ProjBerk.dense_setOf_isRatPL`), by the lattice version
  of the Stone–Weierstrass theorem (`ContinuousMap.sublattice_closure_eq_top`) applied to the
  uniform closure of the PL functions.
* `lem:bj-usc-pl`: if `h : (ℙⁿ)^an → [-∞, +∞)` is usc, the PL functions `ψ > h` form a nonempty
  (`ProjBerk.exists_isRatPL_gt`), downward directed (`ProjBerk.IsRatPL.min`) family with pointwise
  infimum `h` (`ProjBerk.exists_isRatPL_gt_apply_lt`, `ProjBerk.iInf_isRatPL_gt`); as a decreasing
  net: `ProjBerk.exists_antitone_isRatPL_net`; as a comparison principle:
  `ProjBerk.le_of_forall_isRatPL_gt`. The proof is Urysohn's lemma followed by uniform
  approximation.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Auxiliary facts -/

theorem ereal_coe_max (x y : ℝ) : ((max x y : ℝ) : EReal) = max (x : EReal) (y : EReal) :=
  EReal.coe_strictMono.monotone.map_max

theorem ereal_coe_min (x y : ℝ) : ((min x y : ℝ) : EReal) = min (x : EReal) (y : EReal) :=
  EReal.coe_strictMono.monotone.map_min

/-- Continuous real functions on the compact space `(ℙⁿ)^an` are bounded. -/
theorem exists_abs_le_of_continuous {f : ProjBerk k n → ℝ} (hf : Continuous f) :
    ∃ C, ∀ v, |f v| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun v => by simpa only [Real.norm_eq_abs] using hC v (mem_univ v)⟩

/-- Rational PL functions are bounded. -/
theorem IsRatPL.exists_abs_le {f : ProjBerk k n → ℝ} (hf : IsRatPL f) : ∃ C, ∀ v, |f v| ≤ C :=
  exists_abs_le_of_continuous hf.continuous

/-- A finite-valued FS function is the coercion of its real part. -/
theorem IsFiniteRatFS.coe_toReal_eq {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFiniteRatFS a φ) :
    (fun v => ((φ v).toReal : EReal)) = φ :=
  funext fun v => EReal.coe_toReal (h.isFS.ne_top v) (h.ne_bot v)

/-- Rational PL functions in terms of real-valued finite rational FS functions. -/
theorem isRatPL_iff {f : ProjBerk k n → ℝ} :
    IsRatPL f ↔ ∃ (a b : ℚ) (φ ψ : ProjBerk k n → ℝ), IsFiniteRatFS a (fun v => (φ v : EReal)) ∧
      IsFiniteRatFS b (fun v => (ψ v : EReal)) ∧ ∀ v, f v = φ v - ψ v := by
  constructor
  · rintro ⟨a, b, φ, ψ, hφ, hψ, hf⟩
    exact ⟨a, b, fun v => (φ v).toReal, fun v => (ψ v).toReal, by rwa [hφ.coe_toReal_eq],
      by rwa [hψ.coe_toReal_eq], hf⟩
  · rintro ⟨a, b, φ, ψ, hφ, hψ, hf⟩
    exact ⟨a, b, _, _, hφ, hψ, fun v => by simp only [EReal.toReal_coe]; exact hf v⟩

/-! ### Rational PL functions form a separating lattice (`lem:bj-pl-lattice`) -/

/-- `lem:bj-pl-lattice`: rational PL functions are stable under maxima, via
`max(φ₁ - ψ₁, φ₂ - ψ₂) = max(φ₁ + ψ₂, φ₂ + ψ₁) - (ψ₁ + ψ₂)`. -/
theorem IsRatPL.max {f g : ProjBerk k n → ℝ} (hf : IsRatPL f) (hg : IsRatPL g) :
    IsRatPL fun v => Max.max (f v) (g v) := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := isRatPL_iff.1 hf
  obtain ⟨a', b', φ', ψ', hφ', hψ', hg⟩ := isRatPL_iff.1 hg
  have h₁ : IsFiniteRatFS (a + b') fun v => ((φ v + ψ' v : ℝ) : EReal) := by
    simpa only [EReal.coe_add] using hφ.add hψ'
  have h₂ : IsFiniteRatFS (a' + b) fun v => ((φ' v + ψ v : ℝ) : EReal) := by
    simpa only [EReal.coe_add] using hφ'.add hψ
  have h₃ : IsFiniteRatFS (Max.max (a + b') (a' + b))
      fun v => ((Max.max (φ v + ψ' v) (φ' v + ψ v) : ℝ) : EReal) := by
    simpa only [ereal_coe_max] using
      (h₁.mono_class (le_max_left _ _)).max (h₂.mono_class (le_max_right _ _))
  have h₄ : IsFiniteRatFS (b + b') fun v => ((ψ v + ψ' v : ℝ) : EReal) := by
    simpa only [EReal.coe_add] using hψ.add hψ'
  refine isRatPL_iff.2 ⟨_, _, _, _, h₃, h₄, fun v => ?_⟩
  rw [hf v, hg v, ← max_sub_sub_right]
  congr 1 <;> ring

/-- `lem:bj-pl-lattice`: rational PL functions are stable under minima. -/
theorem IsRatPL.min {f g : ProjBerk k n → ℝ} (hf : IsRatPL f) (hg : IsRatPL g) :
    IsRatPL fun v => Min.min (f v) (g v) := by
  simpa only [max_neg_neg, neg_neg] using (hf.neg.max hg.neg).neg

/-- `log|s|` is a rational FS function of class `d` for a nonzero form `s` of degree `d`. -/
theorem isRatFS_logAbs {d : ℕ} {s : MvPolynomial (Fin (n + 1)) k} (hs : s.IsHomogeneous d)
    (hs0 : s ≠ 0) : IsRatFS (d : ℚ) (logAbs (k := k) (n := n) s) := by
  classical
  refine ⟨⟨1, one_pos, d, by simp, {(s, 0)}, fun t ht => ?_,
    ⟨(s, 0), Finset.mem_singleton_self _, hs0⟩⟩, fun t ht => ?_, ?_⟩
  · rw [Finset.mem_singleton.1 ht]; exact hs
  · rw [Finset.mem_singleton.1 ht]; exact ⟨0, by simp⟩
  · funext v
    simp [FSData.eval]

/-- Two distinct points of `(ℙⁿ)^an` differ on some form: points are graded, so their values on a
polynomial are the maxima of their values on its homogeneous components. -/
theorem exists_isHomogeneous_val_ne {v w : ProjBerk k n} (h : v ≠ w) :
    ∃ (d : ℕ) (s : MvPolynomial (Fin (n + 1)) k), s.IsHomogeneous d ∧ v.1.val s ≠ w.1.val s := by
  by_contra! H
  refine h (ProjBerk.ext (Berk.ext (Valuation.ext fun f => ?_)))
  rw [v.isGraded f, w.isGraded f]
  exact Finset.sup_congr rfl fun d _ =>
    H d _ (MvPolynomial.homogeneousComponent_isHomogeneous d f)

/-- `lem:bj-pl-lattice`: rational PL functions **separate the points** of `(ℙⁿ)^an`. If `v ≠ w`,
some form `s` of degree `d` has `|s|_v ≠ |s|_w`, and `max(log|s|, c) ∈ H_ℚ(d)` separates `v` and
`w` for a rational `c` below the larger of the two values. -/
theorem exists_isRatPL_ne {v w : ProjBerk k n} (h : v ≠ w) : ∃ f, IsRatPL f ∧ f v ≠ f w := by
  obtain ⟨d, s, hs, hne⟩ := exists_isHomogeneous_val_ne h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hne
  have key : ∀ v w : ProjBerk k n, logAbs s v < logAbs s w → ∃ f, IsRatPL f ∧ f v ≠ f w := by
    intro v w hlt
    obtain ⟨r, hr⟩ : ∃ r : ℝ, logAbs s w = r :=
      ⟨(logAbs s w).toReal, (EReal.coe_toReal (logAbs_ne_top s w) (ne_bot_of_gt hlt)).symm⟩
    obtain ⟨c, hc⟩ := exists_rat_lt r
    have hc' : ((c : ℝ) : EReal) < logAbs s w := by rw [hr]; exact_mod_cast hc
    have hF := (isRatFS_logAbs hs hs0).max_const c
    refine ⟨_, hF.isRatPL, fun heq => ?_⟩
    have hlt' : Max.max (logAbs s v) ((c : ℝ) : EReal) < Max.max (logAbs s w) ((c : ℝ) : EReal) :=
      (max_lt hlt hc').trans_le (le_max_left _ _)
    have hv := EReal.coe_toReal (hF.isFS.ne_top v) (hF.ne_bot v)
    have hw := EReal.coe_toReal (hF.isFS.ne_top w) (hF.ne_bot w)
    rw [← hv, ← hw, heq] at hlt'
    exact lt_irrefl _ hlt'
  have hne' : logAbs s v ≠ logAbs s w := by
    intro heq
    rw [logAbs_def, logAbs_def] at heq
    exact hne (ENNReal.coe_injective (ENNReal.log_injective heq))
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact key v w hlt
  · obtain ⟨f, hf, hfne⟩ := key w v hlt
    exact ⟨f, hf, hfne.symm⟩

/-! ### Density (`thm:bj-pl-dense`) -/

/-- **Density of PL functions** (BJ22 PLdense, `thm:bj-pl-dense`): every continuous
function on `(ℙⁿ)^an` is a uniform limit of rational PL functions. The uniform closure `L` of the
PL functions (described pointwise) is a lattice containing the real constants, and it separates
points strongly: if `ψ` is PL with `ψ(x) ≠ ψ(y)`, the functions `α ψ + β ∈ L` take arbitrary values
at `x` and `y`. The lattice Stone–Weierstrass theorem gives `closure L = C⁰`. -/
theorem exists_isRatPL_abs_sub_lt {f : ProjBerk k n → ℝ} (hf : Continuous f) {ε : ℝ}
    (hε : 0 < ε) : ∃ ψ, IsRatPL ψ ∧ ∀ v, |f v - ψ v| < ε := by
  set L : Set C(ProjBerk k n, ℝ) :=
    {g | ∀ ε : ℝ, 0 < ε → ∃ ψ, IsRatPL ψ ∧ ∀ v, |g v - ψ v| < ε} with hL
  -- real constants lie in `L`
  have hconst : ∀ c : ℝ, ContinuousMap.const (ProjBerk k n) c ∈ L := by
    intro c ε hε
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show c - ε < c + ε by linarith)
    refine ⟨fun _ => (q : ℝ), isRatPL_const q, fun v => ?_⟩
    rw [ContinuousMap.const_apply, abs_lt]
    constructor <;> linarith
  have hinf : ∀ g ∈ L, ∀ g' ∈ L, g ⊓ g' ∈ L := by
    intro g hg g' hg' ε hε
    obtain ⟨ψ, hψ, hgψ⟩ := hg ε hε
    obtain ⟨ψ', hψ', hgψ'⟩ := hg' ε hε
    refine ⟨_, hψ.min hψ', fun v => ?_⟩
    rw [ContinuousMap.inf_apply]
    exact (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt (hgψ v) (hgψ' v))
  have hsup : ∀ g ∈ L, ∀ g' ∈ L, g ⊔ g' ∈ L := by
    intro g hg g' hg' ε hε
    obtain ⟨ψ, hψ, hgψ⟩ := hg ε hε
    obtain ⟨ψ', hψ', hgψ'⟩ := hg' ε hε
    refine ⟨_, hψ.max hψ', fun v => ?_⟩
    rw [ContinuousMap.sup_apply]
    exact (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt (hgψ v) (hgψ' v))
  have hsep : L.SeparatesPointsStrongly := by
    intro w x y
    by_cases hxy : x = y
    · subst hxy
      exact ⟨ContinuousMap.const _ (w x), hconst _, rfl, rfl⟩
    obtain ⟨ψ, hψ, hne⟩ := exists_isRatPL_ne hxy
    have hd : ψ x - ψ y ≠ 0 := sub_ne_zero.2 hne
    set α : ℝ := (w x - w y) / (ψ x - ψ y) with hα
    set β : ℝ := w x - α * ψ x with hβ
    refine ⟨⟨fun z => α * ψ z + β, (continuous_const.mul hψ.continuous).add continuous_const⟩,
      ?_, ?_, ?_⟩
    · intro ε hε
      obtain ⟨C, hC⟩ := hψ.exists_abs_le
      have hC1 : 0 < |C| + 1 := by positivity
      have hδ : 0 < ε / (2 * (|C| + 1)) := by positivity
      obtain ⟨q, hq₁, hq₂⟩ :=
        exists_rat_btwn (show α - ε / (2 * (|C| + 1)) < α + ε / (2 * (|C| + 1)) by linarith)
      obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show β - ε / 2 < β + ε / 2 by linarith)
      refine ⟨fun z => (q : ℝ) * ψ z + (r : ℝ), (hψ.smul q).add (isRatPL_const r), fun z => ?_⟩
      have hαq : |α - q| ≤ ε / (2 * (|C| + 1)) := abs_le.2 ⟨by linarith, by linarith⟩
      have hβr : |β - r| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      have hψz : |ψ z| ≤ |C| + 1 := (hC z).trans ((le_abs_self C).trans (by linarith))
      change |α * ψ z + β - ((q : ℝ) * ψ z + (r : ℝ))| < ε
      calc |α * ψ z + β - ((q : ℝ) * ψ z + (r : ℝ))| = |(α - q) * ψ z + (β - r)| := by ring_nf
        _ ≤ |α - q| * |ψ z| + |β - r| := by
          rw [← abs_mul]; exact abs_add_le _ _
        _ < ε / (2 * (|C| + 1)) * (|C| + 1) + ε / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hβr
          exact mul_le_mul hαq hψz (abs_nonneg _) hδ.le
        _ = ε := by field_simp; ring
    · change α * ψ x + β = w x
      rw [hβ]; ring
    · change α * ψ y + β = w y
      have : α * (ψ x - ψ y) = w x - w y := by rw [hα]; field_simp
      rw [hβ]; linarith
  have hclosure := ContinuousMap.sublattice_closure_eq_top L ⟨_, hconst 0⟩ hinf hsup hsep
  have hfL : (⟨f, hf⟩ : C(ProjBerk k n, ℝ)) ∈ closure L := by rw [hclosure]; trivial
  obtain ⟨g, hgL, hfg⟩ := Metric.mem_closure_iff.1 hfL (ε / 2) (half_pos hε)
  obtain ⟨ψ, hψ, hgψ⟩ := hgL (ε / 2) (half_pos hε)
  rw [ContinuousMap.dist_lt_iff (half_pos hε)] at hfg
  refine ⟨ψ, hψ, fun v => ?_⟩
  have h₁ : |f v - g v| < ε / 2 := by
    have := hfg v
    rwa [Real.dist_eq] at this
  calc |f v - ψ v| ≤ |f v - g v| + |g v - ψ v| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h₁ (hgψ v)
    _ = ε := add_halves ε

/-- **Density of PL functions** (`thm:bj-pl-dense`), topological form: rational PL functions are
dense in `C((ℙⁿ)^an, ℝ)` for the topology of uniform convergence. -/
theorem dense_setOf_isRatPL : Dense {f : C(ProjBerk k n, ℝ) | IsRatPL f} := by
  refine fun f => Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨ψ, hψ, hfψ⟩ := exists_isRatPL_abs_sub_lt f.continuous (half_pos hε)
  refine ⟨⟨ψ, hψ.continuous⟩, hψ, ?_⟩
  refine lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).2 fun v => ?_) (half_lt_self hε)
  rw [Real.dist_eq]
  exact (hfψ v).le

/-! ### Approximation of usc functions from above (`lem:bj-usc-pl`) -/

/-- `lem:bj-usc-pl`, nonemptiness: a usc function `h : (ℙⁿ)^an → [-∞, +∞)` lies below a rational
PL function, indeed below a rational constant (`h` attains its maximum on the compact space). -/
theorem exists_isRatPL_gt {h : ProjBerk k n → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ v, h v ≠ ⊤) : ∃ ψ, IsRatPL ψ ∧ ∀ v, h v < ψ v := by
  obtain ⟨a, -, ha⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨triv, mem_univ _⟩ isCompact_univ
    (hh.upperSemicontinuousOn univ)
  obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 (htop a))
  obtain ⟨q, hq⟩ := exists_rat_gt r
  refine ⟨fun _ => (q : ℝ), isRatPL_const q, fun v => ?_⟩
  exact ((isMaxOn_iff.1 ha v (mem_univ v)).trans_lt hr).trans (EReal.coe_lt_coe_iff.2 hq)

/-- `lem:bj-usc-pl`, the infimum: if `h : (ℙⁿ)^an → [-∞, +∞)` is usc and `h(v) < c`, there is a
rational PL function `ψ > h` with `ψ(v) < c`. With reals `h(v) < r < r + 3δ < c`, Urysohn's lemma
gives a continuous `g ≥ r` with `g > h`, `g(v) = r` (equal to a large constant on the closed set
`{h ≥ r}`), and a PL function uniformly `δ`-close to `g + 2δ` works. -/
theorem exists_isRatPL_gt_apply_lt {h : ProjBerk k n → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ v, h v ≠ ⊤) {v : ProjBerk k n} {c : EReal} (hc : h v < c) :
    ∃ ψ, IsRatPL ψ ∧ (∀ w, h w < ψ w) ∧ (ψ v : EReal) < c := by
  obtain ⟨r₁, hr₁, hr₁c⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨r, hr, hrr₁⟩ := EReal.lt_iff_exists_real_btwn.1 hr₁
  have hrr₁' : r < r₁ := EReal.coe_lt_coe_iff.1 hrr₁
  set δ : ℝ := (r₁ - r) / 3 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  -- a real upper bound `C ≥ r` of `h`
  obtain ⟨ψ₀, hψ₀, hgt₀⟩ := exists_isRatPL_gt hh htop
  obtain ⟨C₀, hC₀⟩ := hψ₀.exists_abs_le
  set C : ℝ := Max.max C₀ r with hC_def
  have hhC : ∀ w, h w < C := fun w =>
    (hgt₀ w).trans_le (EReal.coe_le_coe_iff.2 (((le_abs_self _).trans (hC₀ w)).trans
      (le_max_left _ _)))
  have hrC : r ≤ C := le_max_right _ _
  -- Urysohn's lemma for `{v}` and the closed set `F = {h ≥ r}`
  set F : Set (ProjBerk k n) := {w | (r : EReal) ≤ h w} with hF_def
  have hF : IsClosed F := by
    have h₁ : F = (h ⁻¹' Iio (r : EReal))ᶜ := by
      ext w; simp [hF_def, not_lt]
    rw [h₁]
    exact (hh.isOpen_preimage _).isClosed_compl
  have hvF : Disjoint {v} F := by
    rw [disjoint_singleton_left]
    exact not_le.2 hr
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed isClosed_singleton hF hvF
  set g : ProjBerk k n → ℝ := fun w => r + (C + 1 - r) * f w with hg_def
  have hgc : Continuous g := by fun_prop
  have hfv : f v = 0 := hf0 (mem_singleton v)
  obtain ⟨ψ, hψ, hψg⟩ := exists_isRatPL_abs_sub_lt (f := fun w => g w + 2 * δ)
    (hgc.add continuous_const) hδ
  refine ⟨ψ, hψ, fun w => ?_, ?_⟩
  · have h₁ : g w + δ < ψ w := by have := abs_lt.1 (hψg w); linarith
    have h₂ : h w < g w := by
      by_cases hw : w ∈ F
      · have : f w = 1 := hf1 hw
        refine (hhC w).trans (EReal.coe_lt_coe_iff.2 ?_)
        rw [hg_def]; dsimp only; rw [this]; linarith
      · have h₃ : h w < r := not_le.1 hw
        refine h₃.trans_le (EReal.coe_le_coe_iff.2 ?_)
        rw [hg_def]; dsimp only
        have := (hf01 w).1
        nlinarith
    exact h₂.trans (EReal.coe_lt_coe_iff.2 (by linarith))
  · have h₁ : ψ v < g v + 3 * δ := by have := abs_lt.1 (hψg v); linarith
    have h₂ : g v + 3 * δ = r₁ := by rw [hg_def]; dsimp only; rw [hfv, hδ_def]; ring
    exact (EReal.coe_lt_coe_iff.2 (h₁.trans_eq h₂)).trans hr₁c

/-- **Approximation of usc functions from above** (`lem:bj-usc-pl`): a usc function
`h : (ℙⁿ)^an → [-∞, +∞)` is the pointwise infimum of the rational PL functions `ψ > h`. -/
theorem iInf_isRatPL_gt {h : ProjBerk k n → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ v, h v ≠ ⊤) (v : ProjBerk k n) :
    ⨅ (ψ : ProjBerk k n → ℝ) (_ : IsRatPL ψ ∧ ∀ w, h w < ψ w), (ψ v : EReal) = h v := by
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    (le_iInf₂ fun ψ hψ => (hψ.2 v).le)
  obtain ⟨ψ, hψ, hgt, hlt⟩ := exists_isRatPL_gt_apply_lt hh htop hc
  exact (iInf₂_le ψ ⟨hψ, hgt⟩).trans hlt.le

/-- `lem:bj-usc-pl` as a decreasing net: a usc function `h : (ℙⁿ)^an → [-∞, +∞)` is the limit of a
decreasing net of rational PL functions `ψᵢ > h`, indexed by the set of all such functions ordered
by reverse pointwise order (directed by `ProjBerk.IsRatPL.min`). -/
theorem exists_antitone_isRatPL_net {h : ProjBerk k n → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ v, h v ≠ ⊤) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (ψ : ι → ProjBerk k n → ℝ), (∀ i, IsRatPL (ψ i)) ∧ (∀ i w, h w < ψ i w) ∧
        (∀ w, Antitone fun i => ψ i w) ∧ ∀ w, h w = ⨅ i, (ψ i w : EReal) := by
  let ι := {ψ : ProjBerk k n → ℝ // IsRatPL ψ ∧ ∀ w, h w < ψ w}ᵒᵈ
  have : IsDirected ι (· ≤ ·) := ⟨fun i j => ⟨OrderDual.toDual
    ⟨fun w => Min.min ((OrderDual.ofDual i).1 w) ((OrderDual.ofDual j).1 w),
      (OrderDual.ofDual i).2.1.min (OrderDual.ofDual j).2.1, fun w => by
        rw [ereal_coe_min]
        exact lt_min ((OrderDual.ofDual i).2.2 w) ((OrderDual.ofDual j).2.2 w)⟩,
    fun w => min_le_left _ _, fun w => min_le_right _ _⟩⟩
  have : Nonempty ι := by
    obtain ⟨ψ, hψ⟩ := exists_isRatPL_gt hh htop
    exact ⟨OrderDual.toDual ⟨ψ, hψ⟩⟩
  refine ⟨ι, inferInstance, inferInstance, inferInstance, fun i => (OrderDual.ofDual i).1,
    fun i => (OrderDual.ofDual i).2.1, fun i => (OrderDual.ofDual i).2.2,
    fun w i j hij => hij w, fun w => ?_⟩
  exact (iInf_isRatPL_gt hh htop w).symm.trans iInf_subtype'

/-- **Comparison with usc functions** (`lem:bj-usc-pl`): if `u ≤ ψ` for every rational PL function
`ψ > h`, where `h : (ℙⁿ)^an → [-∞, +∞)` is usc, then `u ≤ h`. -/
theorem le_of_forall_isRatPL_gt {h u : ProjBerk k n → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ v, h v ≠ ⊤) (hu : ∀ ψ, IsRatPL ψ → (∀ w, h w < ψ w) → ∀ v, u v ≤ ψ v) : u ≤ h :=
  fun v => (iInf_isRatPL_gt hh htop v) ▸ le_iInf₂ fun ψ hψ => hu ψ hψ.1 hψ.2 v

end ProjBerk

end EnvelopeProperty
