/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.FS
import EnvelopeProperty.Local.Hull
import EnvelopeProperty.Local.Imports

/-!
# Rossi's local maximum principle

This file proves the non-Archimedean version of Rossi's local maximum principle,
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Lemma 5.15 (`lem:rossi`; Wu, *On the local theory of non-archimedean psh functions*,
Theorem 5.6), on the analytification `Y^an = Berk k A` of a normal affine variety `Y = Spec A` over
an algebraically closed trivially valued field `k`:

> Let `K ⊆ Y^an` be compact, `x ∈ K̂`, and `V` a relatively compact open neighbourhood of `x`
> with `V̄ ∩ K = ∅`. Then `x` lies in the hull of `∂V ∩ K̂`.

The condition `x ∉ K` follows from `x ∈ V` and `V̄ ∩ K = ∅`.

## Proof

Suppose not. The power trick (`exists_lt_logAbs_of_notMem_hull`) gives `f ∈ A` and `t ∈ ℚ` with
`sup_{∂V ∩ K̂} log|f| < t < log|f(x)|`. The compact set `E = ∂V ∩ {log|f| ≥ t}` is disjoint from
the polynomially convex compact set `K̂`, so FHX Lemma 5.14(1) (`exists_fs_polyhedral_nhd`) gives
`g ∈ FS(Y)` with `g ≥ 0`, `g = 0` on `K̂` and `g > 1` on `E`. Choose an integer `C > 0` with
`C > sup_{V̄} (log|f| - t)` and put `v = max{C g, log|f| - t}` on `V` and `v = C g` off `V`. On
`∂V` we have `log|f| - t < C g`, so the gluing lemma `IsConvexPLOn.piecewise_max` shows that `v`
is convex PL on `Y^an`; it is bounded by the FS function `max{C g, log|f| - t}`, hence of
logarithmic growth, so `v ∈ ℛ(Y)` by the imported FHX Lemma 5.11(6)
(`WuRegularization.localToGlobal`). But `v = 0` on `K` and `v(x) ≥ log|f(x)| - t > 0`, which
contradicts the hull inequality for regularizable functions (`IsRegularizable.satisfiesHullIneq`).

The imported hypothesis `WuRegularization` is the only input beyond the formalized theory; see
`EnvelopeProperty.Local.Imports`.

## Main result

* `EnvelopeProperty.mem_hull_frontier_inter_hull`: Rossi's local maximum principle.
-/

open scoped NNReal ENNReal Topology

open Set

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

/-- **Rossi's local maximum principle** (FHX Lemma 5.15, `lem:rossi`). Let `Y = Spec A` be a
normal affine variety over the algebraically closed trivially valued field `k`, `K ⊆ Y^an`
compact, `x ∈ K̂`, and `V` a relatively compact open neighbourhood of `x` with `V̄ ∩ K = ∅`.
Then `x` lies in the polynomial hull of `∂V ∩ K̂`. (`x ∉ K`, which follows from `x ∈ V` and `V̄ ∩ K = ∅`.) -/
theorem mem_hull_frontier_inter_hull {k : Type u} [Field k] [IsAlgClosed k]
    [WuRegularization.{u, v} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    {K : Set (Berk k A)} (hK : IsCompact K) {x : Berk k A} (hx : x ∈ hull K)
    {V : Set (Berk k A)} (hV : IsOpen V) (hxV : x ∈ V) (hVc : IsCompact (closure V))
    (hVK : Disjoint (closure V) K) : x ∈ hull (frontier V ∩ hull K) := by
  classical
  by_contra hx'
  -- Separation of `x` from `∂V ∩ K̂` by `log|f|` and a rational threshold `t`.
  obtain ⟨f, t, hfL, hfx⟩ := exists_lt_logAbs_of_notMem_hull hx' 0
  -- The compact set `E = ∂V ∩ {log|f| ≥ t}`, disjoint from `K̂`.
  set E : Set (Berk k A) := frontier V ∩ {y | ((t : ℝ) : EReal) ≤ logAbs f y} with hE
  have hEc : IsCompact E :=
    hVc.of_isClosed_subset (isClosed_frontier.inter (isClosed_setOf_le_logAbs f _))
      (inter_subset_left.trans frontier_subset_closure)
  have hKE : hull K ⊆ Eᶜ := by
    intro y hyK hyE
    have hle : logAbs f y ≤ ⨆ z ∈ frontier V ∩ hull K, logAbs f z :=
      le_iSup₂ (f := fun z (_ : z ∈ frontier V ∩ hull K) => logAbs f z) y ⟨hyE.1, hyK⟩
    exact lt_irrefl _ (hyE.2.trans_lt (hle.trans_lt hfL))
  -- The polyhedral neighbourhood: `g ≥ 0`, `g = 0` on `K̂`, `g > 1` on `E`.
  obtain ⟨g, hg0, hgK, hgE⟩ := exists_fs_polyhedral_nhd (isCompact_hull hK) (isPolyConvex_hull K)
    hEc.isClosed.isOpen_compl hKE
  have hg0' : ∀ y, 0 ≤ g.evalReal y := fun y => by
    rw [← EReal.coe_le_coe_iff, g.coe_evalReal]; exact hg0 y
  have hgK' : ∀ y ∈ hull K, g.evalReal y = 0 := fun y hy => by
    have h : g.eval y = 0 := (interior_subset (hgK hy) : y ∈ {x | g.eval x = 0})
    rw [← EReal.coe_eq_coe_iff, g.coe_evalReal, h, EReal.coe_zero]
  have hgE' : ∀ y ∈ E, 1 < g.evalReal y := fun y hy => by
    by_contra h
    refine hgE (show g.eval y ≤ 1 from ?_) hy
    rw [← g.coe_evalReal, ← EReal.coe_one, EReal.coe_le_coe_iff]
    exact not_lt.1 h
  -- A bound for `log|f|` on `V̄` and the integer `C`.
  obtain ⟨R, hR⟩ := exists_abs_le_of_isCompact hVc f
  have hfR : ∀ y ∈ closure V, y.val f ≠ 0 → Real.log (y.val f : ℝ) ≤ R := fun y hy hy0 => by
    have hpos : (0 : ℝ) < y.val f := by
      rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hy0
    have : ((y.val f : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast hR y hy
    linarith [Real.log_le_sub_one_of_pos hpos]
  obtain ⟨C, hC⟩ := exists_nat_gt (max ((R : ℝ) - t) 0)
  have hCR : (R : ℝ) - t < C := (le_max_left _ _).trans_lt hC
  have hC0 : (0 : ℝ) < C := (le_max_right _ _).trans_lt hC
  have hCq : (0 : ℚ) < C := by exact_mod_cast hC0
  -- The functions `C g` and `log|f| - t`.
  set G : FSData k A := g.smul (C : ℚ) hCq with hG
  have hGeval : ∀ y, G.eval y = (((C : ℝ) * g.evalReal y : ℝ) : EReal) := fun y => by
    rw [hG, FSData.eval_smul, ← g.coe_evalReal, EReal.coe_mul, Rat.cast_natCast]
  set w : Berk k A → EReal := fsTerm (f, (1 : ℚ), -t) with hw
  have hw_coe : ∀ y, y.val f ≠ 0 → w y = ((Real.log (y.val f : ℝ) - t : ℝ) : EReal) :=
    fun y hy => by
      rw [hw, fsTerm_eq_coe (t := (f, (1 : ℚ), -t)) hy]
      congr 1
      push_cast
      ring
  have hw_bot : ∀ y, y.val f = 0 → w y = ⊥ := fun y hy =>
    fsTerm_eq_bot (t := (f, (1 : ℚ), -t)) one_pos hy
  -- `f` does not vanish at `x`, and `log|f(x)| - t > 0`.
  have hfx0 : x.val f ≠ 0 := by
    intro h
    rw [(logAbs_eq_bot_iff f x).2 h] at hfx
    exact not_lt_bot hfx
  have hfx' : (t : ℝ) < Real.log (x.val f : ℝ) := by
    rw [logAbs_eq_coe_log hfx0, EReal.coe_lt_coe_iff] at hfx
    linarith
  -- The glued function `v`.
  set U' : Set (Berk k A) := V ∩ {y | y.val f ≠ 0} with hU'
  have hU'o : IsOpen U' := hV.inter (isOpen_setOf_abs_ne_zero f)
  set v : Berk k A → EReal := U'.piecewise (fun y => max (G.eval y) (w y)) G.eval with hv
  -- On `∂V`, `log|f| - t < C g`; hence the gluing condition.
  have hcl : closure {y | y ∈ U' ∧ G.eval y < w y} ∩ univ ⊆ U' := by
    rintro y ⟨hy, -⟩
    have hsub : {y | y ∈ U' ∧ G.eval y < w y} ⊆ closure V ∩ {y | G.eval y ≤ w y} :=
      fun z hz => ⟨subset_closure hz.1.1, hz.2.le⟩
    have hT : IsClosed (closure V ∩ {y | G.eval y ≤ w y}) :=
      isClosed_closure.inter (isClosed_le G.continuous_eval (continuous_fsTerm _))
    obtain ⟨hyV, hyGw⟩ := closure_minimal hsub hT hy
    have hyGw : G.eval y ≤ w y := hyGw
    have hy0 : y.val f ≠ 0 := by
      intro h
      rw [hw_bot y h, hGeval y] at hyGw
      exact EReal.coe_ne_bot _ (le_bot_iff.1 hyGw)
    rw [hGeval y, hw_coe y hy0, EReal.coe_le_coe_iff] at hyGw
    refine ⟨?_, hy0⟩
    by_contra hyV'
    have hyfr : y ∈ frontier V := by rw [hV.frontier_eq]; exact ⟨hyV, hyV'⟩
    have hL := hfR y hyV hy0
    by_cases hty : (t : ℝ) ≤ Real.log (y.val f : ℝ)
    · have hyE : y ∈ E := ⟨hyfr, show ((t : ℝ) : EReal) ≤ logAbs f y by
        rw [logAbs_eq_coe_log hy0]; exact_mod_cast hty⟩
      have h1 := hgE' y hyE
      have : (C : ℝ) < C * g.evalReal y := by nlinarith
      linarith
    · have := mul_nonneg hC0.le (hg0' y)
      linarith
  have hcpl : IsConvexPLOn univ v :=
    IsConvexPLOn.piecewise_max hU'o (subset_univ _) G.isConvexPLOn_univ
      ((isConvexPLOn_fsTerm (f, (1 : ℚ), -t)).mono hU'o inter_subset_right) hcl
  -- `v` has logarithmic growth: it is bounded by the FS function `max{C g, log|f| - t}`.
  have hlog : HasLogGrowth v := by
    refine ⟨G.addTerms {(f, (1 : ℚ), -t)} (by simp), 0, fun y => ?_⟩
    rw [EReal.coe_zero, add_zero, FSData.eval_addTerms, Finset.sup_singleton]
    by_cases hy : y ∈ U'
    · rw [hv, piecewise_eq_of_mem _ _ _ hy]
    · rw [hv, piecewise_eq_of_notMem _ _ _ hy]
      exact le_max_left _ _
  -- The value at `x`.
  have hxU' : x ∈ U' := ⟨hxV, hfx0⟩
  have hvx : 0 < v x := by
    rw [hv, piecewise_eq_of_mem _ _ _ hxU']
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    rw [hw_coe x hfx0, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
    linarith
  -- `v` is regularizable, by the imported local-to-global principle.
  have hreg : IsRegularizable v :=
    WuRegularization.localToGlobal A v ⟨x, ne_bot_of_gt hvx⟩ hlog fun _ _ =>
      ⟨univ, isOpen_univ, subset_univ _, fun _ => v, fun _ => hcpl, fun _ _ => antitone_const,
        fun _ _ => iInf_const.symm⟩
  -- The hull inequality fails: `v = 0` on `K`.
  have hvK : ∀ z ∈ K, v z ≤ 0 := fun z hz => by
    have hzV : z ∉ U' := fun h => disjoint_left.1 hVK (subset_closure h.1) hz
    rw [hv, piecewise_eq_of_notMem _ _ _ hzV, hGeval z, hgK' z (subset_hull K hz), mul_zero,
      EReal.coe_zero]
  have := (hreg.satisfiesHullIneq K hK x hx).trans (iSup₂_le hvK)
  exact absurd hvx (not_lt.2 this)

end EnvelopeProperty
