/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.FS

/-!
# Regularizable functions are finite at the trivial valuation

FHX Lemma 5.11(1) (`lem:regularizable-closure`) asserts that regularizable functions are finite
on `Y^div`; Section 5 only uses finiteness at the trivial valuation `v_triv`, which we prove
directly (blueprint `lem:reg-triv-finite`).

For `g ∈ FS(Y)` and a point `x`, the function `t ↦ g(t·x)` on `[0, ∞)` is a finite maximum of
affine functions, hence convex; in particular `2 g(x) ≤ g(0·x) + g(2·x)`. Moreover
`g(0·x) ≤ g(v_triv)`. Passing to a decreasing limit, `u(v_triv) = -∞` would force `u ≡ -∞`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- `log |f|` is monotone in the value `|f|`. -/
theorem logAbs_le_logAbs_of_val_le {f : A} {x y : Berk k A} (h : x.val f ≤ y.val f) :
    logAbs f x ≤ logAbs f y :=
  ENNReal.log_monotone (ENNReal.coe_le_coe.2 h)

theorem fsTerm_mono {t : A × ℚ × ℚ} (ht : 0 ≤ t.2.1) {x y : Berk k A}
    (h : x.val t.1 ≤ y.val t.1) : fsTerm t x ≤ fsTerm t y := by
  unfold fsTerm
  exact add_le_add (mul_le_mul_of_nonneg_left (logAbs_le_logAbs_of_val_le h)
    (by exact_mod_cast ht)) le_rfl

namespace FSData

/-- Monotonicity of FS functions under the comparison of all absolute values. -/
theorem eval_mono (g : FSData k A) {x y : Berk k A} (h : ∀ f, x.val f ≤ y.val f) :
    g.eval x ≤ g.eval y := by
  unfold eval
  refine max_le_max le_rfl (Finset.sup_le fun t ht => ?_)
  exact (fsTerm_mono (g.pos t ht).le (h t.1)).trans
    (Finset.le_sup (f := fun t => fsTerm t y) ht)

/-- Convexity along the scaling ray, at `0`, `1`, `2`. -/
theorem two_mul_eval_le (g : FSData k A) (x : Berk k A) :
    2 * g.eval x ≤ g.eval (zeroScale x) + g.eval (rpow 2 two_pos x) := by
  classical
  have hterm : ∀ t ∈ g.terms, 2 * fsTerm t x ≤ fsTerm t (zeroScale x) + fsTerm t (rpow 2 two_pos x) := by
    intro t ht
    have ha : (0 : ℝ) < t.2.1 := by exact_mod_cast g.pos t ht
    by_cases hf : x.val t.1 = 0
    · have : fsTerm t x = ⊥ := by
        unfold fsTerm
        rw [(logAbs_eq_bot_iff _ _).2 hf, EReal.coe_mul_bot_of_pos ha, EReal.bot_add]
      rw [this, show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, EReal.coe_mul_bot_of_pos two_pos]
      exact bot_le
    · have h0 : (zeroScale x).val t.1 ≠ 0 := by
        rw [Ne, zeroScale_val_eq_zero_iff]; exact hf
      have h2 : (rpow 2 two_pos x).val t.1 ≠ 0 := by
        rw [rpow_val_apply]; exact (NNReal.rpow_pos (pos_iff_ne_zero.2 hf)).ne'
      unfold fsTerm
      rw [logAbs_eq_coe_log hf, logAbs_eq_coe_log h0, logAbs_eq_coe_log h2,
        zeroScale_val_of_ne_zero hf, rpow_val_apply, NNReal.coe_rpow,
        Real.log_rpow (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hf))]
      simp only [NNReal.coe_one, Real.log_one]
      rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl]
      norm_cast
      apply le_of_eq
      push_cast
      ring
  unfold eval
  -- `2 max(b₀, sup) ≤ max(b₀, sup) + max(b₀, sup)` termwise
  have hb : ∀ y : Berk k A, ((g.const : ℝ) : EReal) ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t y) := fun y => le_max_left _ _
  have hs : ∀ y : Berk k A, ∀ t ∈ g.terms, fsTerm t y ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t y) := fun y t ht =>
    (Finset.le_sup (f := fun t => fsTerm t y) ht).trans (le_max_right _ _)
  rcases le_total (g.terms.sup fun t => fsTerm t x) ((g.const : ℝ) : EReal) with hle | hle
  · rw [max_eq_left hle]
    calc 2 * ((g.const : ℝ) : EReal) = ((g.const : ℝ) : EReal) + ((g.const : ℝ) : EReal) := by
          rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, ← EReal.coe_mul, ← EReal.coe_add]
          congr 1; ring
      _ ≤ _ := add_le_add (hb _) (hb _)
  · rw [max_eq_right hle]
    by_cases hne : g.terms.Nonempty
    · obtain ⟨t, ht, hteq⟩ := Finset.exists_mem_eq_sup g.terms hne fun t => fsTerm t x
      rw [hteq]
      exact (hterm t ht).trans (add_le_add (hs _ t ht) (hs _ t ht))
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne] at hle
      simp only [Finset.sup_empty] at hle
      exact absurd hle (not_le.2 (EReal.bot_lt_coe _))

/-- `g(0·x) ≤ g(v_triv)` on a domain. -/
theorem eval_zeroScale_le_triv [IsDomain A] (g : FSData k A) (x : Berk k A) :
    g.eval (zeroScale x) ≤ g.eval (triv : Berk k A) :=
  g.eval_mono fun f => zeroScale_val_le_triv x f

end FSData

/-- **Regularizable functions are finite at the trivial valuation** (FHX Lemma 5.11(1) at
`v_triv`, blueprint `lem:reg-triv-finite`). -/
theorem IsRegularizable.triv_ne_bot [IsDomain A] {u : Berk k A → EReal} (hu : IsRegularizable u) :
    u (triv : Berk k A) ≠ ⊥ := by
  obtain ⟨⟨x, hx⟩, g, hanti, hlim⟩ := hu
  intro hbot
  rw [hlim] at hbot
  apply hx
  rw [hlim x]
  by_contra hne
  have hmtop : (⨅ j, (g j).eval x) ≠ ⊤ :=
    ne_top_of_le_ne_top ((g 0).eval_ne_top x) (iInf_le _ 0)
  obtain ⟨mr, hmr⟩ : ∃ mr : ℝ, (mr : EReal) = ⨅ j, (g j).eval x :=
    ⟨_, EReal.coe_toReal hmtop hne⟩
  set c := (g 0).evalReal (rpow 2 two_pos x) with hc
  have key : ∀ j, ((2 * mr - c : ℝ) : EReal) ≤ (g j).eval (triv : Berk k A) := by
    intro j
    have h1 : (mr : EReal) ≤ (g j).eval x := hmr ▸ iInf_le _ j
    have h2 := (g j).two_mul_eval_le x
    have h3 := (g j).eval_zeroScale_le_triv x
    have h4 : (g j).eval (rpow 2 two_pos x) ≤ (g 0).eval (rpow 2 two_pos x) :=
      hanti _ (Nat.zero_le j)
    rw [← (g j).coe_evalReal x] at h1 h2
    rw [← (g j).coe_evalReal (zeroScale x), ← (g j).coe_evalReal (rpow 2 two_pos x)] at h2
    rw [← (g j).coe_evalReal (zeroScale x), ← (g j).coe_evalReal triv] at h3
    rw [← (g j).coe_evalReal (rpow 2 two_pos x), ← (g 0).coe_evalReal (rpow 2 two_pos x)] at h4
    rw [← (g j).coe_evalReal triv]
    have h2' : (2 : EReal) * ((g j).evalReal x : EReal) =
        ((2 * (g j).evalReal x : ℝ) : EReal) := by
      rw [EReal.coe_mul]; rfl
    rw [h2', ← EReal.coe_add] at h2
    norm_cast at h1 h2 h3 h4 ⊢
    rw [← hc] at h4
    linarith
  have : ((2 * mr - c : ℝ) : EReal) ≤ ⊥ := hbot ▸ le_iInf key
  exact EReal.coe_ne_bot _ (le_bot_iff.1 this)

/-- Regularizable functions take a finite value at the trivial valuation. -/
theorem IsRegularizable.triv_ne_top {u : Berk k A → EReal} [IsDomain A]
    (hu : IsRegularizable u) : u (triv : Berk k A) ≠ ⊤ := by
  obtain ⟨_, g, _, hlim⟩ := hu
  rw [hlim]
  exact ne_top_of_le_ne_top ((g 0).eval_ne_top _) (iInf_le _ 0)

end EnvelopeProperty
