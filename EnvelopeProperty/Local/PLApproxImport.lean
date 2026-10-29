/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.FS
import EnvelopeProperty.Local.Imports

/-!
# Approximation of convex PL functions standard at infinity (imported hypothesis)

This file introduces the hypothesis class `ConvexPLApproximation k`, the statement
`thm:wu-pl-approx` of the blueprint chapter `sec:wu-discharge`:

> Let `Y = Spec A` be a normal affine variety over the algebraically closed trivially valued field
> `k`, let `h ∈ FS(Y)`, and let `w` be convex PL on `Y^an` with `w = h` outside a compact set
> (`w` is *standard at infinity* with respect to `h`, `def:wu-standard`). For every rational
> `c > 1` there are `h_j ∈ FS(Y)` decreasing to `w` with `h_j ≤ c h + C_j`.

It is the special case of Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Lemma 5.11(5),(6) (`lem:regularizable-closure`), recorded as `WuRegularization k`,
for convex PL functions standard at infinity: `ConvexPLApproximation.of_wuRegularization`
(`lem:wu-pl-special-case`). Conversely, `EnvelopeProperty.Local.WuReduction` derives
`WuRegularization k` from `ConvexPLApproximation k` by affine arguments on `Y^an`
(`thm:wu-growth-control`, `thm:wu-local-to-global`), so the two hypotheses are equivalent and
replacing the former by the latter does not enlarge the trust boundary. The statement is implied by
Wu, *On the local theory of non-archimedean psh functions*, Lemma 3.24(1)
(psh_PL_functions_are_pshlogreg), whose proof uses positivity on a normal projective
compactification (FHX Lemma 5.5, Boucksom–Jonsson, Chambert-Loir–Ducros), not available in
Mathlib.

Like `WuRegularization k`, the class is a `Prop`-valued hypothesis, **not** an axiom.

## Main declarations

* `ConvexPLApproximation k`: the hypothesis class (decreasing form, a literal special case of FHX
  Lemma 5.11(5),(6)).
* `ConvexPLApproximation.of_wuRegularization`: `WuRegularization k → ConvexPLApproximation k`
  (`lem:wu-pl-special-case`).
* Auxiliary: `IsConvexPLOn.continuousOn` (convex PL functions are continuous) and
  `exists_le_eval_add_of_isConvexPLOn_univ` (a function standard at infinity with respect to `h`
  satisfies `w ≤ h + C`, `def:wu-standard`).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

/-- **Imported (blueprint `thm:wu-pl-approx`; special case of FHX Lemma 5.11(5),(6), implied by
Wu26 Lemma 3.24(1)).** For every normal affine variety `Y = Spec A` over the algebraically closed
trivially valued field `k`, every `h ∈ FS(Y)` and every function `w` that is convex PL on `Y^an`
and equal to `h` outside a compact set `E`: for every rational `c > 1` there are `h_j ∈ FS(Y)`
decreasing to `w` with `h_j - c h` bounded above. -/
class ConvexPLApproximation (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  approx : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A] (w : Berk k A → EReal) (h : FSData k A) (E : Set (Berk k A)),
    IsCompact E → IsConvexPLOn Set.univ w → (∀ x, x ∉ E → w x = h.eval x) →
    ∀ c : ℚ, 1 < c → ∃ hs : ℕ → FSData k A, (∀ x, Antitone fun j => (hs j).eval x) ∧
      (∀ x, w x = ⨅ j, (hs j).eval x) ∧
      ∀ j, ∃ Cj : ℝ, ∀ x, (hs j).eval x ≤ ((c : ℝ) : EReal) * h.eval x + (Cj : EReal)

section Auxiliary

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- A convex PL function is continuous at every point of its domain (same proof as
`IsConvexPLOn.continuousAt` in `Local/WeaklyPSH`, repeated here to keep the imports minimal). -/
private theorem IsConvexPLOn.continuousAt_aux {U : Set (Berk k A)} {u : Berk k A → EReal}
    (h : IsConvexPLOn U u) {x : Berk k A} (hx : x ∈ U) : ContinuousAt u x := by
  obtain ⟨W, hW, hxW, -, n, f, s, hs, hf, hu⟩ := h x hx
  have hlog : ∀ i, ContinuousAt (fun y : Berk k A => Real.log (y.val (f i) : ℝ)) x := fun i =>
    (NNReal.continuous_coe.comp (continuous_abs (f i))).continuousAt.log
      (NNReal.coe_ne_zero.2 (hf x hxW i))
  have htrop : ∀ p ∈ s, ContinuousAt (fun y => tropAffine f p y) x := fun p _ =>
    (tendsto_finsetSum Finset.univ fun i _ => continuousAt_const.mul (hlog i)).add
      continuousAt_const
  have hcont : ContinuousAt (fun y => ((s.sup' hs fun p => tropAffine f p y : ℝ) : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp (ContinuousAt.finset_sup'_apply hs htrop)
  exact hcont.congr (Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) fun y hy => (hu y hy).symm)

/-- A convex PL function is continuous on its (open) domain. -/
theorem IsConvexPLOn.continuousOn {U : Set (Berk k A)} {u : Berk k A → EReal}
    (h : IsConvexPLOn U u) : ContinuousOn u U :=
  fun _ hx => (h.continuousAt_aux hx).continuousWithinAt

/-- A convex PL function is real valued on its domain. -/
private theorem IsConvexPLOn.ne_top_aux {U : Set (Berk k A)} {u : Berk k A → EReal}
    (h : IsConvexPLOn U u) {y : Berk k A} (hy : y ∈ U) : u y ≠ ⊤ := by
  obtain ⟨W, -, hyW, -, n, f, s, hs, -, hu⟩ := h y hy
  rw [hu y hyW]
  exact EReal.coe_ne_top _

/-- A function that is convex PL on `Y^an` and equal to an FS function `h` outside a compact set
`E` satisfies `w ≤ h + C` (`def:wu-standard`): it is continuous and real valued, hence bounded
above on `E`, and `h` is bounded below by its constant term. -/
theorem exists_le_eval_add_of_isConvexPLOn_univ {w : Berk k A → EReal} {h : FSData k A}
    {E : Set (Berk k A)} (hE : IsCompact E) (hw : IsConvexPLOn Set.univ w)
    (hwE : ∀ x, x ∉ E → w x = h.eval x) :
    ∃ C : ℝ, ∀ x, w x ≤ h.eval x + (C : EReal) := by
  -- `w` is bounded above on `E` by some natural number `N`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, E ⊆ {x | w x < (N : ℝ)} := by
    have hopen : ∀ N : ℕ, IsOpen {x | w x < ((N : ℝ) : EReal)} := fun N =>
      isOpen_iff_mem_nhds.2 fun x hx =>
        ((hw.continuousAt_aux (Set.mem_univ x)).eventually (gt_mem_nhds hx))
    have hcover : E ⊆ ⋃ N : ℕ, {x | w x < ((N : ℝ) : EReal)} := by
      intro x _
      have hx := hw.ne_top_aux (Set.mem_univ x)
      obtain ⟨r, hr⟩ : ∃ r : ℝ, w x < r := by
        induction h : w x using EReal.rec with
        | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
        | coe r => exact ⟨r + 1, by exact_mod_cast lt_add_one r⟩
        | top => exact absurd h hx
      obtain ⟨N, hN⟩ := exists_nat_gt r
      exact Set.mem_iUnion.2 ⟨N, hr.trans (by exact_mod_cast hN)⟩
    have hdir : Directed (· ⊆ ·) fun N : ℕ => {x | w x < ((N : ℝ) : EReal)} :=
      Monotone.directed_le fun a b hab x (hx : w x < ((a : ℝ) : EReal)) =>
        show w x < ((b : ℝ) : EReal) from
          lt_of_lt_of_le hx (EReal.coe_le_coe_iff.2 (Nat.cast_le.2 hab))
    exact hE.elim_directed_cover _ hopen hcover hdir
  refine ⟨max 0 ((N : ℝ) - h.const), fun x => ?_⟩
  by_cases hx : x ∈ E
  · have h1 : w x ≤ ((N : ℝ) : EReal) := (hN hx).le
    refine h1.trans ?_
    rw [← h.coe_evalReal, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have := h.const_le_evalReal x
    have := le_max_right (0 : ℝ) ((N : ℝ) - h.const)
    linarith
  · rw [hwE x hx]
    have : (0 : EReal) ≤ ((max 0 ((N : ℝ) - h.const) : ℝ) : EReal) :=
      EReal.coe_nonneg.2 (le_max_left _ _)
    simpa using add_le_add (le_refl (h.eval x)) this

end Auxiliary

/-- **Lemma `lem:wu-pl-special-case`.** The statements of FHX Lemma 5.11(5),(6)
(`WuRegularization k`) imply `ConvexPLApproximation k`. A function `w` standard at infinity with
respect to `h` is real valued, satisfies `w ≤ h + C` (so it has logarithmic growth), and on `Y^an`
it is the limit of the constant sequence `w`; so 5.11(6) makes it regularizable, and 5.11(5) with
`g = h` gives the approximants. -/
theorem ConvexPLApproximation.of_wuRegularization (k : Type u) [Field k] [IsAlgClosed k]
    [WuRegularization.{u, v} k] : ConvexPLApproximation.{u, v} k where
  approx A _ _ _ _ _ w h E hE hw hwE c hc := by
    obtain ⟨C, hC⟩ := exists_le_eval_add_of_isConvexPLOn_univ hE hw hwE
    have hreg : IsRegularizable w := by
      refine WuRegularization.localToGlobal A w ⟨Berk.triv, ?_⟩ ⟨h, C, hC⟩ fun K _ =>
        ⟨Set.univ, isOpen_univ, Set.subset_univ K, fun _ => w, fun _ => hw,
          fun _ _ => antitone_const, fun y _ => (iInf_const).symm⟩
      intro hbot
      obtain ⟨W, -, hW, -, n, f, s, hs, -, hu⟩ := hw Berk.triv (Set.mem_univ _)
      rw [hu _ hW] at hbot
      exact EReal.coe_ne_bot _ hbot
    exact WuRegularization.growthControl A w h C hreg hC c hc

end EnvelopeProperty
