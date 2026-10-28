/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLApproxImport

/-!
# Affine reduction of FHX Lemma 5.11(5),(6) to the approximation of convex PL functions

Let `Y = Spec A` be a normal affine variety over the algebraically closed trivially valued field
`k`. This file derives the two statements of Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.11(5),(6) (`lem:regularizable-closure`), recorded as the hypothesis
class `WuRegularization k`, from the smaller hypothesis `ConvexPLApproximation k`
(`thm:wu-pl-approx`: a convex PL function on `Y^an` equal to `h ∈ FS(Y)` outside a compact set is
a decreasing limit of FS functions `h_j ≤ c h + C_j`, for every rational `c > 1`). Together with
`ConvexPLApproximation.of_wuRegularization` this shows that the two hypotheses are equivalent.
The arguments follow the blueprint section `subsec:wu-affine` and take place on `Y^an` alone: no
compactification, no decreasing-limit theorem (PSH2), no countable regularization and no
countability of `k` are used.

## Main results

* `exists_lt_on_compact_of_antitone_of_continuousOn`: Dini's argument on an open set.
* `exists_antitone_seq_of_directed`: a countable downward directed family contains a decreasing
  sequence with the same infimum.
* `exists_collar` (`lem:wu-collar`): gluing decreasing local convex PL approximants of `v`
  with an FS function `h > v` across a compact collar `{t ≤ g ≤ t + 1}` gives functions standard
  at infinity decreasing to `max h v`.
* `exists_antitone_fs_of_antitone_growth` (`lem:wu-growth-diagonal`): a decreasing limit of
  decreasing limits of FS functions of growth `c' g` is a decreasing limit of FS functions `G_m`
  with `c g - a_m ≤ G_m ≤ c g + b_m`, for `c' < c`. Compactness of a compactification is replaced
  by the gap between the growth rates: the truncations `max (F, c g - m)` equal `c g - m` outside
  compact sets.
* `exists_antitone_fs_growth_of_local` (`prop:wu-main`): regularization with two-sided growth
  control of a function `v ≤ g + C` that is, near every compact set, a decreasing limit of convex PL
  functions.
* `ConvexPLApproximation.growthControl` (`thm:wu-growth-control`, FHX 5.11(5) with the two-sided
  bound of the source) and `ConvexPLApproximation.localToGlobal` (`thm:wu-local-to-global`,
  FHX 5.11(6)).
* The instance `ConvexPLApproximation.toWuRegularization : WuRegularization k`.

## Implementation notes

The diagonal lemma is proved with the countable family
`max (F n j, c g - m) + q` (`n, j, m ∈ ℕ`, `q ∈ ℚ_{>0}`), which is downward directed for the
pointwise order on all of `Y^an` (Dini's argument on a compact sublevel set of `g`, and the growth
gap outside it); `exists_antitone_seq_of_directed` then extracts the decreasing sequence. This
replaces the inductive choice of indices in the blueprint proof.

**Circularity guard.** Nothing in this file assumes `WuRegularization k` or uses a result whose
statement or proof needs it; the file imports only `Local/{Defs, FS}`, `Local/Imports` (the class
declaration) and `Local/PLApproxImport`. The instance is the last declaration.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

/-! ### Order-theoretic and topological auxiliaries -/

section Topological

/-- **Dini's argument on an open set.** Let `K ⊆ U` with `K` compact and `U` open, and let
`f j`, `s` be continuous on `U`, with `f j` decreasing in `j` on `U`. If every point of `K` has
some `f j < s`, then `f j < s` on all of `K` for all large `j`. -/
theorem exists_lt_on_compact_of_antitone_of_continuousOn {X β : Type*} [TopologicalSpace X]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℕ → X → β}
    (hf : ∀ j, ContinuousOn (f j) U) (hmono : ∀ x ∈ U, Antitone fun j => f j x)
    {s : X → β} (hs : ContinuousOn s U) (hlt : ∀ x ∈ K, ∃ j, f j x < s x) :
    ∃ j₀, ∀ j, j₀ ≤ j → ∀ x ∈ K, f j x < s x := by
  set O : ℕ → Set X := fun j => U ∩ (fun x => (f j x, s x)) ⁻¹' {p : β × β | p.1 < p.2}
  have hO : ∀ j, IsOpen (O j) := fun j =>
    ((hf j).prodMk hs).isOpen_inter_preimage hU (isOpen_lt continuous_fst continuous_snd)
  have hcover : K ⊆ ⋃ j, O j := fun x hx => by
    obtain ⟨j, hj⟩ := hlt x hx
    exact Set.mem_iUnion.2 ⟨j, hKU hx, hj⟩
  have hdir : Directed (· ⊆ ·) O := Monotone.directed_le fun i j hij x hx =>
    ⟨hx.1, lt_of_le_of_lt (hmono x hx.1 hij) hx.2⟩
  obtain ⟨j₀, hj₀⟩ := hK.elim_directed_cover O hO hcover hdir
  exact ⟨j₀, fun j hj x hx => lt_of_le_of_lt (hmono x (hKU hx) hj) (hj₀ hx).2⟩

/-- **Decreasing sequences in a countable directed family.** If a countable nonempty family of
functions `φ i` is downward directed for the pointwise order, then some sequence `φ (e m)` is
decreasing and has the same pointwise infimum as the whole family. -/
theorem exists_antitone_seq_of_directed {X ι β : Type*} [Countable ι] [Nonempty ι]
    [CompleteLattice β] (φ : ι → X → β)
    (hdir : ∀ a b, ∃ c, ∀ x, φ c x ≤ φ a x ∧ φ c x ≤ φ b x) :
    ∃ e : ℕ → ι, (∀ x, Antitone fun m => φ (e m) x) ∧ ∀ x, ⨅ m, φ (e m) x = ⨅ i, φ i x := by
  obtain ⟨s, hs⟩ := exists_surjective_nat ι
  choose c hc using hdir
  let H : ℕ → ι := fun m => Nat.rec (s 0) (fun m h => c h (s (m + 1))) m
  have Hsucc : ∀ m x, φ (H (m + 1)) x ≤ φ (H m) x ∧ φ (H (m + 1)) x ≤ φ (s (m + 1)) x :=
    fun m x => hc _ _ x
  have Hle : ∀ m x, φ (H m) x ≤ φ (s m) x := by
    intro m x
    cases m with
    | zero => exact le_rfl
    | succ m => exact (Hsucc m x).2
  refine ⟨H, fun x => antitone_nat_of_succ_le fun m => (Hsucc m x).1, fun x => le_antisymm ?_ ?_⟩
  · refine le_iInf fun i => ?_
    obtain ⟨m, rfl⟩ := hs i
    exact (iInf_le _ m).trans (Hle m x)
  · exact le_iInf fun m => iInf_le _ (H m)

/-- An element of `EReal` that is `≤ a + q` for every rational `q > 0` is `≤ a`. -/
private theorem ereal_le_coe_of_forall_rat_pos {y : EReal} {a : ℝ}
    (h : ∀ q : ℚ, 0 < q → y ≤ ((a + q : ℝ) : EReal)) : y ≤ (a : EReal) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  induction r using EReal.rec with
  | bot => exact absurd hr not_lt_bot
  | coe r =>
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_pos.2 (EReal.coe_lt_coe_iff.1 hr))
    exact (h q (by exact_mod_cast hq1)).trans (EReal.coe_le_coe_iff.2 (by linarith))
  | top => exact le_top

end Topological

/-! ### Real-valued forms of FS operations -/

section FS

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Real value of the maximum of two FS functions. -/
private theorem evalReal_sup_aux (g g' : FSData k A) (x : Berk k A) :
    (g.sup g').evalReal x = max (g.evalReal x) (g'.evalReal x) := by
  apply EReal.coe_injective
  rw [FSData.coe_evalReal, FSData.eval_sup, ← g.coe_evalReal, ← g'.coe_evalReal]
  exact EReal.coe_strictMono.monotone.map_max.symm

/-- Real value of a rational translate of an FS function. -/
private theorem evalReal_addConst_aux (g : FSData k A) (q : ℚ) (x : Berk k A) :
    (g.addConst q).evalReal x = g.evalReal x + q := by
  apply EReal.coe_injective
  rw [FSData.coe_evalReal, FSData.eval_addConst, ← g.coe_evalReal, EReal.coe_add]

/-- Real value of a positive rational multiple of an FS function. -/
private theorem evalReal_smul_aux (g : FSData k A) (c : ℚ) (hc : 0 < c) (x : Berk k A) :
    (g.smul c hc).evalReal x = c * g.evalReal x := by
  apply EReal.coe_injective
  rw [FSData.coe_evalReal, FSData.eval_smul, ← g.coe_evalReal, EReal.coe_mul]

/-- Sublevel sets of the real value of an FS function are compact. -/
private theorem isCompact_setOf_evalReal_le (g : FSData k A) (r : ℝ) :
    IsCompact {x : Berk k A | g.evalReal x ≤ r} := by
  have e : {x : Berk k A | g.evalReal x ≤ r} = {x | g.eval x ≤ (r : EReal)} := by
    ext x
    change g.evalReal x ≤ r ↔ g.eval x ≤ (r : EReal)
    rw [← g.coe_evalReal x, EReal.coe_le_coe_iff]
  rw [e]
  exact g.isCompact_setOf_eval_le r

/-! ### Collar gluing -/

/-- **Collar gluing** (`lem:wu-collar`). Let `g, h ∈ FS(Y)`, `t ∈ ℝ`, and let `v < h` on
`{g ≥ t}`. Let `U` be an open neighbourhood of `{g ≤ t + 1}` on which `v` is the limit of a
decreasing sequence of convex PL functions `v_j`. Then, after discarding finitely many indices, the
functions `W_j` equal to `max (h, v_j)` on `{g < t + 1}` and to `h` elsewhere are convex PL on
`Y^an`, equal to `h` on `{g > t}` (so standard at infinity with respect to `h`, with `E = {g ≤ t}`),
and decrease to `max (h, v)`. -/
theorem exists_collar (g h : FSData k A) (t : ℝ) {v : Berk k A → EReal}
    (hvh : ∀ x, t ≤ g.evalReal x → v x < h.eval x) {U : Set (Berk k A)} (hU : IsOpen U)
    (hKU : {x | g.evalReal x ≤ t + 1} ⊆ U) (hv : IsDecrConvexPLLimitOn U v) :
    ∃ W : ℕ → Berk k A → EReal, (∀ j, IsConvexPLOn Set.univ (W j)) ∧
      (∀ j x, t < g.evalReal x → W j x = h.eval x) ∧ (∀ x, Antitone fun j => W j x) ∧
      ∀ x, ⨅ j, W j x = max (h.eval x) (v x) := by
  classical
  obtain ⟨vs, hconv, hanti, hlim⟩ := hv
  -- the compact collar `Q = {t ≤ g ≤ t + 1}`
  set Q : Set (Berk k A) := {x | t ≤ g.evalReal x} ∩ {x | g.evalReal x ≤ t + 1} with hQdef
  have hQ : IsCompact Q := (isCompact_setOf_evalReal_le g (t + 1)).inter_left
    (isClosed_le continuous_const g.continuous_evalReal)
  have hQU : Q ⊆ U := fun x hx => hKU hx.2
  -- by Dini, `v_j < h` on the collar for large `j`
  obtain ⟨j₀, hj₀⟩ := exists_lt_on_compact_of_antitone_of_continuousOn hQ hU hQU
    (fun j => (hconv j).continuousOn) hanti h.continuous_eval.continuousOn fun x hx => by
      have := hvh x hx.1
      rw [hlim x (hQU hx)] at this
      exact iInf_lt_iff.1 this
  set U' : Set (Berk k A) := {x | g.evalReal x < t + 1} with hU'def
  have hU' : IsOpen U' := isOpen_lt g.continuous_evalReal continuous_const
  have hU'U : U' ⊆ U := fun x (hx : g.evalReal x < t + 1) =>
    hKU (show g.evalReal x ≤ t + 1 from le_of_lt hx)
  have hcol : ∀ j, j₀ ≤ j → ∀ x ∈ U', t ≤ g.evalReal x → vs j x < h.eval x :=
    fun j hj x (hx : g.evalReal x < t + 1) htx =>
      hj₀ j hj x ⟨htx, show g.evalReal x ≤ t + 1 from le_of_lt hx⟩
  refine ⟨fun j => U'.piecewise (fun y => max (h.eval y) (vs (j + j₀) y)) h.eval,
    fun j => ?_, fun j x hx => ?_, fun x i j hij => ?_, fun x => ?_⟩
  · -- convexity, by the gluing lemma
    refine IsConvexPLOn.piecewise_max hU' (Set.subset_univ _) h.isConvexPLOn_univ
      ((hconv (j + j₀)).mono hU' hU'U) ?_
    have hsub : {y | y ∈ U' ∧ h.eval y < vs (j + j₀) y} ⊆ {y | g.evalReal y ≤ t} := by
      rintro y ⟨hyU', hy⟩
      by_contra hty
      exact lt_asymm hy (hcol (j + j₀) (Nat.le_add_left _ _) y hyU' (le_of_lt (not_le.1 hty)))
    intro y hy
    have hy' : g.evalReal y ≤ t :=
      closure_minimal hsub (isClosed_le g.continuous_evalReal continuous_const) hy.1
    show g.evalReal y < t + 1
    linarith
  · -- standard at infinity
    beta_reduce
    by_cases hxU' : x ∈ U'
    · rw [Set.piecewise_eq_of_mem _ _ _ hxU']
      exact max_eq_left (hcol (j + j₀) (Nat.le_add_left _ _) x hxU' hx.le).le
    · rw [Set.piecewise_eq_of_notMem _ _ _ hxU']
  · -- monotonicity
    beta_reduce
    by_cases hxU' : x ∈ U'
    · simp only [Set.piecewise_eq_of_mem _ _ _ hxU']
      exact max_le_max le_rfl (hanti x (hU'U hxU') (Nat.add_le_add_right hij j₀))
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hxU', le_refl]
  · -- the limit
    beta_reduce
    by_cases hxU' : x ∈ U'
    · simp only [Set.piecewise_eq_of_mem _ _ _ hxU']
      rw [← sup_iInf_eq, hlim x (hU'U hxU')]
      congr 1
      exact le_antisymm
        (le_iInf fun j => (iInf_le _ j).trans (hanti x (hU'U hxU') (Nat.le_add_right j j₀)))
        (le_iInf fun j => iInf_le _ (j + j₀))
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hxU', iInf_const]
      have : t ≤ g.evalReal x := by
        have := not_lt.1 (show ¬ g.evalReal x < t + 1 from hxU')
        linarith
      exact (max_eq_left (hvh x this).le).symm

/-! ### Growth-controlled diagonal sequences -/

/-- **Growth-controlled diagonal sequences** (`lem:wu-growth-diagonal`). Let `g ∈ FS(Y)` and
`c' < c` with `c ∈ ℚ_{>0}`. Let `w_n` decrease in `n`, and let each `w_n` be the limit of a
decreasing sequence `F_{n,j}` in `FS(Y)` with `F_{n,0} ≤ c' g + D_n`. Then `inf_n w_n` is the limit
of a decreasing sequence `G_m` in `FS(Y)` with `c g - a_m ≤ G_m ≤ c g + b_m`. -/
theorem exists_antitone_fs_of_antitone_growth (g : FSData k A) {c : ℚ} (hc : 0 < c) {c' : ℝ}
    (hc' : c' < c) {w : ℕ → Berk k A → EReal} (hw : ∀ x, Antitone fun n => w n x)
    {F : ℕ → ℕ → FSData k A} (hF : ∀ n x, Antitone fun j => (F n j).eval x)
    (hFw : ∀ n x, w n x = ⨅ j, (F n j).eval x)
    (hgrowth : ∀ n, ∃ D : ℝ, ∀ x, (F n 0).evalReal x ≤ c' * g.evalReal x + D) :
    ∃ G : ℕ → FSData k A, (∀ x, Antitone fun m => (G m).eval x) ∧
      (∀ x, ⨅ n, w n x = ⨅ m, (G m).eval x) ∧
      ∀ m, ∃ a b : ℝ, ∀ x, (c : ℝ) * g.evalReal x - a ≤ (G m).evalReal x ∧
        (G m).evalReal x ≤ (c : ℝ) * g.evalReal x + b := by
  classical
  choose D hD using hgrowth
  have hcc' : (0 : ℝ) < c - c' := sub_pos.2 hc'
  -- real-valued forms of the hypotheses
  have hFr : ∀ n x i j, i ≤ j → (F n j).evalReal x ≤ (F n i).evalReal x := fun n x i j hij => by
    have : (F n j).eval x ≤ (F n i).eval x := hF n x hij
    rwa [← (F n j).coe_evalReal x, ← (F n i).coe_evalReal x, EReal.coe_le_coe_iff] at this
  have hwF : ∀ n j x, w n x ≤ ((F n j).evalReal x : EReal) := fun n j x => by
    rw [hFw n x, (F n j).coe_evalReal x]
    exact iInf_le _ j
  -- the countable family `max (F n j, c g - m) + q`
  let φ : ℕ × ℕ × ℕ × {q : ℚ // 0 < q} → FSData k A := fun i =>
    ((F i.1 i.2.1).sup ((g.smul c hc).addConst (-(i.2.2.1 : ℚ)))).addConst (i.2.2.2 : ℚ)
  have hφ : ∀ i x, (φ i).evalReal x =
      max ((F i.1 i.2.1).evalReal x) ((c : ℝ) * g.evalReal x - i.2.2.1) + ((i.2.2.2 : ℚ) : ℝ) := by
    intro i x
    simp only [φ, evalReal_addConst_aux, evalReal_sup_aux, evalReal_smul_aux, Rat.cast_neg,
      Rat.cast_natCast, sub_eq_add_neg]
  have hφe : ∀ i x, (φ i).eval x = (((φ i).evalReal x : ℝ) : EReal) := fun i x =>
    ((φ i).coe_evalReal x).symm
  -- directedness
  have hdir : ∀ a b, ∃ d, ∀ x, (φ d).eval x ≤ (φ a).eval x ∧ (φ d).eval x ≤ (φ b).eval x := by
    rintro ⟨n₁, j₁, m₁, q₁⟩ ⟨n₂, j₂, m₂, q₂⟩
    set n := max n₁ n₂ with hn
    set m := max m₁ m₂ with hm
    set q : ℚ := min (q₁ : ℚ) q₂ / 2 with hq
    have hmin : 0 < min (q₁ : ℚ) q₂ := lt_min q₁.2 q₂.2
    have hq0 : 0 < q := by positivity
    have hq1 : (q : ℝ) < (q₁ : ℚ) := by
      have : q < q₁ := by have := min_le_left (q₁ : ℚ) q₂; linarith
      exact_mod_cast this
    have hq2 : (q : ℝ) < (q₂ : ℚ) := by
      have : q < q₂ := by have := min_le_right (q₁ : ℚ) q₂; linarith
      exact_mod_cast this
    have hm1 : (m₁ : ℝ) ≤ m := by exact_mod_cast le_max_left m₁ m₂
    have hm2 : (m₂ : ℝ) ≤ m := by exact_mod_cast le_max_right m₁ m₂
    set R : ℝ := (m + D n) / (c - c') with hR
    -- Dini on the compact set `{g ≤ R}`
    obtain ⟨j₀, hj₀⟩ := exists_lt_on_compact_of_antitone_of_continuousOn
      (isCompact_setOf_evalReal_le g R) isOpen_univ (Set.subset_univ _)
      (f := fun j x => (φ (n, j, m, ⟨q, hq0⟩)).evalReal x)
      (s := fun x => min ((φ (n₁, j₁, m₁, q₁)).evalReal x) ((φ (n₂, j₂, m₂, q₂)).evalReal x))
      (fun j => (φ _).continuous_evalReal.continuousOn)
      (fun x _ i j hij => by
        simp only [hφ]
        exact add_le_add (max_le_max (hFr n x i j hij) le_rfl) le_rfl)
      ((φ _).continuous_evalReal.min (φ _).continuous_evalReal).continuousOn
      (fun x _ => by
        have h1 : w n x ≤ ((min ((F n₁ j₁).evalReal x) ((F n₂ j₂).evalReal x) : ℝ) : EReal) := by
          rw [EReal.coe_strictMono.monotone.map_min]
          exact le_min ((hw x (le_max_left n₁ n₂)).trans (hwF _ _ x))
            ((hw x (le_max_right n₁ n₂)).trans (hwF _ _ x))
        have h2 : w n x < ((min ((F n₁ j₁).evalReal x) ((F n₂ j₂).evalReal x) +
            (min ((q₁ : ℚ) : ℝ) ((q₂ : ℚ) : ℝ) - q) : ℝ) : EReal) := by
          refine lt_of_le_of_lt h1 (EReal.coe_lt_coe_iff.2 ?_)
          have := lt_min hq1 hq2
          linarith
        rw [hFw n x] at h2
        obtain ⟨j, hj⟩ := iInf_lt_iff.1 h2
        rw [← (F n j).coe_evalReal x, EReal.coe_lt_coe_iff] at hj
        refine ⟨j, ?_⟩
        simp only [hφ]
        have := min_le_left ((F n₁ j₁).evalReal x) ((F n₂ j₂).evalReal x)
        have := min_le_right ((F n₁ j₁).evalReal x) ((F n₂ j₂).evalReal x)
        have := min_le_left ((q₁ : ℚ) : ℝ) ((q₂ : ℚ) : ℝ)
        have := min_le_right ((q₁ : ℚ) : ℝ) ((q₂ : ℚ) : ℝ)
        have := le_max_left ((F n₁ j₁).evalReal x) ((c : ℝ) * g.evalReal x - m₁)
        have := le_max_right ((F n₁ j₁).evalReal x) ((c : ℝ) * g.evalReal x - m₁)
        have := le_max_left ((F n₂ j₂).evalReal x) ((c : ℝ) * g.evalReal x - m₂)
        have := le_max_right ((F n₂ j₂).evalReal x) ((c : ℝ) * g.evalReal x - m₂)
        refine lt_min ?_ ?_ <;> rw [← lt_sub_iff_add_lt] <;> refine max_lt ?_ ?_ <;> linarith)
    refine ⟨(n, j₀, m, ⟨q, hq0⟩), fun x => ?_⟩
    rw [hφe, hφe, hφe, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    by_cases hx : g.evalReal x ≤ R
    · have := hj₀ j₀ le_rfl x hx
      exact ⟨(this.trans_le (min_le_left _ _)).le, (this.trans_le (min_le_right _ _)).le⟩
    · replace hx := not_le.1 hx
      have hRx : (m : ℝ) + D n < (c - c') * g.evalReal x := by
        rw [hR, div_lt_iff₀ hcc'] at hx
        linarith
      have hF0 := hFr n x 0 j₀ (Nat.zero_le _)
      have hDn := hD n x
      have hsub : ((c : ℝ) - c') * g.evalReal x = c * g.evalReal x - c' * g.evalReal x := by ring
      have heq : (φ (n, j₀, m, ⟨q, hq0⟩)).evalReal x = c * g.evalReal x - m + q := by
        rw [hφ]
        simp only
        rw [max_eq_right (by linarith)]
      rw [heq, hφ, hφ]
      have := le_max_right ((F n₁ j₁).evalReal x) ((c : ℝ) * g.evalReal x - m₁)
      have := le_max_right ((F n₂ j₂).evalReal x) ((c : ℝ) * g.evalReal x - m₂)
      constructor <;> simp only <;> linarith
  -- the infimum of the family is `inf_n w_n`
  have hinf : ∀ x, ⨅ i, (φ i).eval x = ⨅ n, w n x := by
    intro x
    apply le_antisymm
    · refine le_iInf fun n => ?_
      rw [hFw n x]
      refine le_iInf fun j => ?_
      rw [← (F n j).coe_evalReal x]
      refine ereal_le_coe_of_forall_rat_pos fun q hq => ?_
      obtain ⟨m, hm⟩ := exists_nat_ge ((c : ℝ) * g.evalReal x - (F n j).evalReal x)
      refine (iInf_le _ (n, j, m, ⟨q, hq⟩)).trans (le_of_eq ?_)
      rw [hφe, hφ]
      simp only
      rw [max_eq_left (by linarith)]
    · refine le_iInf fun i => (iInf_le _ i.1).trans ?_
      rw [hφe]
      refine (hwF i.1 i.2.1 x).trans (EReal.coe_le_coe_iff.2 ?_)
      rw [hφ]
      have := le_max_left ((F i.1 i.2.1).evalReal x) ((c : ℝ) * g.evalReal x - i.2.2.1)
      have : (0 : ℝ) < ((i.2.2.2 : ℚ) : ℝ) := by exact_mod_cast i.2.2.2.2
      linarith
  -- growth bounds for every member of the family
  have hbd : ∀ i, ∃ a b : ℝ, ∀ x, (c : ℝ) * g.evalReal x - a ≤ (φ i).evalReal x ∧
      (φ i).evalReal x ≤ (c : ℝ) * g.evalReal x + b := by
    rintro ⟨n, j, m, q⟩
    refine ⟨m, max (D n - (c - c') * g.const) 0 + (q : ℚ), fun x => ?_⟩
    rw [hφ]
    simp only
    have hq : (0 : ℝ) < ((q : ℚ) : ℝ) := by exact_mod_cast q.2
    have hb0 : (g.const : ℝ) ≤ g.evalReal x := g.const_le_evalReal x
    have hF0 := hFr n x 0 j (Nat.zero_le _)
    have hDn := hD n x
    have hprod : 0 ≤ ((c : ℝ) - c') * (g.evalReal x - g.const) :=
      mul_nonneg hcc'.le (sub_nonneg.2 hb0)
    have hexp : ((c : ℝ) - c') * (g.evalReal x - g.const) =
        c * g.evalReal x - c' * g.evalReal x - (c - c') * g.const := by ring
    have := le_max_left (D n - (c - c') * g.const) 0
    have := le_max_right (D n - (c - c') * g.const) 0
    have := le_max_right ((F n j).evalReal x) ((c : ℝ) * g.evalReal x - m)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    constructor
    · linarith
    · have : max ((F n j).evalReal x) ((c : ℝ) * g.evalReal x - m) ≤
          c * g.evalReal x + max (D n - (c - c') * g.const) 0 :=
        max_le (by linarith) (by linarith)
      linarith
  -- extract a decreasing sequence
  have : Nonempty (ℕ × ℕ × ℕ × {q : ℚ // 0 < q}) := ⟨(0, 0, 0, ⟨1, one_pos⟩)⟩
  obtain ⟨e, he_anti, he_inf⟩ := exists_antitone_seq_of_directed (fun i x => (φ i).eval x) hdir
  exact ⟨fun m => φ (e m), he_anti, fun x => by rw [he_inf x, hinf x], fun m => hbd (e m)⟩

end FS

/-! ### Regularization with growth control -/

section Main

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]

/-- **Regularization with growth control** (`prop:wu-main`). Assume `ConvexPLApproximation k`.
Let `v ≤ g + C` with `g ∈ FS(Y)`, and assume that every compact subset of `Y^an` has an open
neighbourhood on which `v` is the limit of a decreasing sequence of convex PL functions. Then for
every rational `c > 1` there are `G_m ∈ FS(Y)` decreasing to `v` with
`c g - a_m ≤ G_m ≤ c g + b_m`. -/
theorem exists_antitone_fs_growth_of_local [ConvexPLApproximation.{u, v} k]
    {v : Berk k A → EReal} {g : FSData k A} {C : ℝ} (hv : ∀ x, v x ≤ g.eval x + (C : EReal))
    (hloc : ∀ K : Set (Berk k A), IsCompact K →
      ∃ U : Set (Berk k A), IsOpen U ∧ K ⊆ U ∧ IsDecrConvexPLLimitOn U v)
    {c : ℚ} (hc : 1 < c) :
    ∃ G : ℕ → FSData k A, (∀ x, Antitone fun m => (G m).eval x) ∧
      (∀ x, v x = ⨅ m, (G m).eval x) ∧
      ∀ m, ∃ a b : ℝ, ∀ x, (c : ℝ) * g.evalReal x - a ≤ (G m).evalReal x ∧
        (G m).evalReal x ≤ (c : ℝ) * g.evalReal x + b := by
  -- rational growth rates `1 < c₁ < c₂ < c₃ < c`
  obtain ⟨c₁, c₂, c₃, h1, h12, h23, h3⟩ : ∃ c₁ c₂ c₃ : ℚ, 1 < c₁ ∧ c₁ < c₂ ∧ c₂ < c₃ ∧ c₃ < c :=
    ⟨1 + (c - 1) / 4, 1 + (c - 1) / 2, 1 + 3 * (c - 1) / 4, by linarith, by linarith,
      by linarith, by linarith⟩
  have hc₁ : (0 : ℚ) < c₁ := by linarith
  have h1' : (1 : ℝ) < c₁ := by exact_mod_cast h1
  -- the FS functions `h_n = c₁ g - n`
  set hn : ℕ → FSData k A := fun n => (g.smul c₁ hc₁).addConst (-(n : ℚ)) with hn_def
  have hn_eval : ∀ n x, (hn n).evalReal x = (c₁ : ℝ) * g.evalReal x - n := by
    intro n x
    simp only [hn, evalReal_addConst_aux, evalReal_smul_aux, Rat.cast_neg, Rat.cast_natCast,
      sub_eq_add_neg]
  -- collar radii `t_n`, with `(c₁ - 1) t_n = C + n + 2`
  set t : ℕ → ℝ := fun n => (C + n + 2) / ((c₁ : ℝ) - 1) with ht_def
  have ht : ∀ n, ((c₁ : ℝ) - 1) * t n = C + n + 2 := fun n =>
    mul_div_cancel₀ _ (by linarith)
  have hvh : ∀ n x, t n ≤ g.evalReal x → v x < (hn n).eval x := by
    intro n x hx
    have hv' : v x ≤ ((g.evalReal x + C : ℝ) : EReal) := by
      rw [EReal.coe_add, g.coe_evalReal]
      exact hv x
    refine lt_of_le_of_lt hv' ?_
    rw [← (hn n).coe_evalReal, hn_eval, EReal.coe_lt_coe_iff]
    have hmul := mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ (c₁ : ℝ) - 1)
    rw [ht n] at hmul
    have hexp : ((c₁ : ℝ) - 1) * g.evalReal x = c₁ * g.evalReal x - g.evalReal x := by ring
    linarith
  -- local approximants near `{g ≤ t_n + 1}`, and the collar functions `W n j`
  choose U hUo hKU hUv using fun n => hloc _ (isCompact_setOf_evalReal_le g (t n + 1))
  choose W hWconv hWstd hWanti hWlim using fun n =>
    exists_collar g (hn n) (t n) (hvh n) (hUo n) (hKU n) (hUv n)
  -- FS approximants of the `W n j`, of growth `c₂ g`
  have hc21 : 1 < c₂ / c₁ := (one_lt_div hc₁).2 h12
  choose F hFanti hFlim hFgr using fun n j =>
    ConvexPLApproximation.approx A (W n j) (hn n) {x | g.evalReal x ≤ t n}
      (isCompact_setOf_evalReal_le g (t n)) (hWconv n j)
      (fun x hx => hWstd n j x (lt_of_not_ge hx)) (c₂ / c₁) hc21
  have hFg : ∀ n j, ∃ D : ℝ, ∀ x, (F n j 0).evalReal x ≤ (c₂ : ℝ) * g.evalReal x + D := by
    intro n j
    obtain ⟨D, hD⟩ := hFgr n j 0
    refine ⟨D, fun x => ?_⟩
    have hDx := hD x
    rw [← (F n j 0).coe_evalReal, ← (hn n).coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff, hn_eval] at hDx
    have hc₁' : (c₁ : ℝ) ≠ 0 := by positivity
    have e : ((c₂ / c₁ : ℚ) : ℝ) * ((c₁ : ℝ) * g.evalReal x - n) =
        (c₂ : ℝ) * g.evalReal x - ((c₂ / c₁ : ℚ) : ℝ) * n := by
      push_cast
      field_simp
    have : (0 : ℝ) ≤ ((c₂ / c₁ : ℚ) : ℝ) * n := by
      have : (0 : ℚ) ≤ c₂ / c₁ := by positivity
      positivity
    linarith
  -- first diagonal argument: `max (h_n, v)` is a decreasing limit of growth `c₃ g`
  choose G hGanti hGlim hGbd using fun n =>
    exists_antitone_fs_of_antitone_growth g (c := c₃) (by linarith) (c' := c₂)
      (by exact_mod_cast h23) (hWanti n) (fun j x => hFanti n j x) (fun j x => hFlim n j x)
      (hFg n)
  -- second diagonal argument
  have hmono : ∀ x, Antitone fun n => max ((hn n).eval x) (v x) := by
    intro x n n' hnn'
    refine max_le_max ?_ le_rfl
    rw [← (hn n).coe_evalReal, ← (hn n').coe_evalReal, hn_eval, hn_eval, EReal.coe_le_coe_iff]
    have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    linarith
  obtain ⟨G', hG'anti, hG'lim, hG'bd⟩ := exists_antitone_fs_of_antitone_growth g (c := c)
    (by linarith) (c' := c₃) (by exact_mod_cast h3) hmono hGanti
    (fun n x => by rw [← hWlim n x]; exact hGlim n x)
    (fun n => by
      obtain ⟨a, b, hab⟩ := hGbd n 0
      exact ⟨b, fun x => (hab x).2⟩)
  refine ⟨G', hG'anti, fun x => ?_, hG'bd⟩
  rw [← hG'lim x]
  -- `inf_n max (c₁ g - n, v) = v`
  have hbot : ⨅ n, (hn n).eval x = ⊥ := by
    rw [iInf_eq_bot]
    intro b hb
    induction b using EReal.rec with
    | bot => exact absurd hb (lt_irrefl _)
    | coe r =>
      obtain ⟨n, hn'⟩ := exists_nat_gt ((c₁ : ℝ) * g.evalReal x - r)
      refine ⟨n, ?_⟩
      rw [← (hn n).coe_evalReal, hn_eval, EReal.coe_lt_coe_iff]
      linarith
    | top => exact ⟨0, (hn 0).eval_lt_top x⟩
  rw [← iInf_sup_eq, hbot, bot_sup_eq]

/-- **Growth-controlled approximation** (`thm:wu-growth-control`; FHX Lemma 5.11(5) with the
two-sided bound of the source). Assume `ConvexPLApproximation k`. If `u ∈ ℛ(Y)` and
`u ≤ g + C` with `g ∈ FS(Y)`, then for every rational `c > 1` there are `u_j ∈ FS(Y)` decreasing
to `u` with `u_j - c g` bounded. -/
theorem ConvexPLApproximation.growthControl [ConvexPLApproximation.{u, v} k]
    {u : Berk k A → EReal} {g : FSData k A} {C : ℝ} (hu : IsRegularizable u)
    (hug : ∀ x, u x ≤ g.eval x + (C : EReal)) {c : ℚ} (hc : 1 < c) :
    ∃ h : ℕ → FSData k A, (∀ x, Antitone fun j => (h j).eval x) ∧
      (∀ x, u x = ⨅ j, (h j).eval x) ∧
      ∀ j, ∃ a b : ℝ, ∀ x, ((c : ℝ) : EReal) * g.eval x ≤ (h j).eval x + (a : EReal) ∧
        (h j).eval x ≤ ((c : ℝ) : EReal) * g.eval x + (b : EReal) := by
  obtain ⟨-, φ, hφanti, hφlim⟩ := hu
  obtain ⟨G, hGanti, hGlim, hGbd⟩ := exists_antitone_fs_growth_of_local hug
    (fun K _ => ⟨Set.univ, isOpen_univ, Set.subset_univ K, fun j => (φ j).eval,
      fun j => (φ j).isConvexPLOn_univ, fun y _ => hφanti y, fun y _ => hφlim y⟩) hc
  refine ⟨G, hGanti, hGlim, fun j => ?_⟩
  obtain ⟨a, b, hab⟩ := hGbd j
  refine ⟨a, b, fun x => ?_⟩
  rw [← (G j).coe_evalReal, ← g.coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  exact ⟨by linarith [(hab x).1], (hab x).2⟩

/-- **Local-to-global regularization** (`thm:wu-local-to-global`; FHX Lemma 5.11(6)). Assume
`ConvexPLApproximation k`. A function of logarithmic growth, not identically `-∞`, which on a
neighbourhood of every compact subset of `Y^an` is the limit of a decreasing sequence of convex PL
functions, is regularizable. -/
theorem ConvexPLApproximation.localToGlobal [ConvexPLApproximation.{u, v} k]
    {u : Berk k A → EReal} (hne : ∃ x, u x ≠ ⊥) (hgr : HasLogGrowth u)
    (hloc : ∀ K : Set (Berk k A), IsCompact K →
      ∃ U : Set (Berk k A), IsOpen U ∧ K ⊆ U ∧ IsDecrConvexPLLimitOn U u) :
    IsRegularizable u := by
  obtain ⟨g, C, hC⟩ := hgr
  obtain ⟨G, hGanti, hGlim, -⟩ :=
    exists_antitone_fs_growth_of_local hC hloc (c := 2) one_lt_two
  exact ⟨hne, G, hGanti, hGlim⟩

end Main

universe u v

/-- **FHX Lemma 5.11(5),(6) from `ConvexPLApproximation`** (`rmk:wu-affine`): the imported
hypothesis `WuRegularization k` is a consequence of `ConvexPLApproximation k`. With
`ConvexPLApproximation.of_wuRegularization`, the two hypotheses are equivalent. -/
instance ConvexPLApproximation.toWuRegularization {k : Type u} [Field k] [IsAlgClosed k]
    [ConvexPLApproximation.{u, v} k] : WuRegularization.{u, v} k where
  growthControl A _ _ _ _ _ u g C hu hug c hc := by
    obtain ⟨h, h₁, h₂, h₃⟩ := ConvexPLApproximation.growthControl hu hug hc
    refine ⟨h, h₁, h₂, fun j => ?_⟩
    obtain ⟨_, b, hb⟩ := h₃ j
    exact ⟨b, fun x => (hb x).2⟩
  localToGlobal A _ _ _ _ _ u hne hgr hloc := ConvexPLApproximation.localToGlobal hne hgr hloc

end EnvelopeProperty
