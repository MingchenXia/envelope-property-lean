/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ERealAntitoneLimits
import EnvelopeProperty.Local.FS
import EnvelopeProperty.Local.Diagonal
import EnvelopeProperty.Local.TrivFinite
import EnvelopeProperty.Local.Imports
import EnvelopeProperty.Berkovich.Localization

/-!
# Closure properties of regularizable functions

Let `Y = Spec A` be an affine variety over the trivially valued field `k`. This file proves the
closure properties of the class `ℛ(Y)` of regularizable functions (`IsRegularizable`: limits of
decreasing sequences of affine Fubini–Study functions, not identically `-∞`) stated in
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.11(2),(3),(4)
(`lem:regularizable-closure`; blueprint `lem:reg-closure-elementary`, `lem:diagonal-compact`,
`lem:reg-decreasing`).

* (3) If `q = max_i (a_i log|f_i| + b_i) ≢ -∞` with `a_i ∈ ℚ_{>0}`, `b_i ∈ ℚ`, then `q ∈ ℛ(Y)`
  (`isRegularizable_finsetSup_fsTerm`): with `b = max{0, log|z_1|, …, log|z_n|}` for generators
  `z_l` (`FSData.std`), the FS functions `max{q, b/(j+1) - (j+1)}` (`FSData.truncStd`) decrease to
  `q` since `b ≥ 0` is finite. `ℛ(Y)` is stable under finite maxima (`IsRegularizable.sup`), sums
  (`IsRegularizable.add`; the sum is not `≡ -∞` since both summands are finite at the trivial
  valuation, `IsRegularizable.triv_ne_bot`), positive rational multiples
  (`IsRegularizable.smul`) and real translates (`IsRegularizable.add_const`, using approximants
  `u_j + c_j` with rational `c_j ↓ c`).
* (4) For a morphism `π : Spec B → Spec A` of affine schemes of finite type and `u ∈ ℛ(Y)`,
  `u ∘ π^an` is `≡ -∞` or regularizable (`IsRegularizable.comp_comap`): if `u_j ↓ u` then
  `max{u_j ∘ π^an, b'/(j+1) - (j+1)} ∈ FS(Spec B)` decrease to `u ∘ π^an`. In particular
  restriction to a principal open `Y_f`, `f ≠ 0`, preserves regularizability
  (`IsRegularizable.comp_awayComap`).
* (2) On a normal affine variety, a decreasing limit of regularizable functions which is not
  `≡ -∞` is regularizable (`IsRegularizable.of_antitone`). Every compact `K` lies in the interior
  of a compact `K'`; the diagonal argument (`exists_antitone_diagonal`, packaged as
  `exists_antitone_fs_of_antitone_regularizable`) exhibits the limit on `interior K'` as the
  limit of a decreasing sequence of FS functions, which are convex PL, and the imported
  local-to-global statement (FHX Lemma 5.11(6), `WuRegularization.localToGlobal`) applies.

We also record some facts on infima of decreasing sequences in `EReal`.
-/

open scoped NNReal ENNReal Topology

open Filter Topology

noncomputable section

namespace EnvelopeProperty

open Berk



variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### The truncated standard FS functions -/

namespace FSData

section truncStd

variable (k A) [Algebra.FiniteType k A]

/-- The FS function `b / (j + 1) - (j + 1)`, where `b = max{0, log|z_1|, …, log|z_n|}` is the
standard FS function (`FSData.std`). These decrease to `-∞` as `j → ∞`, since `b ≥ 0` is
finite. -/
def truncStd (j : ℕ) : FSData k A :=
  ((std k A).smul (1 / ((j : ℚ) + 1)) (by positivity)).addConst (-((j : ℚ) + 1))

theorem eval_truncStd (j : ℕ) (x : Berk k A) :
    (truncStd k A j).eval x =
      (((std k A).evalReal x / ((j : ℝ) + 1) - ((j : ℝ) + 1) : ℝ) : EReal) := by
  rw [truncStd, eval_addConst, eval_smul, ← (std k A).coe_evalReal, ← EReal.coe_mul,
    ← EReal.coe_add]
  congr 1
  push_cast
  ring

theorem evalReal_std_nonneg (x : Berk k A) : 0 ≤ (std k A).evalReal x := by
  have := eval_std_nonneg k A x
  rw [← coe_evalReal] at this
  exact_mod_cast this

theorem antitone_truncStd (x : Berk k A) : Antitone fun j => (truncStd k A j).eval x := by
  intro i j hij
  simp only [eval_truncStd, EReal.coe_le_coe_iff]
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h0 := evalReal_std_nonneg k A x
  have : (std k A).evalReal x / ((j : ℝ) + 1) ≤ (std k A).evalReal x / ((i : ℝ) + 1) :=
    div_le_div_of_nonneg_left h0 (by positivity) (by linarith)
  linarith

theorem iInf_truncStd (x : Berk k A) : ⨅ j, (truncStd k A j).eval x = ⊥ := by
  refine eq_bot_iff.2 ((iInf_mono fun j => ?_).trans (iInf_coe_sub_natCast
    ((std k A).evalReal x)).le)
  rw [eval_truncStd, EReal.coe_le_coe_iff]
  have h0 := evalReal_std_nonneg k A x
  have : (std k A).evalReal x / ((j : ℝ) + 1) ≤ (std k A).evalReal x :=
    div_le_self h0 (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  linarith

/-- Taking the maximum with `truncStd` does not change the limit of a decreasing sequence. -/
theorem iInf_max_truncStd {a : ℕ → EReal} (ha : Antitone a) (x : Berk k A) :
    ⨅ j, max (a j) ((truncStd k A j).eval x) = ⨅ j, a j := by
  rw [iInf_max_of_antitone ha (antitone_truncStd k A x), iInf_truncStd, max_bot_right]

end truncStd

end FSData

/-! ### FS functions and basic closure properties -/

section basic

variable {u v : Berk k A → EReal}

theorem IsRegularizable.congr (hu : IsRegularizable u) (h : ∀ x, u x = v x) :
    IsRegularizable v := by
  obtain ⟨⟨x, hx⟩, g, hg, hgu⟩ := hu
  exact ⟨⟨x, h x ▸ hx⟩, g, hg, fun y => (h y).symm.trans (hgu y)⟩

theorem isRegularizable_congr (h : ∀ x, u x = v x) : IsRegularizable u ↔ IsRegularizable v :=
  ⟨fun hu => hu.congr h, fun hv => hv.congr fun x => (h x).symm⟩

/-- An FS function is regularizable (constant approximating sequence), provided the
analytification is nonempty (e.g. `A` a domain: it contains the trivial valuation). -/
theorem FSData.isRegularizable [Nonempty (Berk k A)] (g : FSData k A) :
    IsRegularizable g.eval :=
  ⟨⟨Classical.arbitrary _, g.eval_ne_bot _⟩, fun _ => g, fun _ _ _ _ => le_rfl,
    fun _ => by rw [iInf_const]⟩

theorem IsFS.isRegularizable [Nonempty (Berk k A)] (hu : IsFS u) : IsRegularizable u := by
  obtain ⟨g, hg⟩ := hu
  exact g.isRegularizable.congr fun x => (hg x).symm

/-- A regularizable function is bounded above by each of its approximants. -/
theorem IsRegularizable.exists_approx (hu : IsRegularizable u) :
    ∃ g : ℕ → FSData k A, (∀ x, Antitone fun j => (g j).eval x) ∧
      (∀ x, u x = ⨅ j, (g j).eval x) ∧ ∀ j x, u x ≤ (g j).eval x := by
  obtain ⟨-, g, hg, hgu⟩ := hu
  exact ⟨g, hg, hgu, fun j x => (hgu x).trans_le (iInf_le _ j)⟩

/-- Regularizable functions never take the value `+∞`. -/
theorem IsRegularizable.ne_top (hu : IsRegularizable u) (x : Berk k A) : u x ≠ ⊤ := by
  obtain ⟨-, g, -, hgu⟩ := hu
  rw [hgu]
  exact ne_top_of_le_ne_top ((g 0).eval_ne_top x) (iInf_le _ 0)

/-- **FHX Lemma 5.11(3)**, first part (`lem:reg-closure-elementary`): a finite maximum
`q = max_i (a_i log|f_i| + b_i)` with `a_i ∈ ℚ_{>0}`, `b_i ∈ ℚ`, not identically `-∞`, is
regularizable: the FS functions `max{q, b/(j+1) - (j+1)}` decrease to `q`. -/
theorem isRegularizable_finsetSup_fsTerm [Algebra.FiniteType k A] {s : Finset (A × ℚ × ℚ)}
    (hs : ∀ t ∈ s, 0 < t.2.1) (hne : ∃ x : Berk k A, (s.sup fun t => fsTerm t x) ≠ ⊥) :
    IsRegularizable fun x : Berk k A => s.sup fun t => fsTerm t x := by
  refine ⟨hne, fun j => (FSData.truncStd k A j).addTerms s hs, fun x i j hij => ?_,
    fun x => ?_⟩
  · simp only [FSData.eval_addTerms]
    exact max_le_max (FSData.antitone_truncStd k A x hij) le_rfl
  · simp only [FSData.eval_addTerms]
    rw [iInf_max_of_antitone (FSData.antitone_truncStd k A x) antitone_const,
      FSData.iInf_truncStd, iInf_const, max_bot_left]

/-- `a log|1| + b = b`. -/
theorem fsTerm_one (a b : ℚ) (x : Berk k A) :
    fsTerm (k := k) ((1 : A), a, b) x = ((b : ℝ) : EReal) := by
  simp [fsTerm_def]

/-- **FHX Lemma 5.11(3)** with a constant term: `max{b_0, a_i log|f_i| + b_i}` is
regularizable (`a_i ∈ ℚ_{>0}`), if the analytification is nonempty. -/
theorem isRegularizable_max_const_finsetSup_fsTerm [Algebra.FiniteType k A]
    [Nonempty (Berk k A)] (b : ℚ) {s : Finset (A × ℚ × ℚ)} (hs : ∀ t ∈ s, 0 < t.2.1) :
    IsRegularizable fun x : Berk k A => max ((b : ℝ) : EReal) (s.sup fun t => fsTerm t x) := by
  classical
  have hs' : ∀ t ∈ insert ((1 : A), (1 : ℚ), b) s, 0 < t.2.1 := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact one_pos
    · exact hs t ht
  refine (isRegularizable_finsetSup_fsTerm hs' ⟨Classical.arbitrary _, ?_⟩).congr fun x => ?_
  · rw [Finset.sup_insert, fsTerm_one]
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_left _ _)
  · rw [Finset.sup_insert, fsTerm_one]

/-- `ℛ(Y)` is stable under maxima (FHX Lemma 5.11(3)). -/
theorem IsRegularizable.sup (hu : IsRegularizable u) (hv : IsRegularizable v) :
    IsRegularizable fun x => max (u x) (v x) := by
  obtain ⟨⟨x, hx⟩, g, hg, hgu⟩ := hu
  obtain ⟨-, h, hh, hhv⟩ := hv
  refine ⟨⟨x, ne_bot_of_le_ne_bot hx (le_max_left _ _)⟩, fun j => (g j).sup (h j),
    fun y i j hij => ?_, fun y => ?_⟩
  · simp only [FSData.eval_sup]
    exact max_le_max (hg y hij) (hh y hij)
  · simp only [FSData.eval_sup]
    rw [iInf_max_of_antitone (hg y) (hh y), ← hgu, ← hhv]

/-- `ℛ(Y)` is stable under sums (FHX Lemma 5.11(3)); the sum is not `≡ -∞` since both summands
are finite at the trivial valuation (`IsRegularizable.triv_ne_bot`). -/
theorem IsRegularizable.add [IsDomain A] (hu : IsRegularizable u) (hv : IsRegularizable v) :
    IsRegularizable fun x => u x + v x := by
  have hne : u triv + v triv ≠ ⊥ := by
    rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨hu.triv_ne_bot, hv.triv_ne_bot⟩
  obtain ⟨-, g, hg, hgu⟩ := hu
  obtain ⟨-, h, hh, hhv⟩ := hv
  refine ⟨⟨triv, hne⟩, fun j => (g j).add (h j), fun y i j hij => ?_, fun y => ?_⟩
  · simp only [FSData.eval_add]
    exact add_le_add (hg y hij) (hh y hij)
  · simp only [FSData.eval_add]
    rw [iInf_add_of_antitone (hg y) (hh y) ((g 0).eval_ne_top y) ((h 0).eval_ne_top y), ← hgu,
      ← hhv]

/-- `ℛ(Y)` is stable under multiplication by positive rationals (FHX Lemma 5.11(3)). -/
theorem IsRegularizable.smul (hu : IsRegularizable u) {c : ℚ} (hc : 0 < c) :
    IsRegularizable fun x => ((c : ℝ) : EReal) * u x := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨⟨x, hx⟩, g, hg, hgu⟩ := hu
  refine ⟨⟨x, coe_mul_ne_bot hc' hx⟩, fun j => (g j).smul c hc, fun y i j hij => ?_,
    fun y => ?_⟩
  · simp only [FSData.eval_smul]
    exact mul_le_mul_of_nonneg_left (hg y hij) (by exact_mod_cast hc'.le)
  · simp only [FSData.eval_smul]
    rw [iInf_coe_mul_of_antitone (hg y) hc', ← hgu]

/-- `ℛ(Y)` is stable under addition of real constants (FHX Lemma 5.11(3)): use the approximants
`u_j + c_j` with rational `c_j ↓ c`. -/
theorem IsRegularizable.add_const (hu : IsRegularizable u) (c : ℝ) :
    IsRegularizable fun x => u x + (c : EReal) := by
  obtain ⟨q, hq, -, hqc⟩ := exists_antitone_rat_iInf_eq c
  obtain ⟨⟨x, hx⟩, g, hg, hgu⟩ := hu
  have hq' : Antitone fun j => (((q j : ℚ) : ℝ) : EReal) := fun i j hij => by
    show (((q j : ℚ) : ℝ) : EReal) ≤ ((q i : ℚ) : ℝ)
    exact_mod_cast hq hij
  refine ⟨⟨x, ?_⟩, fun j => (g j).addConst (q j), fun y i j hij => ?_, fun y => ?_⟩
  · rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨hx, EReal.coe_ne_bot c⟩
  · simp only [FSData.eval_addConst]
    exact add_le_add (hg y hij) (hq' hij)
  · simp only [FSData.eval_addConst]
    rw [iInf_add_of_antitone (hg y) hq' ((g 0).eval_ne_top y) (EReal.coe_ne_top _), hqc, ← hgu]

/-- Real constants are regularizable (if the analytification is nonempty). -/
theorem isRegularizable_const [Algebra.FiniteType k A] [Nonempty (Berk k A)] (c : ℝ) :
    IsRegularizable fun _ : Berk k A => (c : EReal) :=
  ((isRegularizable_max_const_finsetSup_fsTerm (k := k) (A := A) 0 (s := ∅)
    (by simp)).add_const c).congr fun x => by simp

end basic

/-! ### Pullbacks -/

section comap

variable {u : Berk k A → EReal} {B : Type*} [CommRing B] [Algebra k B]

/-- **FHX Lemma 5.11(4)** (`lem:reg-closure-elementary`): for a morphism
`π : Spec B → Spec A` with `B` of finite type and `u ∈ ℛ(Spec A)`, the pullback `u ∘ π^an` is
regularizable unless it is identically `-∞`: if `u_j ↓ u`, then
`max{u_j ∘ π^an, b'/(j+1) - (j+1)} ∈ FS(Spec B)` decrease to `u ∘ π^an`. -/
theorem IsRegularizable.comp_comap [Algebra.FiniteType k B] (φ : A →ₐ[k] B)
    (hu : IsRegularizable u) (hne : ∃ x, u (comap φ x) ≠ ⊥) :
    IsRegularizable fun x => u (comap φ x) := by
  obtain ⟨-, g, hg, hgu⟩ := hu
  refine ⟨hne, fun j => FSData.mapSup φ (g j) (FSData.truncStd k B j), fun x i j hij => ?_,
    fun x => ?_⟩
  · simp only [FSData.eval_mapSup]
    exact max_le_max (hg _ hij) (FSData.antitone_truncStd k B x hij)
  · simp only [FSData.eval_mapSup]
    rw [FSData.iInf_max_truncStd k B (hg _) x, ← hgu]

/-- Restriction of a regularizable function to a principal open `Y_f`, `f ≠ 0`, of an affine
variety is regularizable (FHX Lemma 5.11(4)): it is finite at the trivial valuation of `A_f`,
which lies over the trivial valuation of `A`. -/
theorem IsRegularizable.comp_awayComap [IsDomain A] [Algebra.FiniteType k A] {f : A}
    (hf : f ≠ 0) (hu : IsRegularizable u) :
    IsRegularizable fun y : Berk k (Localization.Away f) => u (awayComap f y) := by
  have := isDomain_localizationAway hf
  refine hu.comp_comap (IsScalarTower.toAlgHom k A (Localization.Away f)) ⟨triv, ?_⟩
  rw [← awayComap_eq, awayComap_triv]
  exact hu.triv_ne_bot

end comap

/-! ### Decreasing limits (FHX Lemma 5.11(2)) -/

section antitone

/-- **Diagonal approximation on compact sets** (`lem:diagonal-compact`). If regularizable
functions `u i` decrease to `u` and `K` is compact, there are FS functions `h m`, decreasing on
`K`, with limit `u` on `K`. -/
theorem exists_antitone_fs_of_antitone_regularizable {u : ℕ → Berk k A → EReal}
    (hu : ∀ i, IsRegularizable (u i)) (hmono : ∀ x, Antitone fun i => u i x)
    {K : Set (Berk k A)} (hK : IsCompact K) :
    ∃ h : ℕ → FSData k A, (∀ x ∈ K, Antitone fun m => (h m).eval x) ∧
      ∀ x ∈ K, ⨅ m, (h m).eval x = ⨅ i, u i x := by
  choose G hG hGu using fun i => (hu i).2
  obtain ⟨I, J, q, -, hanti, hlim⟩ := exists_antitone_diagonal hK (fun i j => (G i j).eval)
    (fun i j => (G i j).continuous_eval) (fun i j x => (G i j).eval_ne_bot x)
    (fun i j x => (G i j).eval_ne_top x) (fun i x => hG i x)
    (fun x => by simpa only [← hGu] using hmono x)
  refine ⟨fun m => (G (I m) (J m)).addConst (q m), fun x hx => ?_, fun x hx => ?_⟩
  · simpa only [FSData.eval_addConst] using hanti x hx
  · simp only [FSData.eval_addConst]
    rw [hlim x hx]
    simp only [← hGu]

universe u v

/-- **FHX Lemma 5.11(2)** (`lem:reg-decreasing`). On a normal affine variety, the limit of a
decreasing sequence of regularizable functions is regularizable unless it is identically `-∞`.

Every compact `K` lies in the interior of a compact `K'`; on `K'` the diagonal argument
(`exists_antitone_diagonal`, `lem:diagonal-compact`) gives FS functions decreasing to the limit,
which are convex PL on `interior K'`; the limit has logarithmic growth (it is bounded by `u 0`),
and the imported FHX Lemma 5.11(6) (`WuRegularization.localToGlobal`) applies. -/
theorem IsRegularizable.of_antitone {k : Type u} [Field k] [IsAlgClosed k] [WuRegularization.{u, v} k]
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A] {u : ℕ → Berk k A → EReal} (hu : ∀ i, IsRegularizable (u i))
    (hmono : ∀ x, Antitone fun i => u i x) (hne : ∃ x, (⨅ i, u i x) ≠ ⊥) :
    IsRegularizable fun x => ⨅ i, u i x := by
  refine WuRegularization.localToGlobal A _ hne
    ((hu 0).hasLogGrowth.mono fun x => iInf_le _ 0) fun K hK => ?_
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨h, hanti, hlim⟩ := exists_antitone_fs_of_antitone_regularizable hu hmono hK'
  exact ⟨interior K', isOpen_interior, hKK', fun m => (h m).eval,
    fun m => (h m).isConvexPLOn isOpen_interior, fun y hy => hanti y (interior_subset hy),
    fun y hy => (hlim y (interior_subset hy)).symm⟩

end antitone

end EnvelopeProperty
