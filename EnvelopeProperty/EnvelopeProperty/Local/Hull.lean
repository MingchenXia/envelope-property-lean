/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Defs
import EnvelopeProperty.Berkovich.Topology

/-!
# Polynomial hulls, the hull inequality and polyhedral neighbourhoods

Let `k` be a field with the trivial absolute value and `A` a commutative `k`-algebra. This file
develops the theory of polynomial hulls on the analytification `Berk k A = (Spec A)^an` from
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, §5.3
(`subsec:polynomial-convexity`).

For a set `K`, the polynomial hull is `K̂ = {y | log|f|(y) ≤ sup_K log|f| for all f ∈ A}`
(`EnvelopeProperty.hull`); an open set `D` is Runge if `K̂ ⊆ D` for all compact `K ⊆ D`, and a
function `u` satisfies the hull inequality if `u(y) ≤ sup_K u` for all compact `K` and `y ∈ K̂`.

## Main results

* Hulls (`lem:hull-basic`): `subset_hull`, `hull_mono`, `isClosed_hull`, `hull_hull`
  (`K̂̂ = K̂`, for any `K`), `isCompact_hull` (the hull of a compact set is compact: it is
  closed and lies in the product of the compact intervals `[0, sup_K |f|]`), `hull_empty`.
* The hull inequality (`lem:hull-basic`): it holds for `log|f|`, constants, terms
  `a log|f| + b` (`a > 0`), finite maxima, hence for every FS function
  (`FSData.satisfiesHullIneq`); it is preserved by decreasing limits of upper semicontinuous
  functions (`SatisfiesHullIneq.iInf_of_antitone`), via the Dini-type exchange of `inf` and `sup`
  on compact sets `iInf_iSup_eq_iSup_iInf_of_antitone`; hence every regularizable function
  satisfies it (`IsRegularizable.satisfiesHullIneq`).
* Directed unions of Runge open sets are Runge (`isRunge_iUnion_of_directed`,
  `isRunge_iUnion_of_monotone`).
* Sublevel sets `{g ≤ c}` of FS functions are compact: the functions of an FS function generate
  `A`, so the sublevel set lies in a closed polydisc. (This is also proved, publicly, as
  `FSData.isCompact_setOf_eval_le` in `EnvelopeProperty.Local.FS`, which this file does not
  import; the copy here is private.)
* The "power trick" `exists_lt_logAbs_of_notMem_hull`: a point outside `L̂` is separated from `L`
  by some `log|f|` with a gap of any prescribed size and a rational threshold.
* FHX Lemma 5.14 (`lem:polyhedral-neighborhoods`): (1) `exists_fs_polyhedral_nhd`, a polynomially
  convex compact set `H` inside an open set `U` admits `g ∈ FS(Y)`, `g ≥ 0`, with
  `H ⊆ int{g = 0}` and `{g ≤ 1} ⊆ U`; (2) `IsRunge.exists_fs_exhaustion`, a Runge open set is
  an increasing union of sets `{g_j < 1}` with `g_j ∈ FS(Y)` (for `k` countable).
-/

open scoped NNReal ENNReal Topology

open Filter Set Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Affine maps on `EReal` -/

/-- For `a > 0`, the inequality `a L + b ≤ c` with `c` real is solved for `L ∈ EReal`. -/
private theorem affine_le_coe_iff {a : ℝ} (ha : 0 < a) (b c : ℝ) (L : EReal) :
    (a : EReal) * L + (b : EReal) ≤ (c : EReal) ↔ L ≤ (((c - b) / a : ℝ) : EReal) := by
  induction L using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | coe L =>
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      le_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  | top => simp [EReal.coe_mul_top_of_pos ha]

/-- For `a > 0`, the inequality `a L + b < c` with `c` real is solved for `L ∈ EReal`. -/
private theorem affine_lt_coe_iff {a : ℝ} (ha : 0 < a) (b c : ℝ) (L : EReal) :
    (a : EReal) * L + (b : EReal) < (c : EReal) ↔ L < (((c - b) / a : ℝ) : EReal) := by
  induction L using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | coe L =>
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff,
      lt_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  | top => simp [EReal.coe_mul_top_of_pos ha]

/-- For `a > 0`, every sublevel set of `L ↦ a L + b` on `EReal` is a sublevel set of `L ↦ L`. -/
private theorem exists_affine_le_iff {a : ℝ} (ha : 0 < a) (b : ℝ) (c : EReal) :
    ∃ c' : EReal, ∀ L : EReal, (a : EReal) * L + (b : EReal) ≤ c ↔ L ≤ c' := by
  induction c using EReal.rec with
  | bot =>
    refine ⟨⊥, fun L => ?_⟩
    induction L using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos ha]
    | coe L => simp [← EReal.coe_mul, ← EReal.coe_add]
    | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe c => exact ⟨_, affine_le_coe_iff ha b c⟩
  | top => exact ⟨⊤, fun L => by simp⟩

/-! ### Auxiliary facts on FS functions

These duplicate a few basic facts proved in `EnvelopeProperty.Local.FS`, which this file does not
import. -/

private theorem continuous_fsTerm_aux (t : A × ℚ × ℚ) :
    Continuous (fsTerm t : Berk k A → EReal) := by
  by_cases ha : (t.2.1 : ℝ) = 0
  · have : (fsTerm t : Berk k A → EReal) = fun _ => ((t.2.2 : ℝ) : EReal) := by
      funext x; simp [fsTerm, ha]
    rw [this]; exact continuous_const
  · have hmul : Continuous fun x : Berk k A => ((t.2.1 : ℝ) : EReal) * logAbs t.1 x := by
      have hc : Continuous fun x : Berk k A => (((t.2.1 : ℝ) : EReal), logAbs t.1 x) :=
        continuous_const.prodMk (continuous_logAbs t.1)
      refine continuous_iff_continuousAt.2 fun x => ?_
      refine ContinuousAt.comp (f := fun x : Berk k A => (((t.2.1 : ℝ) : EReal), logAbs t.1 x))
        (g := fun p : EReal × EReal => p.1 * p.2) ?_ hc.continuousAt
      apply EReal.continuousAt_mul <;> simp [ha]
    have hc : Continuous fun x : Berk k A =>
        (((t.2.1 : ℝ) : EReal) * logAbs t.1 x, ((t.2.2 : ℝ) : EReal)) :=
      hmul.prodMk continuous_const
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2) ?_ hc.continuousAt
    apply EReal.continuousAt_add <;> simp

private theorem continuous_eval_aux (g : FSData k A) : Continuous g.eval := by
  have : Continuous fun x : Berk k A => g.terms.sup fun t => fsTerm t x := by
    have h := Continuous.finset_sup (s := g.terms)
      (f := fun t => (fsTerm (k := k) t : Berk k A → EReal)) fun t _ => continuous_fsTerm_aux t
    convert h using 1
    funext x
    rw [Finset.sup_apply]
  exact continuous_const.max this

private theorem fsTerm_le_eval_aux (g : FSData k A) {t : A × ℚ × ℚ} (ht : t ∈ g.terms)
    (x : Berk k A) : fsTerm t x ≤ g.eval x :=
  (Finset.le_sup (f := fun t => fsTerm t x) ht).trans (le_max_right _ _)

private theorem fsTerm_lt_coe_iff {t : A × ℚ × ℚ} (ht : 0 < t.2.1) (x : Berk k A) (c : ℝ) :
    fsTerm t x < (c : EReal) ↔ logAbs t.1 x < (((c - t.2.2) / t.2.1 : ℝ) : EReal) :=
  affine_lt_coe_iff (by exact_mod_cast ht) _ _ _

private theorem fsTerm_le_coe_iff {t : A × ℚ × ℚ} (ht : 0 < t.2.1) (x : Berk k A) (c : ℝ) :
    fsTerm t x ≤ (c : EReal) ↔ logAbs t.1 x ≤ (((c - t.2.2) / t.2.1 : ℝ) : EReal) :=
  affine_le_coe_iff (by exact_mod_cast ht) _ _ _

/-- The term `log|f| - b`. -/
private theorem fsTerm_one_neg_lt_coe_iff (f : A) (b : ℚ) (x : Berk k A) (c : ℝ) :
    fsTerm (f, (1 : ℚ), -b) x < (c : EReal) ↔ logAbs f x < ((c + b : ℝ) : EReal) := by
  rw [fsTerm_lt_coe_iff (by norm_num) x c]
  have e : ((c - (((f, (1 : ℚ), -b) : A × ℚ × ℚ).2.2 : ℝ)) /
      (((f, (1 : ℚ), -b) : A × ℚ × ℚ).2.1 : ℝ) : ℝ) = c + b := by
    push_cast; ring
  rw [e]

/-- The term `log|f| - b`. -/
private theorem coe_lt_fsTerm_one_neg_iff (f : A) (b : ℚ) (x : Berk k A) (c : ℝ) :
    (c : EReal) < fsTerm (f, (1 : ℚ), -b) x ↔ ((c + b : ℝ) : EReal) < logAbs f x := by
  rw [← not_le, ← not_le, fsTerm_le_coe_iff (by norm_num) x c]
  have e : ((c - (((f, (1 : ℚ), -b) : A × ℚ × ℚ).2.2 : ℝ)) /
      (((f, (1 : ℚ), -b) : A × ℚ × ℚ).2.1 : ℝ) : ℝ) = c + b := by
    push_cast; ring
  rw [e]

/-! ### Polynomial hulls -/

/-- Membership in the polynomial hull. -/
theorem mem_hull_iff {K : Set (Berk k A)} {y : Berk k A} :
    y ∈ hull K ↔ ∀ f : A, logAbs f y ≤ ⨆ x ∈ K, logAbs f x :=
  Iff.rfl

/-- On the hull, `log|f|` is bounded by any bound valid on `K`. -/
theorem logAbs_le_of_mem_hull {K : Set (Berk k A)} {y : Berk k A} (hy : y ∈ hull K) {f : A}
    {c : EReal} (hc : ∀ x ∈ K, logAbs f x ≤ c) : logAbs f y ≤ c :=
  (hy f).trans (iSup₂_le hc)

/-- On the hull, `|f|` is bounded by any bound valid on `K`. -/
theorem val_le_of_mem_hull {K : Set (Berk k A)} {y : Berk k A} (hy : y ∈ hull K) {f : A}
    {R : ℝ≥0} (hR : ∀ x ∈ K, x.val f ≤ R) : y.val f ≤ R := by
  have : logAbs f y ≤ ENNReal.log (R : ℝ≥0∞) :=
    logAbs_le_of_mem_hull hy fun x hx => ENNReal.log_monotone (ENNReal.coe_le_coe.2 (hR x hx))
  rwa [logAbs, ENNReal.log_le_log_iff, ENNReal.coe_le_coe] at this

/-- Every set is contained in its hull. -/
theorem subset_hull (K : Set (Berk k A)) : K ⊆ hull K := fun y hy f =>
  le_iSup₂ (f := fun x (_ : x ∈ K) => logAbs f x) y hy

/-- The hull is monotone. -/
theorem hull_mono {K L : Set (Berk k A)} (h : K ⊆ L) : hull K ⊆ hull L := fun _ hy f =>
  (hy f).trans (biSup_mono fun _ hx => h hx)

/-- The hull of any set is closed. -/
theorem isClosed_hull (K : Set (Berk k A)) : IsClosed (hull K) := by
  have : hull K = ⋂ f : A, {y | logAbs f y ≤ ⨆ x ∈ K, logAbs f x} := by
    ext; simp [hull]
  rw [this]
  exact isClosed_iInter fun f => isClosed_setOf_logAbs_le f _

/-- `sup_{K̂} log|f| = sup_K log|f|`. -/
theorem iSup_logAbs_hull (K : Set (Berk k A)) (f : A) :
    ⨆ x ∈ hull K, logAbs f x = ⨆ x ∈ K, logAbs f x :=
  le_antisymm (iSup₂_le fun _ hx => hx f) (biSup_mono fun _ hx => subset_hull K hx)

/-- **The hull is idempotent**: `K̂̂ = K̂` (`lem:hull-basic`). -/
theorem hull_hull (K : Set (Berk k A)) : hull (hull K) = hull K :=
  Set.ext fun _ => forall_congr' fun f => by rw [iSup_logAbs_hull]

/-- The hull of any set is polynomially convex. -/
theorem isPolyConvex_hull (K : Set (Berk k A)) : IsPolyConvex (hull K) :=
  hull_hull K

/-- The hull of the empty set is empty (`log|1| = 0 > -∞ = sup_∅ log|1|`). -/
@[simp]
theorem hull_empty : hull (∅ : Set (Berk k A)) = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  have := hy 1
  simp at this

/-- A set with a nonempty hull is nonempty. -/
theorem nonempty_of_mem_hull {K : Set (Berk k A)} {y : Berk k A} (hy : y ∈ hull K) :
    K.Nonempty := by
  rcases K.eq_empty_or_nonempty with rfl | h
  · simp at hy
  · exact h

/-- **The hull of a compact set is compact** (`lem:hull-basic`): it is closed, and `|f|` is
bounded on it by `sup_K |f|` for every `f`, so it lies in a product of compact intervals. -/
theorem isCompact_hull {K : Set (Berk k A)} (hK : IsCompact K) : IsCompact (hull K) := by
  choose R hR using exists_abs_le_of_isCompact hK
  rw [isInducing_toFun.isCompact_iff]
  refine (isCompact_univ_pi fun f => isCompact_Icc (a := (0 : ℝ≥0)) (b := R f)).of_isClosed_subset
    (isClosedEmbedding_toFun.isClosedMap _ (isClosed_hull K)) ?_
  rintro _ ⟨y, hy, rfl⟩ f -
  exact ⟨zero_le, val_le_of_mem_hull hy (hR f)⟩

/-! ### The hull inequality -/

/-- The hull inequality, phrased with upper bounds. -/
theorem satisfiesHullIneq_iff {u : Berk k A → EReal} :
    SatisfiesHullIneq u ↔ ∀ K : Set (Berk k A), IsCompact K → ∀ y ∈ hull K,
      ∀ c : EReal, (∀ x ∈ K, u x ≤ c) → u y ≤ c := by
  refine forall₂_congr fun K _ => forall₂_congr fun y _ => ?_
  exact ⟨fun h c hc => h.trans (iSup₂_le hc),
    fun h => h _ fun x hx => le_iSup₂ (f := fun x (_ : x ∈ K) => u x) x hx⟩

/-- The functions `log|f|` satisfy the hull inequality (by definition of the hull). -/
theorem satisfiesHullIneq_logAbs (f : A) : SatisfiesHullIneq (logAbs f : Berk k A → EReal) :=
  fun _ _ _ hy => hy f

/-- Constants satisfy the hull inequality (the hull of the empty set being empty). -/
theorem satisfiesHullIneq_const (c : EReal) : SatisfiesHullIneq fun _ : Berk k A => c := by
  intro K _ y hy
  obtain ⟨x, hx⟩ := nonempty_of_mem_hull hy
  exact le_iSup₂ (f := fun x (_ : x ∈ K) => c) x hx

/-- If every sublevel set of `u` is a sublevel set of `v`, and `v` satisfies the hull
inequality, then so does `u`. -/
theorem SatisfiesHullIneq.of_forall_exists_le_iff {u v : Berk k A → EReal}
    (hv : SatisfiesHullIneq v) (h : ∀ c : EReal, ∃ c' : EReal, ∀ x, u x ≤ c ↔ v x ≤ c') :
    SatisfiesHullIneq u := by
  rw [satisfiesHullIneq_iff] at hv ⊢
  intro K hK y hy c hc
  obtain ⟨c', hc'⟩ := h c
  exact (hc' y).2 (hv K hK y hy c' fun x hx => (hc' x).1 (hc x hx))

/-- A term `a log|f| + b` with `a > 0` satisfies the hull inequality. -/
theorem satisfiesHullIneq_fsTerm {t : A × ℚ × ℚ} (ht : 0 < t.2.1) :
    SatisfiesHullIneq (fsTerm t : Berk k A → EReal) :=
  (satisfiesHullIneq_logAbs t.1).of_forall_exists_le_iff fun c => by
    obtain ⟨c', hc'⟩ := exists_affine_le_iff (a := (t.2.1 : ℝ)) (by exact_mod_cast ht) t.2.2 c
    exact ⟨c', fun x => hc' _⟩

/-- The maximum of two functions satisfying the hull inequality satisfies it. -/
theorem SatisfiesHullIneq.max {u v : Berk k A → EReal} (hu : SatisfiesHullIneq u)
    (hv : SatisfiesHullIneq v) : SatisfiesHullIneq fun x => max (u x) (v x) :=
  fun K hK y hy => max_le ((hu K hK y hy).trans (iSup₂_mono fun _ _ => le_max_left _ _))
    ((hv K hK y hy).trans (iSup₂_mono fun _ _ => le_max_right _ _))

/-- A finite maximum of functions satisfying the hull inequality satisfies it. -/
theorem SatisfiesHullIneq.finset_sup {ι : Type*} {s : Finset ι} {u : ι → Berk k A → EReal}
    (h : ∀ i ∈ s, SatisfiesHullIneq (u i)) : SatisfiesHullIneq fun x => s.sup fun i => u i x :=
  fun K hK y hy => Finset.sup_le fun i hi =>
    (h i hi K hK y hy).trans (iSup₂_mono fun x _ => Finset.le_sup (f := fun i => u i x) hi)

/-- **FS functions satisfy the hull inequality** (`lem:hull-basic`): each term does. -/
theorem FSData.satisfiesHullIneq (g : FSData k A) : SatisfiesHullIneq g.eval :=
  (satisfiesHullIneq_const _).max
    (SatisfiesHullIneq.finset_sup fun t ht => satisfiesHullIneq_fsTerm (g.pos t ht))

/-- **Dini-type exchange of `inf` and `sup`.** If upper semicontinuous functions `u j` decrease
(along a directed index set) and `K` is compact, then `inf_j sup_K u j = sup_K inf_j u j`: for
`t > sup_K inf_j u j` the open sets `{u j < t}` increase and cover `K`. -/
theorem iInf_iSup_eq_iSup_iInf_of_antitone {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X → EReal}
    (hu : ∀ j, UpperSemicontinuous (u j)) (hmono : ∀ x, Antitone fun j => u j x)
    {K : Set X} (hK : IsCompact K) :
    ⨅ j, ⨆ x ∈ K, u j x = ⨆ x ∈ K, ⨅ j, u j x := by
  refine le_antisymm ?_ (iSup₂_le fun x hx => le_iInf fun j => (iInf_le _ j).trans
    (le_iSup₂ (f := fun x (_ : x ∈ K) => u j x) x hx))
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have hopen : ∀ j, IsOpen {x | u j x < t} := fun j =>
    upperSemicontinuous_iff_isOpen_preimage.1 (hu j) t
  have hcover : K ⊆ ⋃ j, {x | u j x < t} := by
    intro x hx
    obtain ⟨j, hj⟩ := iInf_lt_iff.1
      ((le_iSup₂ (f := fun x (_ : x ∈ K) => ⨅ j, u j x) x hx).trans_lt ht)
    exact mem_iUnion.2 ⟨j, hj⟩
  have hdir : Directed (· ⊆ ·) fun j => {x | u j x < t} := by
    intro i j
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    exact ⟨l, fun x hx => (hmono x hil).trans_lt hx, fun x hx => (hmono x hjl).trans_lt hx⟩
  obtain ⟨j, hj⟩ := hK.elim_directed_cover _ hopen hcover hdir
  exact (iInf_le _ j).trans (iSup₂_le fun x hx => (hj hx : u j x < t).le)

/-- The hull inequality passes to decreasing limits of upper semicontinuous functions. -/
theorem SatisfiesHullIneq.iInf_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {u : ι → Berk k A → EReal} (h : ∀ j, SatisfiesHullIneq (u j))
    (hu : ∀ j, UpperSemicontinuous (u j)) (hmono : ∀ x, Antitone fun j => u j x) :
    SatisfiesHullIneq fun x => ⨅ j, u j x := by
  intro K hK y hy
  calc ⨅ j, u j y ≤ ⨅ j, ⨆ x ∈ K, u j x := iInf_mono fun j => h j K hK y hy
    _ = ⨆ x ∈ K, ⨅ j, u j x := iInf_iSup_eq_iSup_iInf_of_antitone hu hmono hK

/-- **Regularizable functions satisfy the hull inequality** (`lem:hull-basic`). -/
theorem IsRegularizable.satisfiesHullIneq {u : Berk k A → EReal} (hu : IsRegularizable u) :
    SatisfiesHullIneq u := by
  obtain ⟨-, g, hmono, hlim⟩ := hu
  have e : u = fun x => ⨅ j, (g j).eval x := funext hlim
  rw [e]
  exact SatisfiesHullIneq.iInf_of_antitone (fun j => (g j).satisfiesHullIneq)
    (fun j => (continuous_eval_aux (g j)).upperSemicontinuous) hmono

/-! ### Runge sets -/

/-- **A directed union of Runge open sets is Runge** (`lem:hull-basic`): a compact subset of the
union lies in one of them. -/
theorem isRunge_iUnion_of_directed {ι : Type*} {D : ι → Set (Berk k A)}
    (hopen : ∀ i, IsOpen (D i)) (hR : ∀ i, IsRunge (D i)) (hdir : Directed (· ⊆ ·) D) :
    IsRunge (⋃ i, D i) := by
  intro K hKD hK
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : K = ∅ := by simpa using hKD
    subst this
    simp
  · obtain ⟨i, hi⟩ := hK.elim_directed_cover D hopen hKD hdir
    exact (hR i K hi hK).trans (subset_iUnion D i)

/-- **An increasing union of Runge open sets is Runge** (`lem:hull-basic`). -/
theorem isRunge_iUnion_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {D : ι → Set (Berk k A)} (hopen : ∀ i, IsOpen (D i)) (hR : ∀ i, IsRunge (D i))
    (hmono : Monotone D) : IsRunge (⋃ i, D i) :=
  isRunge_iUnion_of_directed hopen hR hmono.directed_le

/-! ### Sublevel sets of FS functions

`EnvelopeProperty.Local.FS` proves the same statement as `FSData.isCompact_setOf_eval_le`; the
version here is private to avoid a name clash in files importing both. -/

/-- **Sublevel sets of FS functions are compact**: since the functions of the terms generate `A`,
`{g ≤ c}` is a closed subset of a closed polydisc. -/
private theorem isCompact_setOf_eval_le_aux (g : FSData k A) (c : ℝ) :
    IsCompact {x | g.eval x ≤ (c : EReal)} := by
  obtain ⟨C, hC⟩ := (g.terms.image fun t : A × ℚ × ℚ => (c - t.2.2) / t.2.1).bddAbove
  refine (isCompact_setOf_forall_logAbs_le g.gen C).of_isClosed_subset
    (isClosed_le (continuous_eval_aux g) continuous_const) ?_
  rintro x hx _ ⟨t, ht, rfl⟩
  have h1 : fsTerm t x ≤ (c : EReal) := (fsTerm_le_eval_aux g ht x).trans hx
  rw [fsTerm_le_coe_iff (g.pos t ht)] at h1
  exact h1.trans (EReal.coe_le_coe_iff.2 (hC (Finset.mem_coe.2 (Finset.mem_image_of_mem _ ht))))

/-! ### The power trick -/

/-- **Separation from the hull with a prescribed gap.** If `x ∉ L̂` then for every `δ ∈ ℝ` there
are `f ∈ A` and `t ∈ ℚ` with `sup_L log|f| < t` and `t + δ < log|f|(x)`: take `f₀` with
`sup_L log|f₀| < log|f₀|(x)` and replace it by a large power. -/
theorem exists_lt_logAbs_of_notMem_hull {L : Set (Berk k A)} {x : Berk k A} (hx : x ∉ hull L)
    (δ : ℝ) : ∃ (f : A) (t : ℚ), (⨆ y ∈ L, logAbs f y) < ((t : ℝ) : EReal) ∧
      (((t : ℝ) + δ : ℝ) : EReal) < logAbs f x := by
  simp only [mem_hull_iff, not_forall, not_le] at hx
  obtain ⟨f, hf⟩ := hx
  have hxbot : logAbs f x ≠ ⊥ := ne_bot_of_gt hf
  have hxtop : logAbs f x ≠ ⊤ := logAbs_ne_top f x
  generalize hs : (⨆ y ∈ L, logAbs f y) = s at hf
  induction s using EReal.rec with
  | bot =>
    lift logAbs f x to ℝ using ⟨hxtop, hxbot⟩ with r hr
    obtain ⟨t, ht⟩ := exists_rat_lt (r - δ)
    refine ⟨f, t, by rw [hs]; exact EReal.bot_lt_coe _, ?_⟩
    rw [← hr, EReal.coe_lt_coe_iff]
    linarith
  | top => exact absurd hf not_top_lt
  | coe σ =>
    lift logAbs f x to ℝ using ⟨hxtop, hxbot⟩ with r hr
    rw [EReal.coe_lt_coe_iff] at hf
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / (r - σ))
    have hrσ : 0 < r - σ := sub_pos.2 hf
    have hN' : δ < N * (r - σ) := by rw [div_lt_iff₀ hrσ] at hN; linarith
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show (N : ℝ) * σ < N * r - δ by nlinarith)
    refine ⟨f ^ N, t, ?_, ?_⟩
    · refine lt_of_le_of_lt (iSup₂_le fun y hy => ?_) (EReal.coe_lt_coe_iff.2 ht1)
      have hy' : logAbs f y ≤ (σ : EReal) := hs ▸ le_iSup₂ (f := fun y (_ : y ∈ L) => logAbs f y) y hy
      rw [logAbs_pow, EReal.coe_mul, ← EReal.coe_natCast]
      exact mul_le_mul_of_nonneg_left hy' (by exact_mod_cast N.cast_nonneg)
    · rw [logAbs_pow, ← hr, ← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
      linarith

/-! ### Polyhedral neighbourhoods (FHX Lemma 5.14) -/

/-- **Polyhedral neighbourhoods** (FHX Lemma 5.14(1), `lem:polyhedral-neighborhoods`). Let `H`
be a polynomially convex compact set and `U ⊇ H` open. There is an FS function `g ≥ 0` with
`H ⊆ int{g = 0}` and `{g ≤ 1} ⊆ U`. Explicitly,
`g = max{0, max_l (log|z_l| - R), max_ℓ (log|f_ℓ| - a_ℓ)}` for generators `z_l` of `A`, a
rational `R` with `H ⊆ {max_l log|z_l| < R}`, and finitely many `f_ℓ`, `a_ℓ ∈ ℚ` with
`sup_H log|f_ℓ| < a_ℓ` covering `{max_l log|z_l| ≤ R + 1} \ U` by the sets
`{log|f_ℓ| > a_ℓ + 1}`. -/
theorem exists_fs_polyhedral_nhd [Algebra.FiniteType k A] {H U : Set (Berk k A)}
    (hH : IsCompact H) (hHc : IsPolyConvex H) (hU : IsOpen U) (hHU : H ⊆ U) :
    ∃ g : FSData k A, (∀ x, 0 ≤ g.eval x) ∧ H ⊆ interior {x | g.eval x = 0} ∧
      {x | g.eval x ≤ 1} ⊆ U := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (k := k) (A := A)
  -- A rational radius `R` with `H ⊆ {max_l log|z_l| < R}`.
  obtain ⟨R, hR⟩ : ∃ R : ℚ, ∀ x ∈ H, ∀ s ∈ S, logAbs s x < ((R : ℝ) : EReal) := by
    obtain ⟨M, hM⟩ := exists_forall_abs_le_of_isCompact hH S
    obtain ⟨R, hR⟩ := exists_rat_gt (M : ℝ)
    refine ⟨R, fun x hx s hs => lt_of_le_of_lt ((logAbs_le_coe_iff s x M).2 ?_)
      (EReal.coe_lt_coe_iff.2 hR)⟩
    refine (hM hx s hs).trans ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le]
    linarith [Real.add_one_le_exp (M : ℝ)]
  -- The compact set `E = {max_l log|z_l| ≤ R + 1} \ U`.
  set E : Set (Berk k A) :=
    {x | ∀ s ∈ (S : Set A), logAbs s x ≤ (((R : ℝ) + 1 : ℝ) : EReal)} \ U with hE
  have hEc : IsCompact E := (isCompact_setOf_forall_logAbs_le hS _).diff hU
  -- Separating functions for the points of `E`.
  have key : ∀ y ∈ E, ∃ p : A × ℚ, (⨆ x ∈ H, logAbs p.1 x) < ((p.2 : ℝ) : EReal) ∧
      (((p.2 : ℝ) + 1 : ℝ) : EReal) < logAbs p.1 y := by
    intro y hy
    have hyH : y ∉ hull H := by
      rw [hHc]
      exact fun h => hy.2 (hHU h)
    obtain ⟨f, t, h1, h2⟩ := exists_lt_logAbs_of_notMem_hull hyH 1
    exact ⟨(f, t), h1, h2⟩
  choose! p hp using key
  obtain ⟨T, hTE, hET⟩ := hEc.elim_nhds_subcover
    (fun y => {x | (((p y).2 : ℝ) + 1 : ℝ) < logAbs (p y).1 x})
    fun y hy => (isOpen_setOf_lt_logAbs _ _).mem_nhds (hp y hy).2
  -- The FS function.
  let terms : Finset (A × ℚ × ℚ) :=
    S.image (fun s => (s, (1 : ℚ), -R)) ∪ T.image (fun y => ((p y).1, (1 : ℚ), -(p y).2))
  have hpos : ∀ t ∈ terms, 0 < t.2.1 := by
    intro t ht
    simp only [terms, Finset.mem_union, Finset.mem_image] at ht
    rcases ht with ⟨s, -, rfl⟩ | ⟨y, -, rfl⟩ <;> exact one_pos
  have hgen : Algebra.adjoin k (Prod.fst '' (terms : Set (A × ℚ × ℚ))) = ⊤ := by
    rw [eq_top_iff, ← hS]
    exact Algebra.adjoin_mono fun s hs => ⟨(s, 1, -R),
      Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)), rfl⟩
  let g : FSData k A := ⟨terms, 0, hpos, hgen⟩
  have hg : ∀ x, g.eval x = max (((0 : ℚ) : ℝ) : EReal) (terms.sup fun t => fsTerm t x) :=
    fun x => rfl
  have hle : ∀ t ∈ terms, ∀ x, fsTerm t x ≤ g.eval x := fun t ht x => fsTerm_le_eval_aux g ht x
  refine ⟨g, fun x => ?_, ?_, ?_⟩
  · rw [hg]
    exact le_trans (by simp) (le_max_left _ _)
  · -- `g = 0` on an open set containing `H`.
    set O : Set (Berk k A) := (⋂ s ∈ S, {x | logAbs s x < ((R : ℝ) : EReal)}) ∩
      ⋂ y ∈ T, {x | logAbs (p y).1 x < (((p y).2 : ℝ) : EReal)} with hO
    have hOo : IsOpen O :=
      (isOpen_biInter_finset fun s _ => isOpen_setOf_logAbs_lt s _).inter
        (isOpen_biInter_finset fun y _ => isOpen_setOf_logAbs_lt _ _)
    have hHO : H ⊆ O := by
      intro x hx
      simp only [hO, mem_inter_iff, mem_iInter, mem_ofPred_eq]
      refine ⟨fun s hs => hR x hx s hs, fun y hy => ?_⟩
      exact lt_of_le_of_lt (le_iSup₂ (f := fun x (_ : x ∈ H) => logAbs (p y).1 x) x hx)
        (hp y (hTE y hy)).1
    have hO0 : O ⊆ {x | g.eval x = 0} := by
      intro x hx
      simp only [hO, mem_inter_iff, mem_iInter, mem_ofPred_eq] at hx
      have hneg : ∀ t ∈ terms, fsTerm t x < 0 := by
        intro t ht
        simp only [terms, Finset.mem_union, Finset.mem_image] at ht
        rcases ht with ⟨s, hs, rfl⟩ | ⟨y, hy, rfl⟩
        · rw [← EReal.coe_zero, fsTerm_one_neg_lt_coe_iff, zero_add]
          exact hx.1 s hs
        · rw [← EReal.coe_zero, fsTerm_one_neg_lt_coe_iff, zero_add]
          exact hx.2 y hy
      show g.eval x = 0
      rw [hg, max_eq_left]
      · simp
      · exact Finset.sup_le fun t ht => (hneg t ht).le.trans (by simp)
    exact hHO.trans (interior_maximal hO0 hOo)
  · -- `g > 1` off `U`.
    intro x hx
    by_contra hxU
    have hx1 : g.eval x ≤ ((1 : ℝ) : EReal) := by simpa using hx
    by_cases hxR : ∀ s ∈ (S : Set A), logAbs s x ≤ (((R : ℝ) + 1 : ℝ) : EReal)
    · have hxE : x ∈ E := ⟨hxR, hxU⟩
      obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 (hET hxE)
      have hmem : ((p y).1, (1 : ℚ), -(p y).2) ∈ terms :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hyT)
      have h1 : ((1 : ℝ) : EReal) < fsTerm ((p y).1, (1 : ℚ), -(p y).2) x := by
        rw [coe_lt_fsTerm_one_neg_iff, add_comm]
        exact hxy
      exact absurd (h1.trans_le ((hle _ hmem x).trans hx1)) (lt_irrefl _)
    · push Not at hxR
      obtain ⟨s, hs, hsx⟩ := hxR
      have hmem : (s, (1 : ℚ), -R) ∈ terms :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)
      have h1 : ((1 : ℝ) : EReal) < fsTerm (s, (1 : ℚ), -R) x := by
        rw [coe_lt_fsTerm_one_neg_iff, add_comm]
        exact hsx
      exact absurd (h1.trans_le ((hle _ hmem x).trans hx1)) (lt_irrefl _)

/-- **Runge open sets are exhausted by FS sublevel sets** (FHX Lemma 5.14(2),
`lem:polyhedral-neighborhoods`). For `k` countable, a Runge open set `D` is the union of an
increasing sequence of sets `{g_j < 1}` with `g_j ∈ FS(Y)`. Writing `D = ⋃ K_j` with `K_j`
compact, `g_j` is given by Lemma 5.14(1) for `H_j = (K_j ∪ Q_{j-1})^` and `D`, where
`Q_{-1} = ∅` and `Q_j = {g_j ≤ 1}` (compact). -/
theorem IsRunge.exists_fs_exhaustion [Algebra.FiniteType k A] [Countable k]
    {D : Set (Berk k A)} (hDo : IsOpen D) (hD : IsRunge D) :
    ∃ g : ℕ → FSData k A, (∀ j, {x | (g j).eval x < 1} ⊆ {x | (g (j + 1)).eval x < 1}) ∧
      ⋃ j, {x | (g j).eval x < 1} = D := by
  classical
  -- `D` is σ-compact.
  obtain ⟨K, hKc, hKD⟩ : IsSigmaCompact D := by
    have := hDo.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨g₀, -⟩ := exists_fs_polyhedral_nhd (k := k) (A := A) isCompact_empty hull_empty
    isOpen_univ (empty_subset _)
  have hstep : ∀ (n : ℕ) (Q : Set (Berk k A)), ∃ g : FSData k A,
      IsCompact Q → Q ⊆ D → K n ∪ Q ⊆ {x | g.eval x < 1} ∧ {x | g.eval x ≤ 1} ⊆ D := by
    intro n Q
    by_cases hQ : IsCompact Q ∧ Q ⊆ D
    · have hKQc : IsCompact (K n ∪ Q) := (hKc n).union hQ.1
      have hKQD : K n ∪ Q ⊆ D := union_subset (hKD ▸ subset_iUnion K n) hQ.2
      obtain ⟨g, -, hg0, hg1⟩ := exists_fs_polyhedral_nhd (isCompact_hull hKQc)
        (isPolyConvex_hull _) hDo (hD _ hKQD hKQc)
      refine ⟨g, fun _ _ => ⟨fun x hx => ?_, hg1⟩⟩
      have : x ∈ {x | g.eval x = 0} := interior_subset (hg0 (subset_hull _ hx))
      show g.eval x < 1
      rw [show g.eval x = 0 from this]
      exact zero_lt_one
    · exact ⟨g₀, fun h1 h2 => absurd ⟨h1, h2⟩ hQ⟩
  choose G hG using hstep
  let P : ℕ → Set (Berk k A) := fun n =>
    Nat.rec (motive := fun _ => Set (Berk k A)) ∅ (fun n Q => {x | (G n Q).eval x ≤ 1}) n
  have hPs : ∀ n, P (n + 1) = {x | (G n (P n)).eval x ≤ 1} := fun n => rfl
  have hP : ∀ n, IsCompact (P n) ∧ P n ⊆ D := by
    intro n
    induction n with
    | zero => exact ⟨isCompact_empty, empty_subset _⟩
    | succ n ih =>
      rw [hPs]
      exact ⟨by simpa using isCompact_setOf_eval_le_aux (G n (P n)) 1,
        (hG n (P n) ih.1 ih.2).2⟩
  refine ⟨fun n => G n (P n), fun n x hx => ?_, ?_⟩
  · have hx' : x ∈ P (n + 1) := by
      rw [hPs]
      exact (show (G n (P n)).eval x < 1 from hx).le
    exact (hG (n + 1) (P (n + 1)) (hP (n + 1)).1 (hP (n + 1)).2).1 (subset_union_right hx')
  · apply subset_antisymm
    · exact iUnion_subset fun n x hx => (hG n (P n) (hP n).1 (hP n).2).2
        (show (G n (P n)).eval x < 1 from hx).le
    · intro x hx
      rw [← hKD] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, (hG n (P n) (hP n).1 (hP n).2).1 (subset_union_left hn)⟩

end EnvelopeProperty
