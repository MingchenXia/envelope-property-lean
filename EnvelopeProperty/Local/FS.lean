/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Defs
import EnvelopeProperty.Berkovich.Topology

/-!
# Affine Fubini–Study functions

Basic theory of the affine Fubini–Study functions of Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Definition 5.7 (`def:regularizable`), on the analytification of
an affine `k`-scheme `Spec A`:
`g = max{a₁ log|f₁| + b₁, …, a_r log|f_r| + b_r, b₀}` with `aᵢ ∈ ℚ_{>0}`, `bᵢ ∈ ℚ` and the `fᵢ`
including generators of `A`.

## Main results

* Basic properties (the remark after Definition 5.7): `FSData.eval` is continuous, real valued
  (`FSData.eval_ne_bot`, `FSData.eval_ne_top`), bounded below by its constant term, and has
  compact sublevel sets (`FSData.isCompact_setOf_eval_le`).
* Operations on FS data, each with an `eval` lemma: `FSData.sup` (maximum), `FSData.addConst`,
  `FSData.smul` (positive rational multiple), `FSData.add` (sum: a sum of maxima is the maximum of
  the pairwise sums, and `a log|f| + a' log|f'| = N⁻¹ log|f^p f'^{p'}|`), `FSData.addTerms`,
  `FSData.mapSup` (pullback along a `k`-algebra map, joined with FS data on the target) and the
  standard function `FSData.std k A = max{0, log|z₁|, …, log|z_n|}` for chosen generators.
* Convex PL functions (FHX Lemma 5.2(1),(3) for convex PL functions, `lem:local-basic`):
  `IsConvexPLOn` is local, stable under restriction to open subsets, finite maxima, sums,
  nonnegative rational multiples, rational translates and addition of `q log|f|` where `f` does not
  vanish; and the gluing statement `IsConvexPLOn.piecewise_max`.
* FS functions are convex PL (`FSData.isConvexPLOn_univ`), by "the argument following (5.2)":
  near a point, the terms whose function vanishes there are `< b₀` and may be dropped.
* Growth estimates (FHX Lemma 5.8, `lem:growth`): `FSData.exists_eval_comap_le` (pullback along a
  morphism, via the degree estimate `log|f| ≤ d max{0, log|z_l|}`) and
  `FSData.exists_eval_le_comap_of_isIntegral` (along a finite morphism, via the integral equation
  estimate `valuation_le_of_monic_eval₂_eq_zero`).
* Closure properties of `HasLogGrowth` (the remarks after Lemma 5.8).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Auxiliary facts on `log |f|` -/

namespace Berk

/-- Where `f` does not vanish, `log |f|` is the real logarithm of `|f|`. -/
theorem logAbs_eq_coe_log {f : A} {y : Berk k A} (h : y.val f ≠ 0) :
    logAbs f y = ((Real.log (y.val f : ℝ) : ℝ) : EReal) := by
  rw [logAbs_def, ENNReal.log_of_nnreal h]

/-- `log |f| ≤ R` as soon as `|f| ≤ exp R`. -/
theorem logAbs_le_coe_of_le_exp {f : A} {y : Berk k A} {R : ℝ}
    (h : (y.val f : ℝ) ≤ Real.exp R) : logAbs f y ≤ (R : EReal) := by
  by_cases hf : y.val f = 0
  · rw [(logAbs_eq_bot_iff f y).2 hf]; exact bot_le
  · rw [logAbs_eq_coe_log hf, EReal.coe_le_coe_iff]
    have hpos : (0 : ℝ) < y.val f := by
      rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hf
    exact (Real.log_le_iff_le_exp hpos).2 h

end Berk

/-! ### Terms `a log|f| + b` -/

theorem fsTerm_def (t : A × ℚ × ℚ) (x : Berk k A) :
    fsTerm t x = ((t.2.1 : ℝ) : EReal) * logAbs t.1 x + ((t.2.2 : ℝ) : EReal) := rfl

/-- Multiplication by a nonnegative real does not produce `⊤` from a value `≠ ⊤`. -/
theorem ereal_coe_mul_ne_top {a : ℝ} (ha : 0 ≤ a) {L : EReal} (hL : L ≠ ⊤) :
    (a : EReal) * L ≠ ⊤ := by
  induction L using EReal.rec with
  | bot =>
    rcases ha.eq_or_lt with h | h
    · simp [← h]
    · simp [EReal.coe_mul_bot_of_pos h]
  | coe l => exact (EReal.coe_ne_top (a * l)) ∘ fun h => by rw [EReal.coe_mul]; exact h
  | top => exact absurd rfl hL

theorem fsTerm_ne_top {t : A × ℚ × ℚ} (ht : 0 ≤ t.2.1) (x : Berk k A) : fsTerm t x ≠ ⊤ := by
  rw [fsTerm_def]
  refine EReal.add_ne_top ?_ (EReal.coe_ne_top _)
  exact ereal_coe_mul_ne_top (by exact_mod_cast ht) (logAbs_ne_top _ _)

theorem fsTerm_eq_bot {t : A × ℚ × ℚ} (ht : 0 < t.2.1) {x : Berk k A} (hx : x.val t.1 = 0) :
    fsTerm t x = ⊥ := by
  rw [fsTerm_def, (logAbs_eq_bot_iff _ _).2 hx, EReal.coe_mul_bot_of_pos (by exact_mod_cast ht),
    EReal.bot_add]

/-- Where `f` does not vanish, the term `a log|f| + b` is the real number `a log|f| + b`. -/
theorem fsTerm_eq_coe {t : A × ℚ × ℚ} {x : Berk k A} (hx : x.val t.1 ≠ 0) :
    fsTerm t x = (((t.2.1 : ℝ) * Real.log (x.val t.1 : ℝ) + t.2.2 : ℝ) : EReal) := by
  rw [fsTerm_def, logAbs_eq_coe_log hx]
  norm_cast

@[fun_prop]
theorem continuous_fsTerm (t : A × ℚ × ℚ) : Continuous (fsTerm t : Berk k A → EReal) := by
  by_cases ha : (t.2.1 : ℝ) = 0
  · have : (fsTerm t : Berk k A → EReal) = fun _ => ((t.2.2 : ℝ) : EReal) := by
      funext x; simp [fsTerm_def, ha]
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

/-- Shifting the constant of a term. -/
theorem fsTerm_add_const (t : A × ℚ × ℚ) (q : ℚ) (x : Berk k A) :
    fsTerm (t.1, t.2.1, t.2.2 + q) x = fsTerm t x + ((q : ℝ) : EReal) := by
  simp only [fsTerm_def, Rat.cast_add, EReal.coe_add, add_assoc]

theorem fsTerm_const_add (t : A × ℚ × ℚ) (q : ℚ) (x : Berk k A) :
    fsTerm (t.1, t.2.1, q + t.2.2) x = ((q : ℝ) : EReal) + fsTerm t x := by
  rw [add_comm q, fsTerm_add_const, add_comm]

theorem fsTerm_smul (t : A × ℚ × ℚ) {c : ℚ} (hc : 0 ≤ c) (x : Berk k A) :
    fsTerm (t.1, c * t.2.1, c * t.2.2) x = ((c : ℝ) : EReal) * fsTerm t x := by
  simp only [fsTerm_def, Rat.cast_mul, EReal.coe_mul]
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc) (EReal.coe_ne_top _),
    mul_assoc]

/-- The term `(f^p f'^{p'}, 1/N, b + b')` representing the sum of the terms `(f, a, b)` and
`(f', a', b')` (for `a, a' > 0`), with `N = den a · den a'`, `p = num a · den a'`,
`p' = num a' · den a`. -/
def fsTermAdd (t t' : A × ℚ × ℚ) : A × ℚ × ℚ :=
  (t.1 ^ (t.2.1.num.toNat * t'.2.1.den) * t'.1 ^ (t'.2.1.num.toNat * t.2.1.den),
    1 / ((t.2.1.den : ℚ) * t'.2.1.den), t.2.2 + t'.2.2)

theorem fsTermAdd_pos (t t' : A × ℚ × ℚ) : 0 < (fsTermAdd t t').2.1 := by
  simp only [fsTermAdd]
  positivity

/-- A positive natural number times `⊥` in `EReal`. -/
theorem ereal_natCast_mul_bot {n : ℕ} (hn : 0 < n) : (n : EReal) * ⊥ = ⊥ := by
  rw [← EReal.coe_natCast]
  exact EReal.coe_mul_bot_of_pos (by exact_mod_cast hn)

theorem fsTerm_fsTermAdd {t t' : A × ℚ × ℚ} (ht : 0 < t.2.1) (ht' : 0 < t'.2.1)
    (x : Berk k A) : fsTerm (fsTermAdd t t') x = fsTerm t x + fsTerm t' x := by
  obtain ⟨f, a, b⟩ := t
  obtain ⟨f', a', b'⟩ := t'
  simp only at ht ht'
  have hnum : 0 < a.num := Rat.num_pos.2 ht
  have hnum' : 0 < a'.num := Rat.num_pos.2 ht'
  have hp : 0 < a.num.toNat * a'.den := Nat.mul_pos (by omega) a'.den_pos
  have hp' : 0 < a'.num.toNat * a.den := Nat.mul_pos (by omega) a.den_pos
  simp only [fsTermAdd, fsTerm_def, logAbs_mul, logAbs_pow]
  by_cases hf : x.val f = 0
  · rw [(logAbs_eq_bot_iff f x).2 hf, ereal_natCast_mul_bot hp, EReal.bot_add,
      EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add,
      EReal.coe_mul_bot_of_pos (by exact_mod_cast ht), EReal.bot_add, EReal.bot_add]
  by_cases hf' : x.val f' = 0
  · rw [(logAbs_eq_bot_iff f' x).2 hf', ereal_natCast_mul_bot hp', EReal.add_bot,
      EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add,
      EReal.coe_mul_bot_of_pos (by exact_mod_cast ht'), EReal.bot_add, EReal.add_bot]
  rw [logAbs_eq_coe_log hf, logAbs_eq_coe_log hf', ← EReal.coe_natCast, ← EReal.coe_natCast]
  norm_cast
  have ha : (a : ℝ) = (a.num : ℝ) / (a.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have ha' : (a' : ℝ) = (a'.num : ℝ) / (a'.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have e1 : ((a.num.toNat : ℕ) : ℝ) = (a.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have e2 : ((a'.num.toNat : ℕ) : ℝ) = (a'.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum'.le
  have hd : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hd' : (a'.den : ℝ) ≠ 0 := by exact_mod_cast a'.den_ne_zero
  push_cast
  rw [e1, e2, ha, ha']
  field_simp
  ring

/-! ### Basic properties of FS functions -/

namespace FSData

variable (g g' : FSData k A)

theorem eval_def (x : Berk k A) :
    g.eval x = max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t x) := rfl

theorem const_le_eval (x : Berk k A) : ((g.const : ℝ) : EReal) ≤ g.eval x :=
  le_max_left _ _

theorem fsTerm_le_eval {t : A × ℚ × ℚ} (ht : t ∈ g.terms) (x : Berk k A) :
    fsTerm t x ≤ g.eval x :=
  (Finset.le_sup (f := fun t => fsTerm t x) ht).trans (le_max_right _ _)

theorem eval_ne_bot (x : Berk k A) : g.eval x ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (g.const_le_eval x)

theorem eval_lt_top (x : Berk k A) : g.eval x < ⊤ :=
  max_lt (EReal.coe_lt_top _) ((Finset.sup_lt_iff (bot_lt_top)).2 fun t ht =>
    (fsTerm_ne_top (g.pos t ht).le x).lt_top)

theorem eval_ne_top (x : Berk k A) : g.eval x ≠ ⊤ :=
  (g.eval_lt_top x).ne

/-- The (real) value of an FS function. -/
def evalReal (x : Berk k A) : ℝ := (g.eval x).toReal

theorem coe_evalReal (x : Berk k A) : ((g.evalReal x : ℝ) : EReal) = g.eval x :=
  EReal.coe_toReal (g.eval_ne_top x) (g.eval_ne_bot x)

theorem const_le_evalReal (x : Berk k A) : (g.const : ℝ) ≤ g.evalReal x := by
  rw [← EReal.coe_le_coe_iff, coe_evalReal]; exact g.const_le_eval x

@[fun_prop]
theorem continuous_eval : Continuous g.eval := by
  have : Continuous fun x : Berk k A => g.terms.sup fun t => fsTerm t x := by
    have h := Continuous.finset_sup (s := g.terms)
      (f := fun t => (fsTerm (k := k) t : Berk k A → EReal)) fun t _ => continuous_fsTerm t
    convert h using 1
    funext x
    rw [Finset.sup_apply]
  exact continuous_const.max this

theorem continuous_evalReal : Continuous g.evalReal :=
  EReal.continuousOn_toReal.comp_continuous g.continuous_eval fun x => by
    simp [g.eval_ne_top x, g.eval_ne_bot x]

end FSData

theorem isFS_eval (g : FSData k A) : IsFS g.eval := ⟨g, fun _ => rfl⟩

/-! ### Operations on FS data -/

namespace FSData

variable (g g' : FSData k A)

theorem adjoin_eq_top_of_subset {s : Finset (A × ℚ × ℚ)} (hs : g.terms ⊆ s) :
    Algebra.adjoin k (Prod.fst '' (s : Set (A × ℚ × ℚ))) = ⊤ :=
  eq_top_iff.2 (g.gen ▸ Algebra.adjoin_mono (Set.image_mono (by exact_mod_cast hs)))

theorem adjoin_image_eq_top (φ : A × ℚ × ℚ → A × ℚ × ℚ) (hφ : ∀ t, (φ t).1 = t.1)
    [DecidableEq (A × ℚ × ℚ)] :
    Algebra.adjoin k (Prod.fst '' ((g.terms.image φ : Finset _) : Set (A × ℚ × ℚ))) = ⊤ := by
  rw [Finset.coe_image, Set.image_image]
  simp only [hφ]
  exact g.gen

open Classical in
/-- The maximum of two FS functions. -/
def sup : FSData k A where
  terms := g.terms ∪ g'.terms
  const := max g.const g'.const
  pos t ht := by
    rcases Finset.mem_union.1 ht with h | h
    exacts [g.pos t h, g'.pos t h]
  gen := g.adjoin_eq_top_of_subset Finset.subset_union_left

theorem coe_max_rat (q q' : ℚ) :
    (((max q q' : ℚ) : ℝ) : EReal) = max ((q : ℝ) : EReal) ((q' : ℝ) : EReal) := by
  rw [Rat.cast_max]
  exact EReal.coe_strictMono.monotone.map_max

@[simp]
theorem eval_sup (x : Berk k A) : (g.sup g').eval x = max (g.eval x) (g'.eval x) := by
  classical
  simp only [eval_def, sup, Finset.sup_union, coe_max_rat]
  exact max_max_max_comm _ _ _ _

open Classical in
/-- Adding a rational constant to an FS function. -/
def addConst (q : ℚ) : FSData k A where
  terms := g.terms.image fun t => (t.1, t.2.1, t.2.2 + q)
  const := g.const + q
  pos t ht := by
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact g.pos t' ht'
  gen := g.adjoin_image_eq_top (fun t => (t.1, t.2.1, t.2.2 + q)) fun _ => rfl

theorem sup_add_coe {ι : Type*} (s : Finset ι) (F : ι → EReal) (c : EReal) :
    s.sup F + c = s.sup fun i => F i + c :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (g := fun y => y + c)
    (fun _ _ h => add_le_add_left h c) (EReal.bot_add c)

theorem coe_add_sup {ι : Type*} (s : Finset ι) (F : ι → EReal) (c : EReal) :
    c + s.sup F = s.sup fun i => c + F i := by
  rw [add_comm, sup_add_coe]
  simp only [add_comm]

@[simp]
theorem eval_addConst (q : ℚ) (x : Berk k A) :
    (g.addConst q).eval x = g.eval x + ((q : ℝ) : EReal) := by
  classical
  simp only [eval_def, addConst, Finset.sup_image, Function.comp_def, fsTerm_add_const,
    ← sup_add_coe, Rat.cast_add, EReal.coe_add]
  exact max_add_add_right _ _ _

open Classical in
/-- A positive rational multiple of an FS function. -/
def smul (c : ℚ) (hc : 0 < c) : FSData k A where
  terms := g.terms.image fun t => (t.1, c * t.2.1, c * t.2.2)
  const := c * g.const
  pos t ht := by
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact mul_pos hc (g.pos t' ht')
  gen := g.adjoin_image_eq_top (fun t => (t.1, c * t.2.1, c * t.2.2)) fun _ => rfl

theorem coe_mul_sup {ι : Type*} (s : Finset ι) (F : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * s.sup F = s.sup fun i => (c : EReal) * F i :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (g := fun y => (c : EReal) * y)
    (fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hc.le))
    (EReal.coe_mul_bot_of_pos hc)

@[simp]
theorem eval_smul (c : ℚ) (hc : 0 < c) (x : Berk k A) :
    (g.smul c hc).eval x = ((c : ℝ) : EReal) * g.eval x := by
  classical
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  simp only [eval_def, smul, Finset.sup_image, Function.comp_def, fsTerm_smul _ hc.le,
    ← coe_mul_sup _ _ hc', Rat.cast_mul, EReal.coe_mul]
  exact (Monotone.map_max fun _ _ h => mul_le_mul_of_nonneg_left h
    (by exact_mod_cast hc'.le)).symm

open Classical in
/-- The sum of two FS functions: a sum of two maxima is the maximum of the pairwise sums. -/
def add : FSData k A where
  terms := g.terms.image (fun t => (t.1, t.2.1, t.2.2 + g'.const)) ∪
    g'.terms.image (fun t => (t.1, t.2.1, g.const + t.2.2)) ∪
    (g.terms ×ˢ g'.terms).image (fun tt => fsTermAdd tt.1 tt.2)
  const := g.const + g'.const
  pos t ht := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product] at ht
    rcases ht with (⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩) | ⟨tt, -, rfl⟩
    · exact g.pos t' ht'
    · exact g'.pos t' ht'
    · exact fsTermAdd_pos _ _
  gen := by
    refine eq_top_iff.2 ((g.adjoin_image_eq_top (fun t => (t.1, t.2.1, t.2.2 + g'.const))
      fun _ => rfl) ▸ Algebra.adjoin_mono (Set.image_mono ?_))
    intro t ht
    simp only [Finset.coe_union, Set.mem_union]
    exact Or.inl (Or.inl ht)

@[simp]
theorem eval_add (x : Berk k A) : (g.add g').eval x = g.eval x + g'.eval x := by
  classical
  have h3 : ((g.terms ×ˢ g'.terms).sup fun tt => fsTerm (fsTermAdd tt.1 tt.2) x) =
      (g.terms.sup fun t => fsTerm t x) + (g'.terms.sup fun t => fsTerm t x) := by
    rw [Finset.sup_product_left, sup_add_coe]
    refine Finset.sup_congr rfl fun t ht => ?_
    rw [coe_add_sup]
    exact Finset.sup_congr rfl fun t' ht' => fsTerm_fsTermAdd (g.pos t ht) (g'.pos t' ht') x
  simp only [eval_def, add, Finset.sup_union, Finset.sup_image, Function.comp_def,
    fsTerm_add_const, fsTerm_const_add, h3, ← sup_add_coe, ← coe_add_sup, Rat.cast_add,
    EReal.coe_add, ← max_add_add_right, ← max_add_add_left]
  simp only [max_assoc]

open Classical in
/-- Adding further terms `(f, a, b)` with `a > 0` to an FS function. -/
def addTerms (s : Finset (A × ℚ × ℚ)) (hs : ∀ t ∈ s, 0 < t.2.1) : FSData k A where
  terms := g.terms ∪ s
  const := g.const
  pos t ht := by
    rcases Finset.mem_union.1 ht with h | h
    exacts [g.pos t h, hs t h]
  gen := g.adjoin_eq_top_of_subset Finset.subset_union_left

@[simp]
theorem eval_addTerms (s : Finset (A × ℚ × ℚ)) (hs : ∀ t ∈ s, 0 < t.2.1) (x : Berk k A) :
    (g.addTerms s hs).eval x = max (g.eval x) (s.sup fun t => fsTerm t x) := by
  classical
  simp only [eval_def, addTerms, Finset.sup_union, max_assoc]

section mapSup

variable {B : Type*} [CommRing B] [Algebra k B]

open Classical in
/-- The FS function `max{g ∘ φ^an, g'}` on `Spec B`, for a `k`-algebra map `φ : A → B`, FS data
`g` on `Spec A` and FS data `g'` on `Spec B` (which supplies generators of `B`). -/
def mapSup (φ : A →ₐ[k] B) (g : FSData k A) (g' : FSData k B) : FSData k B where
  terms := g.terms.image (fun t => (φ t.1, t.2.1, t.2.2)) ∪ g'.terms
  const := max g.const g'.const
  pos t ht := by
    rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 h
      exact g.pos t' ht'
    · exact g'.pos t h
  gen := g'.adjoin_eq_top_of_subset Finset.subset_union_right

@[simp]
theorem eval_mapSup (φ : A →ₐ[k] B) (g : FSData k A) (g' : FSData k B) (x : Berk k B) :
    (mapSup φ g g').eval x = max (g.eval (comap φ x)) (g'.eval x) := by
  classical
  simp only [eval_def, mapSup, Finset.sup_union, Finset.sup_image, Function.comp_def,
    coe_max_rat]
  exact max_max_max_comm _ _ _ _

end mapSup

section std

variable (k A) [Algebra.FiniteType k A]

/-- A fixed finite set of generators of the finitely generated `k`-algebra `A`. -/
def stdGens : Finset A :=
  Classical.choose (Algebra.FiniteType.out (R := k) (A := A))

theorem adjoin_stdGens : Algebra.adjoin k (stdGens k A : Set A) = ⊤ :=
  Classical.choose_spec (Algebra.FiniteType.out (R := k) (A := A))

open Classical in
/-- The standard FS function `max{0, log|z₁|, …, log|z_n|}` for the generators `stdGens k A`. -/
def std : FSData k A where
  terms := (stdGens k A).image fun s => (s, 1, 0)
  const := 0
  pos t ht := by
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 ht
    exact one_pos
  gen := by
    rw [Finset.coe_image, Set.image_image]
    simpa using adjoin_stdGens k A

theorem eval_std (x : Berk k A) :
    (std k A).eval x = max 0 ((stdGens k A).sup fun s => logAbs s x) := by
  classical
  simp [eval_def, std, Finset.sup_image, Function.comp_def, fsTerm_def]

theorem eval_std_nonneg (x : Berk k A) : 0 ≤ (std k A).eval x := by
  rw [eval_std]; exact le_max_left _ _

theorem const_std : (std k A).const = 0 := rfl

end std

end FSData

/-! ### The class `FS(Y)` -/

namespace IsFS

variable {u v : Berk k A → EReal}

theorem sup (hu : IsFS u) (hv : IsFS v) : IsFS fun x => max (u x) (v x) := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨g', hg'⟩ := hv
  exact ⟨g.sup g', fun x => by simp [hg, hg']⟩

theorem add (hu : IsFS u) (hv : IsFS v) : IsFS fun x => u x + v x := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨g', hg'⟩ := hv
  exact ⟨g.add g', fun x => by simp [hg, hg']⟩

theorem add_const (hu : IsFS u) (q : ℚ) : IsFS fun x => u x + ((q : ℝ) : EReal) := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g.addConst q, fun x => by simp [hg]⟩

theorem smul (hu : IsFS u) {c : ℚ} (hc : 0 < c) : IsFS fun x => ((c : ℝ) : EReal) * u x := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g.smul c hc, fun x => by simp [hg]⟩

theorem continuous (hu : IsFS u) : Continuous u := by
  obtain ⟨g, hg⟩ := hu
  rw [show u = g.eval from funext hg]
  exact g.continuous_eval

end IsFS

/-! ### Convex PL functions -/

section ConvexPL

variable {U V : Set (Berk k A)} {u v : Berk k A → EReal}

/-- A set on which some function is convex PL is open (it is covered by the open sets `W`). -/
theorem IsConvexPLOn.isOpen (h : IsConvexPLOn U u) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, hWU, -⟩ := h x hx
  exact ⟨W, hWU, hW, hxW⟩

/-- Restriction of a convex PL function to an open subset. -/
theorem IsConvexPLOn.mono (h : IsConvexPLOn U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsConvexPLOn V u := by
  intro x hx
  obtain ⟨W, hW, hxW, -, n, f, s, hs, hf, hu⟩ := h x (hVU hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, Set.inter_subset_right, n, f, s, hs,
    fun y hy => hf y hy.1, fun y hy => hu y hy.1⟩

theorem IsConvexPLOn.congr (h : IsConvexPLOn U u) (heq : ∀ y ∈ U, u y = v y) :
    IsConvexPLOn U v := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, n, f, s, hs, hf, hu⟩ := h x hx
  exact ⟨W, hW, hxW, hWU, n, f, s, hs, hf, fun y hy => (heq y (hWU hy)).symm.trans (hu y hy)⟩

/-- Being convex PL is a local property. -/
theorem isConvexPLOn_of_local
    (h : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsConvexPLOn V u) : IsConvexPLOn U u := by
  intro x hx
  obtain ⟨V, -, hxV, hVU, hu⟩ := h x hx
  obtain ⟨W, hW, hxW, hWV, rest⟩ := hu x hxV
  exact ⟨W, hW, hxW, hWV.trans hVU, rest⟩

theorem isConvexPLOn_iff_local : IsConvexPLOn U u ↔
    ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsConvexPLOn V u :=
  ⟨fun h _ hx => ⟨U, h.isOpen, hx, subset_rfl, h⟩, isConvexPLOn_of_local⟩

/-- Rational constants are convex PL on open sets. -/
theorem isConvexPLOn_const (hU : IsOpen U) (q : ℚ) :
    IsConvexPLOn U fun _ => ((q : ℝ) : EReal) := by
  intro x hx
  refine ⟨U, hU, hx, subset_rfl, 0, Fin.elim0, {(0, q)}, Finset.singleton_nonempty _,
    fun y _ i => i.elim0, fun y _ => ?_⟩
  simp [tropAffine]

/-- `q log|f|` is convex PL where `f` does not vanish, for any `q ∈ ℚ`. -/
theorem isConvexPLOn_smul_logAbs (f : A) (q : ℚ) :
    IsConvexPLOn {y : Berk k A | y.val f ≠ 0} fun y => ((q : ℝ) : EReal) * logAbs f y := by
  intro x hx
  refine ⟨_, isOpen_setOf_abs_ne_zero f, hx, subset_rfl, 1, fun _ => f, {(fun _ => q, 0)},
    Finset.singleton_nonempty _, fun y hy _ => hy, fun y hy => ?_⟩
  beta_reduce
  rw [logAbs_eq_coe_log hy]
  simp [tropAffine, EReal.coe_mul]

theorem tropAffine_append {n m : ℕ} (f : Fin n → A) (f' : Fin m → A) (p : (Fin n → ℚ) × ℚ)
    (p' : (Fin m → ℚ) × ℚ) (y : Berk k A) :
    tropAffine (Fin.append f f') (Fin.append p.1 p'.1, p.2 + p'.2) y =
      tropAffine f p y + tropAffine f' p' y := by
  simp only [tropAffine, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  push_cast
  ring

theorem tropAffine_append_zero_right {n m : ℕ} (f : Fin n → A) (f' : Fin m → A)
    (p : (Fin n → ℚ) × ℚ) (y : Berk k A) :
    tropAffine (Fin.append f f') (Fin.append p.1 0, p.2) y = tropAffine f p y := by
  simp [tropAffine, Fin.sum_univ_add]

theorem tropAffine_zero_append {n m : ℕ} (f : Fin n → A) (f' : Fin m → A)
    (p : (Fin m → ℚ) × ℚ) (y : Berk k A) :
    tropAffine (Fin.append f f') (Fin.append 0 p.1, p.2) y = tropAffine f' p y := by
  simp [tropAffine, Fin.sum_univ_add]

theorem append_abs_ne_zero {n m : ℕ} {f : Fin n → A} {f' : Fin m → A} {y : Berk k A}
    (hf : ∀ i, y.val (f i) ≠ 0) (hf' : ∀ i, y.val (f' i) ≠ 0) (i : Fin (n + m)) :
    y.val (Fin.append f f' i) ≠ 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]; exact hf i
  · rw [Fin.append_right]; exact hf' i

/-- The maximum of two convex PL functions is convex PL. -/
theorem IsConvexPLOn.max (hu : IsConvexPLOn U u) (hv : IsConvexPLOn U v) :
    IsConvexPLOn U fun y => max (u y) (v y) := by
  classical
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, hW₁U, n₁, f₁, s₁, hs₁, hf₁, hu₁⟩ := hu x hx
  obtain ⟨W₂, hW₂, hxW₂, -, n₂, f₂, s₂, hs₂, hf₂, hv₂⟩ := hv x hx
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hxW₁, hxW₂⟩, Set.inter_subset_left.trans hW₁U, n₁ + n₂,
    Fin.append f₁ f₂, s₁.image (fun p => (Fin.append p.1 0, p.2)) ∪
      s₂.image (fun p => (Fin.append 0 p.1, p.2)),
    (hs₁.image _).mono Finset.subset_union_left,
    fun y hy => append_abs_ne_zero (hf₁ y hy.1) (hf₂ y hy.2), fun y hy => ?_⟩
  beta_reduce
  rw [hu₁ y hy.1, hv₂ y hy.2, Finset.sup'_union (hs₁.image _) (hs₂.image _), Finset.sup'_image,
    Finset.sup'_image]
  simp only [Function.comp_def, tropAffine_append_zero_right, tropAffine_zero_append]
  exact (EReal.coe_strictMono.monotone.map_max).symm

theorem sup'_product_add {ι κ : Type*} {s : Finset ι} {t : Finset κ} (hs : s.Nonempty)
    (ht : t.Nonempty) (F : ι → ℝ) (G : κ → ℝ) :
    (s ×ˢ t).sup' (hs.product ht) (fun pq => F pq.1 + G pq.2) = s.sup' hs F + t.sup' ht G := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun pq hpq =>
      add_le_add (Finset.le_sup' F (Finset.mem_product.1 hpq).1)
        (Finset.le_sup' G (Finset.mem_product.1 hpq).2)
  · obtain ⟨i, hi, hFi⟩ := Finset.exists_mem_eq_sup' hs F
    obtain ⟨j, hj, hGj⟩ := Finset.exists_mem_eq_sup' ht G
    rw [hFi, hGj]
    exact Finset.le_sup' (fun pq : ι × κ => F pq.1 + G pq.2)
      (show (i, j) ∈ s ×ˢ t from Finset.mem_product.2 ⟨hi, hj⟩)

/-- The sum of two convex PL functions is convex PL. -/
theorem IsConvexPLOn.add (hu : IsConvexPLOn U u) (hv : IsConvexPLOn U v) :
    IsConvexPLOn U fun y => u y + v y := by
  classical
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, hW₁U, n₁, f₁, s₁, hs₁, hf₁, hu₁⟩ := hu x hx
  obtain ⟨W₂, hW₂, hxW₂, -, n₂, f₂, s₂, hs₂, hf₂, hv₂⟩ := hv x hx
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hxW₁, hxW₂⟩, Set.inter_subset_left.trans hW₁U, n₁ + n₂,
    Fin.append f₁ f₂, (s₁ ×ˢ s₂).image (fun pq => (Fin.append pq.1.1 pq.2.1, pq.1.2 + pq.2.2)),
    (hs₁.product hs₂).image _,
    fun y hy => append_abs_ne_zero (hf₁ y hy.1) (hf₂ y hy.2), fun y hy => ?_⟩
  have key := sup'_product_add hs₁ hs₂ (fun p => tropAffine f₁ p y) (fun q => tropAffine f₂ q y)
  beta_reduce at key ⊢
  rw [hu₁ y hy.1, hv₂ y hy.2, Finset.sup'_image]
  simp only [Function.comp_def, tropAffine_append]
  rw [key, EReal.coe_add]

/-- A nonnegative rational multiple of a convex PL function is convex PL. -/
theorem IsConvexPLOn.smul (hu : IsConvexPLOn U u) {c : ℚ} (hc : 0 ≤ c) :
    IsConvexPLOn U fun y => ((c : ℝ) : EReal) * u y := by
  classical
  intro x hx
  obtain ⟨W, hW, hxW, hWU, n, f, s, hs, hf, hu'⟩ := hu x hx
  refine ⟨W, hW, hxW, hWU, n, f, s.image (fun p => (c • p.1, c * p.2)), hs.image _, hf,
    fun y hy => ?_⟩
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  beta_reduce
  rw [hu' y hy, Finset.sup'_image, ← EReal.coe_mul,
    Finset.apply_sup'_eq_sup'_comp hs (fun r : ℝ => (c : ℝ) * r)
      (fun _ _ => Monotone.map_max fun _ _ h => mul_le_mul_of_nonneg_left h hc')]
  congr 2
  funext p
  simp only [Function.comp_apply, tropAffine, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    Finset.mul_sum, mul_add, mul_assoc]

/-- Adding a rational constant preserves convex PL functions. -/
theorem IsConvexPLOn.add_const (hu : IsConvexPLOn U u) (q : ℚ) :
    IsConvexPLOn U fun y => u y + ((q : ℝ) : EReal) :=
  hu.add (isConvexPLOn_const hu.isOpen q)

/-- Adding `q log|f|`, `q ∈ ℚ`, preserves convex PL functions where `f` does not vanish. -/
theorem IsConvexPLOn.add_smul_logAbs (hu : IsConvexPLOn U u) (f : A) (q : ℚ) :
    IsConvexPLOn (U ∩ {y | y.val f ≠ 0}) fun y => u y + ((q : ℝ) : EReal) * logAbs f y := by
  have hO : IsOpen (U ∩ {y : Berk k A | y.val f ≠ 0}) :=
    hu.isOpen.inter (isOpen_setOf_abs_ne_zero f)
  exact (hu.mono hO Set.inter_subset_left).add
    ((isConvexPLOn_smul_logAbs f q).mono hO Set.inter_subset_right)

/-- **Gluing** (FHX Lemma 5.2(3) for convex PL functions). Let `U' ⊆ U` be open, `u` convex PL
on `U` and `v` convex PL on `U'`, such that the closure of `{x ∈ U' | v x > u x}`, intersected
with `U`, is contained in `U'`. Then the function equal to `max u v` on `U'` and to `u` on
`U \ U'` is convex PL on `U`. -/
theorem IsConvexPLOn.piecewise_max {U' : Set (Berk k A)} [∀ y, Decidable (y ∈ U')]
    (hU' : IsOpen U') (hU'U : U' ⊆ U) (hu : IsConvexPLOn U u) (hv : IsConvexPLOn U' v)
    (hcl : closure {y | y ∈ U' ∧ u y < v y} ∩ U ⊆ U') :
    IsConvexPLOn U (U'.piecewise (fun y => Max.max (u y) (v y)) u) := by
  refine isConvexPLOn_of_local fun x hx => ?_
  by_cases hxU' : x ∈ U'
  · exact ⟨U', hU', hxU', hU'U, ((hu.mono hU' hU'U).max hv).congr fun y hy =>
      (Set.piecewise_eq_of_mem U' (fun y => Max.max (u y) (v y)) u hy).symm⟩
  · have hxcl : x ∉ closure {y | y ∈ U' ∧ u y < v y} := fun h => hxU' (hcl ⟨h, hx⟩)
    have hO : IsOpen (U ∩ (closure {y | y ∈ U' ∧ u y < v y})ᶜ) :=
      hu.isOpen.inter isClosed_closure.isOpen_compl
    refine ⟨_, hO, ⟨hx, hxcl⟩, Set.inter_subset_left,
      (hu.mono hO Set.inter_subset_left).congr fun y hy => ?_⟩
    by_cases hyU' : y ∈ U'
    · rw [Set.piecewise_eq_of_mem _ _ _ hyU']
      have : ¬ (u y < v y) := fun h => hy.2 (subset_closure ⟨hyU', h⟩)
      exact (max_eq_left (not_lt.1 this)).symm
    · rw [Set.piecewise_eq_of_notMem _ _ _ hyU']

/-- A term `a log|f| + b` is convex PL where `f` does not vanish. -/
theorem isConvexPLOn_fsTerm (t : A × ℚ × ℚ) :
    IsConvexPLOn {y : Berk k A | y.val t.1 ≠ 0} (fsTerm t) :=
  (isConvexPLOn_smul_logAbs t.1 t.2.1).add_const t.2.2

theorem isOpen_setOf_forall_abs_ne_zero (s : Finset (A × ℚ × ℚ)) :
    IsOpen {y : Berk k A | ∀ t ∈ s, y.val t.1 ≠ 0} := by
  have e : {y : Berk k A | ∀ t ∈ s, y.val t.1 ≠ 0} = ⋂ t ∈ s, {y | y.val t.1 ≠ 0} := by
    ext; simp
  rw [e]
  exact isOpen_biInter_finset fun t _ => isOpen_setOf_abs_ne_zero t.1

theorem isConvexPLOn_max_sup_fsTerm (c : ℚ) (s : Finset (A × ℚ × ℚ)) :
    IsConvexPLOn {y : Berk k A | ∀ t ∈ s, y.val t.1 ≠ 0}
      fun y => max ((c : ℝ) : EReal) (s.sup fun t => fsTerm t y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (isConvexPLOn_const (isOpen_setOf_forall_abs_ne_zero ∅) c).congr fun y _ => by simp
  | insert t s ht ih =>
    have hO := isOpen_setOf_forall_abs_ne_zero (k := k) (insert t s)
    have h1 : IsConvexPLOn {y : Berk k A | ∀ t' ∈ insert t s, y.val t'.1 ≠ 0} (fsTerm t) :=
      (isConvexPLOn_fsTerm t).mono hO fun y hy => hy t (Finset.mem_insert_self t s)
    have h2 := ih.mono hO fun y hy t' ht' => hy t' (Finset.mem_insert_of_mem ht')
    refine (h1.max h2).congr fun y _ => ?_
    simp only [Finset.sup_insert]
    exact max_left_comm _ _ _

theorem max_sup_eq_max_sup_filter {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (F : ι → EReal) (c : EReal) (h : ∀ i ∈ s, ¬ p i → F i ≤ c) :
    max c (s.sup F) = max c ((s.filter p).sup F) := by
  apply le_antisymm
  · refine max_le (le_max_left _ _) (Finset.sup_le fun i hi => ?_)
    by_cases hp : p i
    · exact (Finset.le_sup (Finset.mem_filter.2 ⟨hi, hp⟩)).trans (le_max_right _ _)
    · exact (h i hi hp).trans (le_max_left _ _)
  · exact max_le_max le_rfl (Finset.sup_mono (Finset.filter_subset _ _))

/-- **FS functions are convex PL** ("the argument following (5.2)" in FHX): near a point `x`, the
terms whose function vanishes at `x` are `-∞` at `x`, hence below the constant term nearby, and may
be omitted; the remaining functions do not vanish near `x`. -/
theorem FSData.isConvexPLOn_univ (g : FSData k A) : IsConvexPLOn Set.univ g.eval := by
  classical
  refine isConvexPLOn_of_local fun x _ => ?_
  let V : Set (Berk k A) := {y | ∀ t ∈ g.terms.filter (fun t => x.val t.1 ≠ 0), y.val t.1 ≠ 0} ∩
    ⋂ t ∈ g.terms.filter (fun t => ¬ x.val t.1 ≠ 0), {y | fsTerm t y < ((g.const : ℝ) : EReal)}
  have hV : IsOpen V := (isOpen_setOf_forall_abs_ne_zero _).inter
    (isOpen_biInter_finset fun t _ => isOpen_lt (continuous_fsTerm t) continuous_const)
  have hxV : x ∈ V := by
    refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, Set.mem_iInter₂.2 fun t ht => ?_⟩
    have ht' := Finset.mem_filter.1 ht
    show fsTerm t x < _
    rw [fsTerm_eq_bot (g.pos t ht'.1) (not_not.1 ht'.2)]
    exact EReal.bot_lt_coe _
  refine ⟨V, hV, hxV, Set.subset_univ _,
    ((isConvexPLOn_max_sup_fsTerm g.const _).mono hV Set.inter_subset_left).congr
      fun y hy => ?_⟩
  rw [FSData.eval_def, max_sup_eq_max_sup_filter g.terms (fun t => x.val t.1 ≠ 0)]
  intro t ht hxt
  exact (Set.mem_iInter₂.1 hy.2 t (Finset.mem_filter.2 ⟨ht, hxt⟩)).le

theorem FSData.isConvexPLOn (g : FSData k A) (hU : IsOpen U) : IsConvexPLOn U g.eval :=
  g.isConvexPLOn_univ.mono hU (Set.subset_univ _)

theorem IsFS.isConvexPLOn (hu : IsFS u) (hU : IsOpen U) : IsConvexPLOn U u := by
  obtain ⟨g, hg⟩ := hu
  exact (g.isConvexPLOn hU).congr fun y _ => (hg y).symm

end ConvexPL

/-! ### Growth estimates (FHX Lemma 5.8) -/

/-- `a log|f| + b ≤ a R + b` when `|f| ≤ exp R` and `a > 0`. -/
theorem fsTerm_le_of_abs_le_exp {t : A × ℚ × ℚ} (ht : 0 < t.2.1) {x : Berk k A} {R : ℝ}
    (h : (x.val t.1 : ℝ) ≤ Real.exp R) :
    fsTerm t x ≤ (((t.2.1 : ℝ) * R + t.2.2 : ℝ) : EReal) := by
  rw [fsTerm_def, EReal.coe_add, EReal.coe_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (logAbs_le_coe_of_le_exp h)
    (by exact_mod_cast ht.le)) le_rfl

/-- **Integral equation estimate** (proof of FHX Lemma 5.8(2)). If `f` is a root of a monic
polynomial `p` with coefficients `bᵢ` (mapped by `ψ`), and `v(bᵢ) ≤ r ^ (m - i)` for all `i < m`
where `m = deg p`, then `v(f) ≤ r`; that is, `log|f| ≤ max_{i<m} log|bᵢ| / (m - i)`. -/
theorem valuation_le_of_monic_eval₂_eq_zero {R : Type*} [CommRing R] (v : Valuation A ℝ≥0)
    (ψ : R →+* A) {p : Polynomial R} (hp : p.Monic) {f : A} (hf : p.eval₂ ψ f = 0) {r : ℝ≥0}
    (hr : ∀ i < p.natDegree, v (ψ (p.coeff i)) ≤ r ^ (p.natDegree - i)) : v f ≤ r := by
  by_contra hlt
  rw [not_le] at hlt
  have hvf : 0 < v f := lt_of_le_of_lt zero_le hlt
  have heq : f ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i := by
    have h := hf
    rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at h
    exact eq_neg_of_add_eq_zero_left h
  have hlt' : v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) < v f ^ p.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hvf.ne') fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [v.map_mul, v.map_pow]
    calc v (ψ (p.coeff i)) * v f ^ i ≤ r ^ (p.natDegree - i) * v f ^ i :=
          mul_le_mul_of_nonneg_right (hr i hi') zero_le
      _ < v f ^ (p.natDegree - i) * v f ^ i :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hlt zero_le (by omega)) (pow_pos hvf _)
      _ = v f ^ p.natDegree := by rw [← pow_add, Nat.sub_add_cancel hi'.le]
  have h2 : v (f ^ p.natDegree) = v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) := by
    rw [heq, Valuation.map_neg]
  rw [v.map_pow] at h2
  rw [← h2] at hlt'
  exact lt_irrefl _ hlt'

namespace FSData

/-- The generators occurring in `h` satisfy `|f| ≤ exp((h - b) / a)` for their term `(f, a, b)`. -/
theorem abs_le_exp_of_mem (h : FSData k A) {t : A × ℚ × ℚ} (ht : t ∈ h.terms) (y : Berk k A) :
    (y.val t.1 : ℝ) ≤ Real.exp ((h.evalReal y - t.2.2) / t.2.1) := by
  by_cases hy : y.val t.1 = 0
  · rw [hy, NNReal.coe_zero]; exact (Real.exp_pos _).le
  have hle := h.fsTerm_le_eval ht y
  rw [fsTerm_eq_coe hy, ← h.coe_evalReal, EReal.coe_le_coe_iff] at hle
  have ha : (0 : ℝ) < t.2.1 := by exact_mod_cast h.pos t ht
  have hpos : (0 : ℝ) < y.val t.1 := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hy
  rw [← Real.log_le_iff_le_exp hpos, le_div_iff₀ ha]
  linarith

/-- Uniform bound for the generators occurring in `h`: `|f| ≤ exp(K (h - b₀) + K')`. -/
theorem exists_abs_le_exp_of_mem (h : FSData k A) : ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
    ∀ t ∈ h.terms, ∀ y : Berk k A,
      (y.val t.1 : ℝ) ≤ Real.exp (K * (h.evalReal y - h.const) + K') := by
  have hpos : ∀ t ∈ h.terms, (0 : ℝ) < t.2.1 := fun t ht => by exact_mod_cast h.pos t ht
  refine ⟨∑ t ∈ h.terms, 1 / (t.2.1 : ℝ), ∑ t ∈ h.terms, |(h.const : ℝ) - t.2.2| / t.2.1,
    Finset.sum_nonneg fun t ht => (one_div_pos.2 (hpos t ht)).le,
    Finset.sum_nonneg fun t ht => div_nonneg (abs_nonneg _) (hpos t ht).le, fun t ht y => ?_⟩
  refine (h.abs_le_exp_of_mem ht y).trans (Real.exp_le_exp.2 ?_)
  have ha := hpos t ht
  have hN : 0 ≤ h.evalReal y - h.const := sub_nonneg.2 (h.const_le_evalReal y)
  have h1 : 1 / (t.2.1 : ℝ) ≤ ∑ t ∈ h.terms, 1 / (t.2.1 : ℝ) :=
    Finset.single_le_sum (f := fun t => 1 / (t.2.1 : ℝ))
      (fun t ht => (one_div_pos.2 (hpos t ht)).le) ht
  have h2 : |(h.const : ℝ) - t.2.2| / t.2.1 ≤ ∑ t ∈ h.terms, |(h.const : ℝ) - t.2.2| / t.2.1 :=
    Finset.single_le_sum (f := fun t => |(h.const : ℝ) - t.2.2| / t.2.1)
      (fun t ht => div_nonneg (abs_nonneg _) (hpos t ht).le) ht
  have h3 : ((h.const : ℝ) - t.2.2) / t.2.1 ≤ |(h.const : ℝ) - t.2.2| / t.2.1 :=
    div_le_div_of_nonneg_right (le_abs_self _) ha.le
  calc (h.evalReal y - t.2.2) / t.2.1
      = 1 / (t.2.1 : ℝ) * (h.evalReal y - h.const) + ((h.const : ℝ) - t.2.2) / t.2.1 := by
        field_simp; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right h1 hN) (h3.trans h2)

/-- Sublevel sets of FS functions are compact, since they lie in closed polydiscs (FHX, remark
after Definition 5.7). -/
theorem isCompact_setOf_eval_le (g : FSData k A) (c : ℝ) :
    IsCompact {x : Berk k A | g.eval x ≤ c} := by
  refine isCompact_of_isClosed_of_forall_abs_le g.gen
    (isClosed_le g.continuous_eval continuous_const)
    (Real.exp (∑ t ∈ g.terms, |c - t.2.2| / t.2.1)).toNNReal fun x hx s hs => ?_
  obtain ⟨t, ht, rfl⟩ := hs
  have hpos : (0 : ℝ) < t.2.1 := by exact_mod_cast g.pos t ht
  have hE : g.evalReal x ≤ c := by
    rw [← EReal.coe_le_coe_iff, coe_evalReal]; exact hx
  rw [Real.le_toNNReal_iff_coe_le (Real.exp_pos _).le]
  refine (g.abs_le_exp_of_mem ht x).trans (Real.exp_le_exp.2 ?_)
  calc (g.evalReal x - t.2.2) / t.2.1 ≤ |c - t.2.2| / t.2.1 :=
        div_le_div_of_nonneg_right ((sub_le_sub_right hE _).trans (le_abs_self _)) hpos.le
    _ ≤ ∑ t ∈ g.terms, |c - t.2.2| / t.2.1 :=
        Finset.single_le_sum (f := fun t => |c - (t.2.2 : ℝ)| / t.2.1)
          (fun t ht => div_nonneg (abs_nonneg _) (by exact_mod_cast (g.pos t ht).le)) ht

/-- **Polynomial estimate** in terms of an FS function (proof of FHX Lemma 5.8(1)): for finitely
many `f ∈ A` there are `K, K' ≥ 0` with `|f| ≤ exp(K (h - b₀) + K')`, since
`log|f| ≤ d max{0, log|z_l|}` for the generators `z_l` occurring in `h`. -/
theorem exists_abs_le_exp (h : FSData k A) (F : Finset A) : ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
    ∀ f ∈ F, ∀ y : Berk k A, (y.val f : ℝ) ≤ Real.exp (K * (h.evalReal y - h.const) + K') := by
  obtain ⟨K₀, K₀', hK₀, hK₀', hgen⟩ := h.exists_abs_le_exp_of_mem
  choose d hd using fun f => exists_abs_le_pow_of_adjoin_eq_top h.gen f
  refine ⟨(∑ f ∈ F, d f : ℕ) * K₀, (∑ f ∈ F, d f : ℕ) * K₀', by positivity, by positivity,
    fun f hf y => ?_⟩
  have hR : 0 ≤ K₀ * (h.evalReal y - h.const) + K₀' :=
    add_nonneg (mul_nonneg hK₀ (sub_nonneg.2 (h.const_le_evalReal y))) hK₀'
  set R := K₀ * (h.evalReal y - h.const) + K₀' with hRdef
  have hM : (1 : ℝ≥0) ≤ (Real.exp R).toNNReal := by
    rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal (Real.one_le_exp hR)
  have h1 := hd f y _ hM (by
    rintro _ ⟨t, ht, rfl⟩
    exact (Real.le_toNNReal_iff_coe_le (Real.exp_pos R).le).2 (hgen t ht y))
  have h2 : y.val f ≤ (Real.exp R).toNNReal ^ (∑ f ∈ F, d f) :=
    h1.trans (pow_le_pow_right₀ hM (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf))
  calc (y.val f : ℝ) ≤ (((Real.exp R).toNNReal ^ (∑ f ∈ F, d f) : ℝ≥0) : ℝ) := by
        exact_mod_cast h2
    _ = Real.exp R ^ (∑ f ∈ F, d f) := by
        rw [NNReal.coe_pow, Real.coe_toNNReal _ (Real.exp_pos R).le]
    _ = _ := by
        rw [← Real.exp_nat_mul]; congr 1; rw [hRdef]; ring

/-- If all the functions occurring in `g` satisfy `|f|_x ≤ exp R` with `R ≥ 0`, then
`g(x) ≤ (∑ aᵢ) R + ∑ |bᵢ| + |b₀|`. -/
theorem eval_le_of_abs_le_exp (g : FSData k A) {x : Berk k A} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ t ∈ g.terms, (x.val t.1 : ℝ) ≤ Real.exp R) :
    g.eval x ≤ (((∑ t ∈ g.terms, (t.2.1 : ℝ)) * R +
      (∑ t ∈ g.terms, |(t.2.2 : ℝ)| + |(g.const : ℝ)|) : ℝ) : EReal) := by
  have hα0 : 0 ≤ ∑ t ∈ g.terms, (t.2.1 : ℝ) :=
    Finset.sum_nonneg fun t ht => by exact_mod_cast (g.pos t ht).le
  have hβ0 : 0 ≤ ∑ t ∈ g.terms, |(t.2.2 : ℝ)| := Finset.sum_nonneg fun t _ => abs_nonneg _
  refine max_le ?_ (Finset.sup_le fun t ht => ?_)
  · rw [EReal.coe_le_coe_iff]
    have := le_abs_self (g.const : ℝ)
    nlinarith [mul_nonneg hα0 hR]
  · refine (fsTerm_le_of_abs_le_exp (g.pos t ht) (h t ht)).trans ?_
    rw [EReal.coe_le_coe_iff]
    have hα : (t.2.1 : ℝ) ≤ ∑ t ∈ g.terms, (t.2.1 : ℝ) :=
      Finset.single_le_sum (f := fun t => (t.2.1 : ℝ))
        (fun t ht => by exact_mod_cast (g.pos t ht).le) ht
    have hβ : |(t.2.2 : ℝ)| ≤ ∑ t ∈ g.terms, |(t.2.2 : ℝ)| :=
      Finset.single_le_sum (f := fun t => |(t.2.2 : ℝ)|) (fun t _ => abs_nonneg _) ht
    nlinarith [mul_le_mul_of_nonneg_right hα hR, le_abs_self (t.2.2 : ℝ),
      abs_nonneg (g.const : ℝ)]

/-- **FHX Lemma 5.8(1)** (`lem:growth`). For a `k`-algebra map `φ : A → B`, FS data `g` on
`Spec A` and `g'` on `Spec B`, there are constants `C ≥ 0`, `C'` with
`g ∘ φ^an ≤ C g' + C'`. -/
theorem exists_eval_comap_le {B : Type*} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (g : FSData k A) (g' : FSData k B) :
    ∃ C C' : ℝ, 0 ≤ C ∧
      ∀ x : Berk k B, g.eval (comap φ x) ≤ (C : EReal) * g'.eval x + (C' : EReal) := by
  classical
  obtain ⟨K, K', hK, hK', hb⟩ := g'.exists_abs_le_exp (g.terms.image fun t => φ t.1)
  have hα0 : 0 ≤ ∑ t ∈ g.terms, (t.2.1 : ℝ) :=
    Finset.sum_nonneg fun t ht => by exact_mod_cast (g.pos t ht).le
  refine ⟨(∑ t ∈ g.terms, (t.2.1 : ℝ)) * K, (∑ t ∈ g.terms, (t.2.1 : ℝ)) * K' +
    (∑ t ∈ g.terms, |(t.2.2 : ℝ)| + |(g.const : ℝ)|) -
      (∑ t ∈ g.terms, (t.2.1 : ℝ)) * K * g'.const, mul_nonneg hα0 hK, fun x => ?_⟩
  have hR : 0 ≤ K * (g'.evalReal x - g'.const) + K' :=
    add_nonneg (mul_nonneg hK (sub_nonneg.2 (g'.const_le_evalReal x))) hK'
  refine (g.eval_le_of_abs_le_exp hR fun t ht => ?_).trans (le_of_eq ?_)
  · exact hb _ (Finset.mem_image_of_mem _ ht) x
  · rw [← g'.coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring

/-- FHX Lemma 5.8(1) for the identity: any two FS functions satisfy `g ≤ C g' + C'`. -/
theorem exists_eval_le (g g' : FSData k A) :
    ∃ C C' : ℝ, 0 ≤ C ∧ ∀ x : Berk k A, g.eval x ≤ (C : EReal) * g'.eval x + (C' : EReal) :=
  exists_eval_comap_le (AlgHom.id k A) g g'

/-- **FHX Lemma 5.8(2)** (`lem:growth`). Let `φ : B → A` be an integral `k`-algebra map (a finite
morphism `Spec A → Spec B`). For FS data `g` on `Spec A` and `h` on `Spec B` there are constants
`C ≥ 0`, `C'` with `g ≤ C h ∘ φ^an + C'`. -/
theorem exists_eval_le_comap_of_isIntegral {B : Type*} [CommRing B] [Algebra k B]
    (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral) (g : FSData k A) (h : FSData k B) :
    ∃ C C' : ℝ, 0 ≤ C ∧
      ∀ x : Berk k A, g.eval x ≤ (C : EReal) * h.eval (comap φ x) + (C' : EReal) := by
  classical
  choose p hp using fun a : A => hφ a
  obtain ⟨K, K', hK, hK', hb⟩ := h.exists_abs_le_exp
    (g.terms.biUnion fun t => (Finset.range (p t.1).natDegree).image fun i => (p t.1).coeff i)
  have hα0 : 0 ≤ ∑ t ∈ g.terms, (t.2.1 : ℝ) :=
    Finset.sum_nonneg fun t ht => by exact_mod_cast (g.pos t ht).le
  refine ⟨(∑ t ∈ g.terms, (t.2.1 : ℝ)) * K, (∑ t ∈ g.terms, (t.2.1 : ℝ)) * K' +
    (∑ t ∈ g.terms, |(t.2.2 : ℝ)| + |(g.const : ℝ)|) -
      (∑ t ∈ g.terms, (t.2.1 : ℝ)) * K * h.const, mul_nonneg hα0 hK, fun x => ?_⟩
  have hR : 0 ≤ K * (h.evalReal (comap φ x) - h.const) + K' :=
    add_nonneg (mul_nonneg hK (sub_nonneg.2 (h.const_le_evalReal _))) hK'
  set R := K * (h.evalReal (comap φ x) - h.const) + K' with hRdef
  have hM : (1 : ℝ≥0) ≤ (Real.exp R).toNNReal := by
    rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal (Real.one_le_exp hR)
  refine (g.eval_le_of_abs_le_exp hR fun t ht => ?_).trans (le_of_eq ?_)
  · have key := valuation_le_of_monic_eval₂_eq_zero x.val (φ : B →+* A) (hp t.1).1 (hp t.1).2
      (r := (Real.exp R).toNNReal) fun i hi => by
        have h1 : ((comap φ x).val ((p t.1).coeff i) : ℝ) ≤ Real.exp R :=
          hb _ (Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image_of_mem _ (Finset.mem_range.2 hi)⟩) _
        exact ((Real.le_toNNReal_iff_coe_le (Real.exp_pos R).le).2 h1).trans
          (le_self_pow₀ hM (by omega))
    calc (x.val t.1 : ℝ) ≤ ((Real.exp R).toNNReal : ℝ) := by exact_mod_cast key
      _ = Real.exp R := Real.coe_toNNReal _ (Real.exp_pos R).le
  · rw [← h.coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    rw [hRdef]
    ring

/-- FHX Lemma 5.8(2) for an integral algebra `A` over `B`. -/
theorem exists_eval_le_comap_of_isIntegral' {B : Type*} [CommRing B] [Algebra k B] [Algebra B A]
    [IsScalarTower k B A] [Algebra.IsIntegral B A] (g : FSData k A) (h : FSData k B) :
    ∃ C C' : ℝ, 0 ≤ C ∧ ∀ x : Berk k A,
      g.eval x ≤ (C : EReal) * h.eval (comap (IsScalarTower.toAlgHom k B A) x) + (C' : EReal) :=
  exists_eval_le_comap_of_isIntegral _
    (fun a => by rw [IsScalarTower.coe_toAlgHom]; exact Algebra.IsIntegral.isIntegral a) g h

/-- An FS function has logarithmic growth. -/
theorem hasLogGrowth (g : FSData k A) : HasLogGrowth g.eval :=
  ⟨g, 0, fun x => by simp⟩

end FSData

/-! ### Functions of logarithmic growth -/

namespace HasLogGrowth

variable {u v : Berk k A → EReal}

theorem mono (hv : HasLogGrowth v) (huv : ∀ x, u x ≤ v x) : HasLogGrowth u := by
  obtain ⟨g, C, hg⟩ := hv
  exact ⟨g, C, fun x => (huv x).trans (hg x)⟩

theorem sup (hu : HasLogGrowth u) (hv : HasLogGrowth v) :
    HasLogGrowth fun x => max (u x) (v x) := by
  obtain ⟨g, C, hg⟩ := hu
  obtain ⟨g', C', hg'⟩ := hv
  refine ⟨g.sup g', max C C', fun x => max_le ?_ ?_⟩
  · exact (hg x).trans (add_le_add (by rw [FSData.eval_sup]; exact le_max_left _ _)
      (EReal.coe_le_coe_iff.2 (le_max_left _ _)))
  · exact (hg' x).trans (add_le_add (by rw [FSData.eval_sup]; exact le_max_right _ _)
      (EReal.coe_le_coe_iff.2 (le_max_right _ _)))

theorem add (hu : HasLogGrowth u) (hv : HasLogGrowth v) : HasLogGrowth fun x => u x + v x := by
  obtain ⟨g, C, hg⟩ := hu
  obtain ⟨g', C', hg'⟩ := hv
  refine ⟨g.add g', C + C', fun x => ?_⟩
  rw [FSData.eval_add, EReal.coe_add, add_add_add_comm]
  exact add_le_add (hg x) (hg' x)

theorem add_const (hu : HasLogGrowth u) (c : ℝ) : HasLogGrowth fun x => u x + (c : EReal) := by
  obtain ⟨g, C, hg⟩ := hu
  refine ⟨g, C + c, fun x => ?_⟩
  rw [EReal.coe_add, ← add_assoc]
  exact add_le_add (hg x) le_rfl

/-- A nonnegative (real) multiple of a function of logarithmic growth has logarithmic growth. -/
theorem smul (hu : HasLogGrowth u) {c : ℝ} (hc : 0 ≤ c) :
    HasLogGrowth fun x => (c : EReal) * u x := by
  obtain ⟨g, C, hg⟩ := hu
  have hq : (0 : ℚ) < (⌈c⌉₊ : ℚ) + 1 := by positivity
  have hcq : c ≤ (((⌈c⌉₊ : ℚ) + 1 : ℚ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil c]
  refine ⟨g.smul _ hq, c * C - ((((⌈c⌉₊ : ℚ) + 1 : ℚ) : ℝ) - c) * g.const, fun x => ?_⟩
  rw [FSData.eval_smul, ← g.coe_evalReal]
  have h1 : u x ≤ ((g.evalReal x + C : ℝ) : EReal) := by
    rw [EReal.coe_add, g.coe_evalReal]; exact hg x
  have h0 := g.const_le_evalReal x
  calc (c : EReal) * u x ≤ (c : EReal) * ((g.evalReal x + C : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h1 (by exact_mod_cast hc)
    _ ≤ (((((⌈c⌉₊ : ℚ) + 1 : ℚ) : ℝ) * g.evalReal x +
          (c * C - ((((⌈c⌉₊ : ℚ) + 1 : ℚ) : ℝ) - c) * g.const) : ℝ) : EReal) := by
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
        nlinarith [mul_nonneg (sub_nonneg.2 hcq) (sub_nonneg.2 h0)]
    _ = _ := by rw [EReal.coe_add, EReal.coe_mul]

/-- Pullback along a morphism of affine schemes of finite type preserves logarithmic growth
(FHX, remark after Lemma 5.8). -/
theorem comp_comap {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (φ : A →ₐ[k] B) (hu : HasLogGrowth u) : HasLogGrowth fun x : Berk k B => u (comap φ x) := by
  obtain ⟨g, C, hg⟩ := hu
  obtain ⟨C₁, C₂, -, hle⟩ := g.exists_eval_comap_le φ (FSData.std k B)
  have hq : (0 : ℚ) < (⌈C₁⌉₊ : ℚ) + 1 := by positivity
  have hCq : C₁ ≤ (((⌈C₁⌉₊ : ℚ) + 1 : ℚ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil C₁]
  refine ⟨(FSData.std k B).smul _ hq, C₂ + C, fun x => ?_⟩
  rw [FSData.eval_smul, ← (FSData.std k B).coe_evalReal]
  have h0 : 0 ≤ (FSData.std k B).evalReal x := by
    have := FSData.eval_std_nonneg k B x
    rw [← FSData.coe_evalReal] at this
    exact_mod_cast this
  have h1 := hle x
  rw [← (FSData.std k B).coe_evalReal, ← g.coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h1
  calc u (comap φ x) ≤ g.eval (comap φ x) + C := hg _
    _ = ((g.evalReal (comap φ x) + C : ℝ) : EReal) := by rw [EReal.coe_add, FSData.coe_evalReal]
    _ ≤ (((((⌈C₁⌉₊ : ℚ) + 1 : ℚ) : ℝ) * (FSData.std k B).evalReal x + (C₂ + C) : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        nlinarith [mul_le_mul_of_nonneg_right hCq h0]
    _ = _ := by rw [EReal.coe_add, EReal.coe_mul]

end HasLogGrowth

theorem IsFS.hasLogGrowth {u : Berk k A → EReal} (hu : IsFS u) : HasLogGrowth u := by
  obtain ⟨g, hg⟩ := hu
  exact g.hasLogGrowth.mono fun x => (hg x).le

/-- Regularizable functions have logarithmic growth: `u ≤ g₀`. -/
theorem IsRegularizable.hasLogGrowth {u : Berk k A → EReal} (hu : IsRegularizable u) :
    HasLogGrowth u := by
  obtain ⟨-, g, -, hg⟩ := hu
  exact (g 0).hasLogGrowth.mono fun x => (hg x).trans_le (iInf_le _ 0)

/-- Constants have logarithmic growth (for `A` of finite type). -/
theorem hasLogGrowth_const [Algebra.FiniteType k A] (c : ℝ) :
    HasLogGrowth fun _ : Berk k A => (c : EReal) :=
  ⟨FSData.std k A, c, fun x => by
    simpa using add_le_add (FSData.eval_std_nonneg k A x) (le_refl (c : EReal))⟩

/-- `log|f|` has logarithmic growth (for `A` of finite type). -/
theorem hasLogGrowth_logAbs [Algebra.FiniteType k A] (f : A) :
    HasLogGrowth (logAbs f : Berk k A → EReal) := by
  refine ⟨(FSData.std k A).addTerms {(f, 1, 0)} (by simp), 0, fun x => ?_⟩
  rw [FSData.eval_addTerms, Finset.sup_singleton, EReal.coe_zero, add_zero]
  refine le_trans (le_of_eq ?_) (le_max_right _ _)
  simp [fsTerm_def]

end EnvelopeProperty
