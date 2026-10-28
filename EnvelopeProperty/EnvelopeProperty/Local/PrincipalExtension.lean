/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Regularizable
import EnvelopeProperty.Local.Hull

/-!
# Extension of regularizable functions from principal opens

Let `Y = Spec A` be a normal affine variety over the trivially valued field `k`, `0 ≠ f ∈ A` and
`Y_f = Spec A_f` the principal open subset, whose analytification is the open subset
`{|f| ≠ 0}` of `Y^an` (`EnvelopeProperty.Berkovich.Localization`). This file proves
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.12
(`lem:principal-extension`) and Lemma 5.17 (`lem:principal-hull`).

* `awayExtend f v`: the extension of a function `v` on `Y_f^an` to `Y^an` by `-∞` on `{|f| = 0}`.
* `IsConvexPLOn.awayExtend`: convex PL functions on an open subset of `Y_f^an` are convex PL on its
  image in `Y^an`: an element of `A_f` is `a / f^n`, and `log|a / f^n| = log|a| - n log|f|`
  with `a`, `f` nonvanishing.
* `FSData.awayEps`: for `g ∈ FS(Y)` and `ε ∈ ℚ_{>0}`, the FS function
  `g_ε = max{g, ε log|1/f|} = max{g, -ε log|f|}` on `Y_f`.
* `IsRegularizable.awayExtend_add` (**FHX Lemma 5.12**): if `u ∈ ℛ(Y_f)` and `u ≤ g + C` for
  some `g ∈ FS(Y)`, then for every `c ∈ ℚ_{>0}` the extension of `u + c log|f|` by `-∞` lies in
  `ℛ(Y)`. With `ε = c/3`, the imported growth control (FHX Lemma 5.11(5)) gives `u_j ∈ FS(Y_f)`
  decreasing to `u` with `u_j ≤ 2 g_ε + C_j`; then
  `u_j + c log|f| ≤ max{2g + c log|f|, (c - 2ε) log|f|} + C_j → -∞` near `{|f| = 0}`, so the
  functions `v_j = max{u_j + c log|f|, -j}`, extended by `-j`, are convex PL on `Y^an`, have
  logarithmic growth, hence are regularizable (FHX Lemma 5.11(6)), and decrease to the
  extension; conclude by FHX Lemma 5.11(2) (`IsRegularizable.of_antitone`).
* `le_iSup_of_mem_hull_awayExtend` (**FHX Lemma 5.17**): for `v` as above, a compact
  `K ⊆ Y^an` and `x ∈ K̂ ∩ Y_f^an`, `v(x) ≤ sup_K v`: apply the hull inequality to the
  extensions of `v + c log|f|` and let `c → 0`. `le_iSup_of_awayComap_mem_hull` is the same
  statement for `K ⊆ Y_f^an`.

Auxiliary results: `isConvexPLOn_univ_max_awayExtend` (gluing across `{|f| = 0}`),
`IsConvexPLOn.isRegularizable` (FHX Lemma 5.11(6) for a globally convex PL function) and
`isIntegrallyClosed_localizationAway`.

The source states Lemma 5.17 for `K ⊆ Y_f^an`; the extension by `-∞` makes this hypothesis
unnecessary.
-/

open scoped NNReal ENNReal Topology

open Filter Topology

noncomputable section

namespace EnvelopeProperty

open Berk

section general

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Extension by `-∞` -/

section awayExtend

variable (f : A)

open Classical in
/-- The extension of a function `v` on `(Y_f)^an` to `Y^an` by `-∞` on `{|f| = 0}`. -/
def awayExtend (v : Berk k (Localization.Away f) → EReal) (x : Berk k A) : EReal :=
  if h : x.val f ≠ 0 then v (awayLift f x h) else ⊥

variable (v : Berk k (Localization.Away f) → EReal)

theorem awayExtend_of_ne_zero {x : Berk k A} (h : x.val f ≠ 0) :
    awayExtend f v x = v (awayLift f x h) := by
  rw [awayExtend, dif_pos h]

@[simp]
theorem awayExtend_of_eq_zero {x : Berk k A} (h : x.val f = 0) : awayExtend f v x = ⊥ := by
  rw [awayExtend, dif_neg (not_not.2 h)]

@[simp]
theorem awayExtend_awayComap (y : Berk k (Localization.Away f)) :
    awayExtend f v (awayComap f y) = v y := by
  rw [awayExtend_of_ne_zero f v (awayComap_val_ne_zero f y), awayLift_awayComap]

theorem awayExtend_le_iff {x : Berk k A} {c : EReal} :
    awayExtend f v x ≤ c ↔ ∀ h : x.val f ≠ 0, v (awayLift f x h) ≤ c := by
  by_cases h : x.val f = 0
  · simp [h]
  · simp [awayExtend_of_ne_zero f v h, h]

end awayExtend

/-! ### Transport of convex PL functions -/

theorem ereal_coe_max (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

/-- `log |f|` is the real number `log |f|_x` on `(Y_f)^an`. -/
theorem logAbs_awayComap_eq_coe (f : A) (y : Berk k (Localization.Away f)) :
    logAbs f (awayComap f y) = ((Real.log ((awayComap f y).val f : ℝ) : ℝ) : EReal) :=
  logAbs_eq_coe_log (awayComap_val_ne_zero f y)

/-- `log |a / f ^ n| = log |a| - n log |f|` as real numbers, where `a`, `f` do not vanish. -/
theorem log_val_mk'_awayComap {f : A} (y : Berk k (Localization.Away f)) (a : A) (n : ℕ)
    (ha : (awayComap f y).val a ≠ 0) :
    Real.log (y.val (IsLocalization.mk' (Localization.Away f) a
        (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) : ℝ) =
      Real.log ((awayComap f y).val a : ℝ) - n * Real.log ((awayComap f y).val f : ℝ) := by
  have hf := awayComap_val_ne_zero f y
  rw [awayComap_val_mk', NNReal.coe_div, NNReal.coe_pow,
    Real.log_div (by exact_mod_cast ha) (pow_ne_zero n (by exact_mod_cast hf)), Real.log_pow]

/-- **Transport of convex PL functions** along `(Y_f)^an ↪ Y^an`. If `v` is convex PL on `V` and
`w` agrees with `v` on `V` (through `(Y_f)^an → Y^an`), then `w` is convex PL on the image of `V`:
an element of `A_f` is `a / f ^ n`, and `log |a / f ^ n| = log |a| - n log |f|` with `a` and `f`
nonvanishing. -/
theorem IsConvexPLOn.awayComap_image {f : A} {V : Set (Berk k (Localization.Away f))}
    {v : Berk k (Localization.Away f) → EReal} (hv : IsConvexPLOn V v) {w : Berk k A → EReal}
    (hw : ∀ y ∈ V, w (awayComap f y) = v y) : IsConvexPLOn (awayComap f '' V) w := by
  classical
  rintro _ ⟨y, hyV, rfl⟩
  obtain ⟨W, hW, hyW, hWV, n, F, s, hs, hF, hvW⟩ := hv y hyV
  choose a m hm using fun i => Berk.Away.exists_eq_mk' (Localization.Away f) f (F i)
  have hval : ∀ y' : Berk k (Localization.Away f), ∀ i, y'.val (F i) =
      (awayComap f y').val (a i) / (awayComap f y').val f ^ m i := fun y' i => by
    rw [hm i, awayComap_val_mk']
  have ha : ∀ y' ∈ W, ∀ i, (awayComap f y').val (a i) ≠ 0 := fun y' hy' i h => by
    have := hF y' hy' i
    rw [hval y' i, h, zero_div] at this
    exact this rfl
  have hlog : ∀ y' ∈ W, ∀ i, Real.log (y'.val (F i) : ℝ) =
      Real.log ((awayComap f y').val (a i) : ℝ) -
        m i * Real.log ((awayComap f y').val f : ℝ) := fun y' hy' i => by
    rw [hm i]
    exact log_val_mk'_awayComap y' (a i) (m i) (ha y' hy' i)
  let φ : (Fin n → ℚ) × ℚ → (Fin (n + 1) → ℚ) × ℚ :=
    fun p => (Fin.cons (-(∑ i, p.1 i * (m i : ℚ))) p.1, p.2)
  refine ⟨awayComap f '' W, (isOpenEmbedding_awayComap f).isOpenMap W hW, ⟨y, hyW, rfl⟩,
    Set.image_mono hWV, n + 1, Fin.cons f a, s.image φ, hs.image φ, ?_, ?_⟩
  · rintro _ ⟨y', hy', rfl⟩ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using awayComap_val_ne_zero f y'
    · simpa using ha y' hy' i
  · rintro _ ⟨y', hy', rfl⟩
    rw [hw y' (hWV hy'), hvW y' hy', Finset.sup'_image]
    congr 1
    refine Finset.sup'_congr hs rfl fun p _ => ?_
    simp only [Function.comp_apply, φ, tropAffine, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, hlog y' hy']
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_mul, mul_assoc]
    ring

/-- Convex PL functions on an open subset of `(Y_f)^an`, extended by `-∞`, are convex PL on its
image in `Y^an`. -/
theorem IsConvexPLOn.awayExtend {f : A} {V : Set (Berk k (Localization.Away f))}
    {v : Berk k (Localization.Away f) → EReal} (hv : IsConvexPLOn V v) :
    IsConvexPLOn (awayComap f '' V) (awayExtend f v) :=
  hv.awayComap_image fun y _ => awayExtend_awayComap f v y

/-- **Gluing across `{|f| = 0}`.** If `φ` is convex PL on `(Y_f)^an` and `φ ≤ r` near every
point of `{|f| = 0}`, then `max{φ, r}` extended by `r` is convex PL on `Y^an`. -/
theorem isConvexPLOn_univ_max_awayExtend {f : A} {φ : Berk k (Localization.Away f) → EReal}
    (hφ : IsConvexPLOn Set.univ φ) (r : ℚ)
    (hloc : ∀ x : Berk k A, x.val f = 0 → ∃ N : Set (Berk k A), IsOpen N ∧ x ∈ N ∧
      ∀ y, awayComap f y ∈ N → φ y ≤ ((r : ℝ) : EReal)) :
    IsConvexPLOn Set.univ fun x => max (awayExtend f φ x) ((r : ℝ) : EReal) := by
  refine isConvexPLOn_of_local fun x _ => ?_
  by_cases hx : x.val f = 0
  · obtain ⟨N, hN, hxN, hle⟩ := hloc x hx
    refine ⟨N, hN, hxN, Set.subset_univ _, (isConvexPLOn_const hN r).congr fun x' hx' => ?_⟩
    by_cases h' : x'.val f = 0
    · rw [awayExtend_of_eq_zero f φ h', max_bot_left]
    · rw [awayExtend_of_ne_zero f φ h',
        max_eq_right (hle _ (by rwa [awayComap_awayLift]))]
  · have hΩ : awayComap f '' Set.univ = {x : Berk k A | x.val f ≠ 0} := by
      rw [Set.image_univ, range_awayComap]
    have h1 := hφ.awayExtend (f := f)
    rw [hΩ] at h1
    exact ⟨_, isOpen_setOf_abs_ne_zero f, hx, Set.subset_univ _,
      h1.max (isConvexPLOn_const (isOpen_setOf_abs_ne_zero f) r)⟩

/-! ### The FS functions `g_ε = max{g, ε log|1/f|}` on `Y_f` -/

open Classical in
/-- For `g ∈ FS(Y)` and `ε ∈ ℚ_{>0}`, the FS function `max{g, ε log|1/f|} = max{g, -ε log|f|}`
on `Y_f` (its functions are those of `g` together with `1/f`, which generate `A_f`). -/
def FSData.awayEps (g : FSData k A) (f : A) (ε : ℚ) (hε : 0 < ε) :
    FSData k (Localization.Away f) where
  terms := insert (IsLocalization.Away.invSelf f, ε, 0)
    (g.terms.image fun t => (algebraMap A (Localization.Away f) t.1, t.2.1, t.2.2))
  const := g.const
  pos t ht := by
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hε
    · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
      exact g.pos t' ht'
  gen := by
    have e : Prod.fst '' ((insert (IsLocalization.Away.invSelf f, ε, 0)
        (g.terms.image fun t => (algebraMap A (Localization.Away f) t.1, t.2.1, t.2.2)) :
          Finset _) : Set (Localization.Away f × ℚ × ℚ)) =
        insert (IsLocalization.Away.invSelf f)
          (algebraMap A (Localization.Away f) '' (Prod.fst '' (g.terms : Set (A × ℚ × ℚ)))) := by
      rw [Finset.coe_insert, Set.image_insert_eq, Finset.coe_image, Set.image_image,
        Set.image_image]
    rw [e]
    exact adjoin_awayInvSelf_eq_top f g.gen

theorem FSData.eval_awayEps (g : FSData k A) (f : A) (ε : ℚ) (hε : 0 < ε)
    (y : Berk k (Localization.Away f)) :
    (g.awayEps f ε hε).eval y = max (g.eval (awayComap f y))
      (((ε : ℝ) : EReal) * logAbs (IsLocalization.Away.invSelf f : Localization.Away f) y) := by
  classical
  have h1 : fsTerm ((IsLocalization.Away.invSelf f : Localization.Away f), ε, (0 : ℚ)) y =
      ((ε : ℝ) : EReal) * logAbs (IsLocalization.Away.invSelf f : Localization.Away f) y := by
    simp [fsTerm_def]
  simp only [eval_def, awayEps, Finset.sup_insert, Finset.sup_image, Function.comp_def, h1]
  rw [max_left_comm, max_comm (((ε : ℝ) : EReal) * _)]
  rfl

theorem FSData.eval_awayEps' (g : FSData k A) (f : A) (ε : ℚ) (hε : 0 < ε)
    (y : Berk k (Localization.Away f)) :
    (g.awayEps f ε hε).eval y = max (g.eval (awayComap f y))
      (-(((ε : ℝ) : EReal) * logAbs f (awayComap f y))) := by
  rw [eval_awayEps, logAbs_awayComap_invSelf, mul_neg]

end general

/-! ### FHX Lemma 5.12 -/

section normal

universe u v

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- A convex PL function on `Y^an` of logarithmic growth, not identically `-∞`, is regularizable
(the imported FHX Lemma 5.11(6) with the constant sequence). -/
theorem IsConvexPLOn.isRegularizable [IsAlgClosed k] [WuRegularization.{u, v} k] [IsIntegrallyClosed A]
    {w : Berk k A → EReal} (hw : IsConvexPLOn Set.univ w) (hne : ∃ x, w x ≠ ⊥)
    (hlog : HasLogGrowth w) : IsRegularizable w :=
  WuRegularization.localToGlobal A w hne hlog fun _ _ =>
    ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ => w, fun _ => hw,
      fun _ _ => antitone_const, fun _ _ => iInf_const.symm⟩

/-- `Localization.Away f` of a normal domain is a normal domain. -/
theorem isIntegrallyClosed_localizationAway [IsIntegrallyClosed A] {f : A} (hf : f ≠ 0) :
    IsIntegrallyClosed (Localization.Away f) :=
  isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

/-- **FHX Lemma 5.12** (`lem:principal-extension`). Let `Y = Spec A` be a normal affine variety,
`0 ≠ f ∈ A`, and `v ∈ ℛ(Y_f)` with `v ≤ g + C` on `(Y_f)^an` for some `g ∈ FS(Y)`. For every
`c ∈ ℚ_{>0}`, the function equal to `v + c log|f|` on `(Y_f)^an` and to `-∞` on `{|f| = 0}` is
regularizable on `Y`. -/
theorem IsRegularizable.awayExtend_add [IsAlgClosed k] [WuRegularization.{u, v} k] [IsIntegrallyClosed A]
    {f : A} (hf : f ≠ 0) {v : Berk k (Localization.Away f) → EReal} (hv : IsRegularizable v)
    (g : FSData k A) (C : ℝ) (hvg : ∀ y, v y ≤ g.eval (awayComap f y) + (C : EReal))
    {c : ℚ} (hc : 0 < c) :
    IsRegularizable
      (awayExtend f fun y => v y + ((c : ℝ) : EReal) * logAbs f (awayComap f y)) := by
  have : IsDomain (Localization.Away f) := isDomain_localizationAway hf
  have : IsIntegrallyClosed (Localization.Away f) := isIntegrallyClosed_localizationAway hf
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  -- `ε = c / 3` and `g_ε = max{g, -ε log|f|}`.
  set ε : ℚ := c / 3 with hεdef
  have hε : 0 < ε := by positivity
  have hεR : (ε : ℝ) = c / 3 := by rw [hεdef]; push_cast; ring
  set gε := g.awayEps f ε hε with hgε
  have hvgε : ∀ y, v y ≤ gε.eval y + (C : EReal) := fun y =>
    (hvg y).trans (add_le_add (by rw [hgε, FSData.eval_awayEps]; exact le_max_left _ _) le_rfl)
  -- Growth-controlled approximants `u_j ≤ 2 g_ε + C_j` (FHX Lemma 5.11(5)).
  obtain ⟨h, hanti, hlim, hbd⟩ :=
    WuRegularization.growthControl (Localization.Away f) v gε C hv hvgε 2 one_lt_two
  choose Cj hCj using hbd
  -- The real form of the bound: `u_j ≤ 2 max{g, -ε L} + C_j` with `L = log|f|`.
  have hbdR : ∀ j y, (h j).evalReal y ≤
      2 * max (g.evalReal (awayComap f y))
        (-(ε * Real.log ((awayComap f y).val f : ℝ))) + Cj j := by
    intro j y
    have := hCj j y
    rw [hgε, FSData.eval_awayEps', logAbs_awayComap_eq_coe, ← g.coe_evalReal,
      ← (h j).coe_evalReal, ← EReal.coe_mul, ← EReal.coe_neg,
      ← ereal_coe_max, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    simpa using this
  -- The functions `ψ_j = u_j + c log|f|` on `(Y_f)^an` and `w_j = max{ψ_j, -j}` extended by `-j`.
  set ψ : ℕ → Berk k (Localization.Away f) → EReal :=
    fun j y => (h j).eval y + ((c : ℝ) : EReal) * logAbs f (awayComap f y) with hψ
  set w : ℕ → Berk k A → EReal :=
    fun j x => max (awayExtend f (ψ j) x) (((-(j : ℚ) : ℚ) : ℝ) : EReal) with hw
  have hψR : ∀ j y, ψ j y = (((h j).evalReal y + c * Real.log ((awayComap f y).val f : ℝ) : ℝ) :
      EReal) := by
    intro j y
    simp only [hψ]
    rw [logAbs_awayComap_eq_coe, ← (h j).coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add]
  -- Convex PL: near `{|f| = 0}`, `ψ_j ≤ -j`.
  have hcpl : ∀ j, IsConvexPLOn Set.univ (w j) := by
    intro j
    refine isConvexPLOn_univ_max_awayExtend ?_ (-(j : ℚ)) fun x hx => ?_
    · have hlogf : IsConvexPLOn Set.univ fun y : Berk k (Localization.Away f) =>
          ((c : ℝ) : EReal) * logAbs (algebraMap A (Localization.Away f) f) y := by
        have e : {y : Berk k (Localization.Away f) | y.val (algebraMap A _ f) ≠ 0} = Set.univ :=
          Set.eq_univ_of_forall (Berk.Away.val_algebraMap_ne_zero (Localization.Away f) f)
        have h' := isConvexPLOn_smul_logAbs (k := k) (algebraMap A (Localization.Away f) f) c
        rw [e] at h'
        exact h'
      exact (h j).isConvexPLOn_univ.add hlogf
    · -- Choose `T` so negative that the bound forces `ψ_j ≤ -j` where `log|f| < T`, `g < g(x)+1`.
      set G₀ : ℝ := g.evalReal x + 1
      set T : ℝ := min ((-(j : ℝ) - Cj j - 2 * G₀) / c) ((-(j : ℝ) - Cj j) / (c / 3))
      refine ⟨{x' | g.eval x' < (G₀ : EReal)} ∩ {x' | logAbs f x' < (T : EReal)},
        (isOpen_lt g.continuous_eval continuous_const).inter (isOpen_setOf_logAbs_lt f _),
        ⟨?_, ?_⟩, fun y hy => ?_⟩
      · show g.eval x < (G₀ : EReal)
        rw [← g.coe_evalReal, EReal.coe_lt_coe_iff]
        linarith
      · show logAbs f x < (T : EReal)
        rw [(logAbs_eq_bot_iff f x).2 hx]
        exact EReal.bot_lt_coe T
      · obtain ⟨hy1, hy2⟩ := hy
        simp only [Set.mem_ofPred_eq] at hy1 hy2
        rw [← g.coe_evalReal, EReal.coe_lt_coe_iff] at hy1
        rw [logAbs_awayComap_eq_coe, EReal.coe_lt_coe_iff] at hy2
        rw [hψR, EReal.coe_le_coe_iff]
        push_cast
        set L := Real.log ((awayComap f y).val f : ℝ)
        have hb := hbdR j y
        have hT1 : T ≤ (-(j : ℝ) - Cj j - 2 * G₀) / c := min_le_left _ _
        have hT2 : T ≤ (-(j : ℝ) - Cj j) / (c / 3) := min_le_right _ _
        rw [le_div_iff₀ hcR] at hT1
        rw [le_div_iff₀ (by positivity)] at hT2
        rw [hεR] at hb
        rcases le_total (g.evalReal (awayComap f y)) (-(c / 3 * L)) with hm | hm
        · rw [max_eq_right hm] at hb
          nlinarith
        · rw [max_eq_left hm] at hb
          nlinarith
  -- Logarithmic growth: `w_j ≤ max{max{2g + c log|f|, (c - 2ε) log|f|} + C_j, -j}`.
  have hlog : ∀ j, HasLogGrowth (w j) := by
    intro j
    have hc2 : (0 : ℝ) ≤ c / 3 := by positivity
    have hβ : HasLogGrowth fun x : Berk k A =>
        max (max (((2 : ℝ) : EReal) * g.eval x + ((c : ℝ) : EReal) * logAbs f x)
          (((c / 3 : ℝ) : EReal) * logAbs f x) + ((Cj j : ℝ) : EReal))
          (((-(j : ℚ) : ℚ) : ℝ) : EReal) :=
      ((((g.hasLogGrowth.smul (by norm_num : (0 : ℝ) ≤ 2)).add
        ((hasLogGrowth_logAbs f).smul hcR.le)).sup ((hasLogGrowth_logAbs f).smul hc2)).add_const
          (Cj j)).sup (hasLogGrowth_const _)
    refine hβ.mono fun x => max_le_max ?_ le_rfl
    rw [awayExtend_le_iff]
    intro hx
    set y := awayLift f x hx
    have hxy : awayComap f y = x := awayComap_awayLift f x hx
    rw [hψR, ← hxy, logAbs_awayComap_eq_coe, ← g.coe_evalReal, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← ereal_coe_max, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    set L := Real.log ((awayComap f y).val f : ℝ)
    have hb := hbdR j y
    rw [hεR] at hb
    rcases le_total (g.evalReal (awayComap f y)) (-(c / 3 * L)) with hm | hm
    · rw [max_eq_right hm] at hb
      have : (c : ℝ) / 3 * L ≤ max (2 * g.evalReal (awayComap f y) + c * L) (c / 3 * L) :=
        le_max_right _ _
      linarith
    · rw [max_eq_left hm] at hb
      have : 2 * g.evalReal (awayComap f y) + c * L ≤
          max (2 * g.evalReal (awayComap f y) + c * L) (c / 3 * L) := le_max_left _ _
      linarith
  -- Each `w_j` is regularizable (FHX Lemma 5.11(6)).
  have hwreg : ∀ j, IsRegularizable (w j) := fun j =>
    (hcpl j).isRegularizable ⟨triv, ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)⟩
      (hlog j)
  -- The `w_j` decrease to the extension.
  have hext_anti : ∀ x, Antitone fun j => awayExtend f (ψ j) x := by
    intro x i j hij
    show awayExtend f (ψ j) x ≤ awayExtend f (ψ i) x
    by_cases hx : x.val f = 0
    · simp [awayExtend_of_eq_zero f _ hx]
    · rw [awayExtend_of_ne_zero f _ hx, awayExtend_of_ne_zero f _ hx]
      exact add_le_add (hanti _ hij) le_rfl
  have hconst_anti : Antitone fun j : ℕ => (((-(j : ℚ) : ℚ) : ℝ) : EReal) := by
    intro i j hij
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only [Rat.cast_neg, Rat.cast_natCast, EReal.coe_le_coe_iff]
    linarith
  have hconst_inf : ⨅ j : ℕ, (((-(j : ℚ) : ℚ) : ℝ) : EReal) = ⊥ := by
    simpa using iInf_neg_natCast
  have hwmono : ∀ x, Antitone fun j => w j x := fun x i j hij =>
    max_le_max (hext_anti x hij) (hconst_anti hij)
  have hwlim : ∀ x, ⨅ j, w j x =
      awayExtend f (fun y => v y + ((c : ℝ) : EReal) * logAbs f (awayComap f y)) x := by
    intro x
    simp only [hw]
    rw [iInf_max_of_antitone (hext_anti x) hconst_anti, hconst_inf, max_bot_right]
    by_cases hx : x.val f = 0
    · simp [awayExtend_of_eq_zero f _ hx]
    · simp only [awayExtend_of_ne_zero f _ hx, hψ]
      rw [iInf_add_of_antitone (hanti _) antitone_const ((h 0).eval_ne_top _)
        (ereal_coe_mul_ne_top hcR.le (logAbs_ne_top _ _)), iInf_const, ← hlim]
  -- The extension is finite at the trivial valuation.
  have hne : ∃ x, (⨅ j, w j x) ≠ ⊥ := by
    refine ⟨triv, ?_⟩
    rw [hwlim, ← awayComap_triv f, awayExtend_awayComap, awayComap_triv f,
      logAbs_triv_of_ne_zero hf, mul_zero, add_zero]
    exact hv.triv_ne_bot
  exact (IsRegularizable.of_antitone hwreg hwmono hne).congr hwlim

/-- **FHX Lemma 5.12**, stated with the explicit case distinction. -/
theorem IsRegularizable.awayExtend_add' [IsAlgClosed k] [WuRegularization.{u, v} k] [IsIntegrallyClosed A]
    {f : A} (hf : f ≠ 0) {v : Berk k (Localization.Away f) → EReal} (hv : IsRegularizable v)
    (g : FSData k A) (C : ℝ) (hvg : ∀ y, v y ≤ g.eval (awayComap f y) + (C : EReal))
    {c : ℚ} (hc : 0 < c) [∀ x : Berk k A, Decidable (x.val f ≠ 0)] :
    IsRegularizable fun x => if h : x.val f ≠ 0 then
      v (awayLift f x h) + ((c : ℝ) : EReal) * logAbs f x else ⊥ := by
  refine (hv.awayExtend_add hf g C hvg hc).congr fun x => ?_
  by_cases hx : x.val f ≠ 0
  · rw [awayExtend_of_ne_zero f _ hx, dif_pos hx, awayComap_awayLift]
  · rw [awayExtend_of_eq_zero f _ (not_not.1 hx), dif_neg hx]

/-! ### FHX Lemma 5.17 -/

/-- **FHX Lemma 5.17** (`lem:principal-hull`). Let `Y = Spec A` be a normal affine variety,
`0 ≠ f ∈ A`, `v ∈ ℛ(Y_f)` with `v ≤ g + C` on `(Y_f)^an` for some `g ∈ FS(Y)`, `K ⊆ Y^an`
compact and `x ∈ K̂` (hull in `Y`) with `|f|_x ≠ 0`. Then `v(x) ≤ sup_K v`, where `v` is
extended by `-∞` on `{|f| = 0}`. -/
theorem le_iSup_of_mem_hull_awayExtend [IsAlgClosed k] [WuRegularization.{u, v} k] [IsIntegrallyClosed A]
    {f : A} (hf : f ≠ 0) {v : Berk k (Localization.Away f) → EReal} (hv : IsRegularizable v)
    (g : FSData k A) (C : ℝ) (hvg : ∀ y, v y ≤ g.eval (awayComap f y) + (C : EReal))
    {K : Set (Berk k A)} (hK : IsCompact K) {x : Berk k A} (hx : x ∈ hull K)
    (hxf : x.val f ≠ 0) : awayExtend f v x ≤ ⨆ y ∈ K, awayExtend f v y := by
  obtain ⟨R, hR⟩ := exists_abs_le_of_isCompact hK f
  set Lx : ℝ := Real.log (x.val f : ℝ) with hLx
  set M : ℝ := max (Real.log (max (R : ℝ) 1)) (-Lx) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (Real.log_nonneg (le_max_right _ _))
  set S := ⨆ y ∈ K, awayExtend f v y with hS
  -- For every rational `c > 0`: `v(x) ≤ sup_K v + 2 c M`.
  have key : ∀ c : ℚ, 0 < c → awayExtend f v x ≤ S + ((2 * c * M : ℝ) : EReal) := by
    intro c hc
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hhull := (hv.awayExtend_add hf g C hvg hc).satisfiesHullIneq K hK x hx
    rw [awayExtend_of_ne_zero f _ hxf, awayComap_awayLift, logAbs_eq_coe_log hxf] at hhull
    have hsup : (⨆ y ∈ K, awayExtend f
        (fun y => v y + ((c : ℝ) : EReal) * logAbs f (awayComap f y)) y) ≤
        S + ((c * M : ℝ) : EReal) := by
      refine iSup₂_le fun y hy => ?_
      rw [awayExtend_le_iff]
      intro hyf
      rw [awayComap_awayLift, logAbs_eq_coe_log hyf, ← awayExtend_of_ne_zero f v hyf]
      refine add_le_add (le_iSup₂ (f := fun y (_ : y ∈ K) => awayExtend f v y) y hy) ?_
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      refine mul_le_mul_of_nonneg_left ((Real.log_le_log ?_ ?_).trans (le_max_left _ _)) hcR.le
      · exact_mod_cast pos_iff_ne_zero.2 hyf
      · exact (NNReal.coe_le_coe.2 (hR y hy)).trans (le_max_left _ _)
    have h1 : awayExtend f v x + ((-(c * M) : ℝ) : EReal) ≤ S + ((c * M : ℝ) : EReal) := by
      refine le_trans ?_ (hhull.trans hsup)
      rw [awayExtend_of_ne_zero f v hxf]
      refine add_le_add le_rfl ?_
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      have : -M ≤ Lx := by rw [hM]; linarith [le_max_right (Real.log (max (R : ℝ) 1)) (-Lx)]
      nlinarith
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _)), add_assoc, ← EReal.coe_add] at h1
    convert h1 using 3
    ring
  -- Let `c → 0`.
  clear_value S
  clear hS
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  induction S using EReal.rec with
  | bot =>
    have := key 1 one_pos
    rw [EReal.bot_add] at this
    exact this.trans bot_le
  | coe s =>
    rw [EReal.coe_lt_coe_iff] at hz
    obtain ⟨c, hc0, hc⟩ := exists_rat_btwn (show (0 : ℝ) < (z - s) / (2 * M + 1) by
      apply div_pos <;> linarith)
    have hc0' : (0 : ℚ) < c := by exact_mod_cast hc0
    refine (key c hc0').trans ?_
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [lt_div_iff₀ (by linarith)] at hc
    nlinarith
  | top => exact absurd hz (not_lt.2 le_top)

/-- **FHX Lemma 5.17** on `Y_f` (`lem:principal-hull`): for `K ⊆ (Y_f)^an` compact and
`y ∈ (Y_f)^an` whose image in `Y^an` lies in the hull (in `Y`) of the image of `K`,
`v(y) ≤ sup_K v`. -/
theorem le_iSup_of_awayComap_mem_hull [IsAlgClosed k] [WuRegularization.{u, v} k] [IsIntegrallyClosed A]
    {f : A} (hf : f ≠ 0) {v : Berk k (Localization.Away f) → EReal} (hv : IsRegularizable v)
    (g : FSData k A) (C : ℝ) (hvg : ∀ y, v y ≤ g.eval (awayComap f y) + (C : EReal))
    {K : Set (Berk k (Localization.Away f))} (hK : IsCompact K)
    {y : Berk k (Localization.Away f)} (hy : awayComap f y ∈ hull (awayComap f '' K)) :
    v y ≤ ⨆ y' ∈ K, v y' := by
  have h := le_iSup_of_mem_hull_awayExtend hf hv g C hvg (hK.image (continuous_awayComap f)) hy
    (awayComap_val_ne_zero f y)
  rw [awayExtend_awayComap] at h
  refine h.trans (iSup₂_le ?_)
  rintro _ ⟨y', hy', rfl⟩
  rw [awayExtend_awayComap]
  exact le_iSup₂ (f := fun y' (_ : y' ∈ K) => v y') y' hy'

end normal

end EnvelopeProperty
