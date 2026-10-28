/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Diagonal approximation of decreasing double limits on a compact set

Let `X` be a topological space, `K ⊆ X` compact, and let `g i j : X → EReal` be continuous,
finite-valued functions, decreasing in `j`, whose limits `u i = ⨅ j, g i j` decrease in `i`, with
limit `u = ⨅ i, u i`. Then there is a sequence of functions of the form `g i j + q`
(`q` a positive rational) that is decreasing on `K` and converges to `u` on `K`.

This is the sequential, finite-valued form of the directedness argument of Boucksom–Jonsson
(BJ22, Lemma 4.? `lem:PSH`): for two functions `s = g i₁ j₁ + q₁` and `t = g i₂ j₂ + q₂`,
choosing `i ≥ i₁, i₂` and `0 < q < min q₁ q₂` gives `u i + q < min s t` everywhere (finiteness
makes the inequality strict), and by compactness some `g i j + q < min s t` on all of `K`.
It is used to derive FHX Lemma 5.11(2) from Lemma 5.11(6).
-/

open scoped Topology

noncomputable section

namespace EnvelopeProperty

variable {X : Type*} [TopologicalSpace X]

/-- Strict comparison on a compact set: if continuous `f j` decrease pointwise to a limit that is
strictly below a continuous finite-valued function `s` on a compact set `K`, then `f j < s` on `K`
for some `j`. -/
theorem exists_lt_on_compact_of_antitone {K : Set X} (hK : IsCompact K)
    {f : ℕ → X → EReal} (hf : ∀ j, Continuous (f j)) (hmono : ∀ x, Antitone fun j => f j x)
    {s : X → EReal} (hs : Continuous s) (hlt : ∀ x ∈ K, (⨅ j, f j x) < s x) :
    ∃ j, ∀ x ∈ K, f j x < s x := by
  -- The open sets `{f j < s}` increase and cover `K`.
  have hopen : ∀ j, IsOpen {x | f j x < s x} := fun j => isOpen_lt (hf j) hs
  have hcover : K ⊆ ⋃ j, {x | f j x < s x} := by
    intro x hx
    obtain ⟨j, hj⟩ := iInf_lt_iff.1 (hlt x hx)
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hdir : Directed (· ⊆ ·) fun j => {x | f j x < s x} := by
    intro i j
    refine ⟨max i j, fun x hx => lt_of_le_of_lt (hmono x (le_max_left i j)) hx,
      fun x hx => lt_of_le_of_lt (hmono x (le_max_right i j)) hx⟩
  obtain ⟨j, hj⟩ := hK.elim_directed_cover _ hopen hcover hdir
  exact ⟨j, fun x hx => hj hx⟩

/-- **Diagonal approximation.** Let `g i j` be continuous functions `X → EReal` with values in
`ℝ`, decreasing in `j`, such that `u i := ⨅ j, g i j` decreases in `i`, and let `K` be compact.
Then there are indices `i m, j m` and positive rationals `q m` such that
`h m = g (i m) (j m) + q m` is decreasing on `K` and `⨅ m, h m x = ⨅ i, u i x` for `x ∈ K`. -/
theorem exists_antitone_diagonal {K : Set X} (hK : IsCompact K)
    (g : ℕ → ℕ → X → EReal) (hcont : ∀ i j, Continuous (g i j))
    (hbot : ∀ i j x, g i j x ≠ ⊥) (htop : ∀ i j x, g i j x ≠ ⊤)
    (hj : ∀ i x, Antitone fun j => g i j x)
    (hi : ∀ x, Antitone fun i => ⨅ j, g i j x) :
    ∃ (I J : ℕ → ℕ) (q : ℕ → ℚ), (∀ m, 0 < q m) ∧
      (∀ x ∈ K, Antitone fun m => g (I m) (J m) x + ((q m : ℝ) : EReal)) ∧
      ∀ x ∈ K, ⨅ m, (g (I m) (J m) x + ((q m : ℝ) : EReal)) = ⨅ i, ⨅ j, g i j x := by
  classical
  -- The countable family `T = {g i j + q}` indexed by `ℕ × ℕ × ℚ_{>0}`.
  set T : ℕ × ℕ × {q : ℚ // 0 < q} → X → EReal :=
    fun t x => g t.1 t.2.1 x + (((t.2.2 : ℚ) : ℝ) : EReal) with hT
  -- Key step: for any `s t`, some element of `T` is below both on `K`.
  have key : ∀ a b : ℕ × ℕ × {q : ℚ // 0 < q}, ∃ c : ℕ × ℕ × {q : ℚ // 0 < q},
      ∀ x ∈ K, T c x ≤ min (T a x) (T b x) := by
    intro a b
    obtain ⟨i₁, j₁, q₁⟩ := a
    obtain ⟨i₂, j₂, q₂⟩ := b
    set i := max i₁ i₂
    set q : ℚ := min (q₁ : ℚ) q₂ / 2
    have hq : 0 < q := by
      have := lt_min q₁.2 q₂.2
      positivity
    have hq1 : q < q₁ := by
      have : min (q₁ : ℚ) q₂ ≤ q₁ := min_le_left _ _
      have h0 : 0 < min (q₁ : ℚ) q₂ := lt_min q₁.2 q₂.2
      simp only [q]; linarith
    have hq2 : q < q₂ := by
      have : min (q₁ : ℚ) q₂ ≤ q₂ := min_le_right _ _
      have h0 : 0 < min (q₁ : ℚ) q₂ := lt_min q₁.2 q₂.2
      simp only [q]; linarith
    -- the function `min s t` is continuous
    set s : X → EReal := fun x => min (T (i₁, j₁, q₁) x) (T (i₂, j₂, q₂) x) with hs
    have hcont_add : ∀ i j (r : ℝ), Continuous fun x => g i j x + (r : EReal) := by
      intro i j r
      refine continuous_iff_continuousAt.2 fun x => ?_
      refine ContinuousAt.comp (f := fun x => (g i j x, (r : EReal)))
        (g := fun p : EReal × EReal => p.1 + p.2) ?_ ?_
      · exact EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
      · exact ((hcont i j).continuousAt).prodMk continuousAt_const
    have hscont : Continuous s := (hcont_add _ _ _).min (hcont_add _ _ _)
    -- `u i + q < s` pointwise
    have hlt : ∀ x ∈ K, (⨅ j, (g i j x + ((q : ℝ) : EReal))) < s x := by
      intro x _
      -- `⨅ j, (g i j x + q) ≤ g i₁ j₁ x + q < g i₁ j₁ x + q₁`, using `u i ≤ u i₁ ≤ g i₁ j₁`.
      have hui1 : (⨅ j, g i j x) ≤ g i₁ j₁ x :=
        (hi x (le_max_left i₁ i₂)).trans (iInf_le _ j₁)
      have hui2 : (⨅ j, g i j x) ≤ g i₂ j₂ x :=
        (hi x (le_max_right i₁ i₂)).trans (iInf_le _ j₂)
      have hstrict : ∀ (a b : EReal) (r r' : ℝ), b ≠ ⊥ → b ≠ ⊤ → a ≤ b → r < r' →
          ∀ c : EReal, (c ≤ a + (r : EReal)) → c < b + (r' : EReal) := by
        intro a b r r' hb hb' hab hrr c hc
        lift b to ℝ using ⟨hb', hb⟩
        refine lt_of_le_of_lt hc (lt_of_le_of_lt (add_le_add hab le_rfl) ?_)
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      -- choose the infimum over `j` of `g i j + q`: bounded by `(⨅ j, g i j) + q`.
      have hinf : (⨅ j, (g i j x + ((q : ℝ) : EReal))) ≤ (⨅ j, g i j x) + ((q : ℝ) : EReal) := by
        refine le_of_forall_gt fun c hc => ?_
        -- If `(⨅ j, g i j x) + q < c` then some `g i j x + q < c`.
        by_cases hinfbot : (⨅ j, g i j x) = ⊥
        · -- then for every real bound some `g i j x` is below it
          have : ∃ j, g i j x + ((q : ℝ) : EReal) < c := by
            rw [hinfbot, EReal.bot_add] at hc
            obtain ⟨c', hc'⟩ : ∃ c' : ℝ, (c' : EReal) + ((q : ℝ) : EReal) < c := by
              induction c using EReal.rec with
              | bot => exact absurd hc (lt_irrefl _)
              | coe c => exact ⟨c - q - 1, by rw [← EReal.coe_add, EReal.coe_lt_coe_iff]; linarith⟩
              | top => exact ⟨0, by simp⟩
            have : (⨅ j, g i j x) < (c' : EReal) := by rw [hinfbot]; exact EReal.bot_lt_coe c'
            obtain ⟨j, hj⟩ := iInf_lt_iff.1 this
            refine ⟨j, lt_of_le_of_lt ?_ hc'⟩
            exact add_le_add hj.le le_rfl
          obtain ⟨j, hj⟩ := this
          exact lt_of_le_of_lt (iInf_le _ j) hj
        · have hinftop : (⨅ j, g i j x) ≠ ⊤ :=
            ne_top_of_le_ne_top (htop i 0 x) (iInf_le _ 0)
          lift (⨅ j, g i j x) to ℝ using ⟨hinftop, hinfbot⟩ with m hm
          -- `m + q < c`, so pick `j` with `g i j x < c - q`
          have : ∃ j, g i j x + ((q : ℝ) : EReal) < c := by
            induction c using EReal.rec with
            | bot => exact absurd hc (not_lt_bot)
            | coe c =>
              rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at hc
              have : (⨅ j, g i j x) < ((c - q : ℝ) : EReal) := by
                rw [← hm, EReal.coe_lt_coe_iff]; linarith
              obtain ⟨j, hj⟩ := iInf_lt_iff.1 this
              refine ⟨j, ?_⟩
              calc g i j x + ((q : ℝ) : EReal) < ((c - q : ℝ) : EReal) + ((q : ℝ) : EReal) := by
                      have hgtop := htop i j x
                      have hgbot := hbot i j x
                      lift g i j x to ℝ using ⟨hgtop, hgbot⟩ with a
                      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
                      rw [EReal.coe_lt_coe_iff] at hj; linarith
                  _ = (c : EReal) := by rw [← EReal.coe_add]; congr 1; ring
            | top =>
              exact ⟨0, by
                have hgtop := htop i 0 x
                have hgbot := hbot i 0 x
                lift g i 0 x to ℝ using ⟨hgtop, hgbot⟩ with a
                rw [← EReal.coe_add]; exact EReal.coe_lt_top _⟩
          obtain ⟨j, hj⟩ := this
          exact lt_of_le_of_lt (iInf_le _ j) hj
      refine lt_min ?_ ?_
      · exact hstrict _ _ _ _ (hbot i₁ j₁ x) (htop i₁ j₁ x) hui1 (by exact_mod_cast hq1) _ hinf
      · exact hstrict _ _ _ _ (hbot i₂ j₂ x) (htop i₂ j₂ x) hui2 (by exact_mod_cast hq2) _ hinf
    have hmono' : ∀ x, Antitone fun j => g i j x + ((q : ℝ) : EReal) :=
      fun x a b hab => add_le_add (hj i x hab) le_rfl
    obtain ⟨j, hjK⟩ := exists_lt_on_compact_of_antitone hK (fun j => hcont_add i j q)
      hmono' hscont hlt
    exact ⟨(i, j, ⟨q, hq⟩), fun x hx => (hjK x hx).le⟩
  -- Enumerate `T` and build the decreasing sequence.
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ × ℕ × {q : ℚ // 0 < q}, Function.Surjective e := by
    have : Nonempty (ℕ × ℕ × {q : ℚ // 0 < q}) := ⟨(0, 0, ⟨1, one_pos⟩)⟩
    exact exists_surjective_nat _
  choose c hc using key
  let H : ℕ → ℕ × ℕ × {q : ℚ // 0 < q} := fun m => Nat.rec (e 0) (fun m h => c h (e (m + 1))) m
  have Hsucc : ∀ m x, x ∈ K → T (H (m + 1)) x ≤ min (T (H m) x) (T (e (m + 1)) x) :=
    fun m x hx => hc _ _ x hx
  have Hle : ∀ m x, x ∈ K → T (H m) x ≤ T (e m) x := by
    intro m x hx
    cases m with
    | zero => exact le_rfl
    | succ m => exact (Hsucc m x hx).trans (min_le_right _ _)
  refine ⟨fun m => (H m).1, fun m => (H m).2.1, fun m => ((H m).2.2 : ℚ), fun m => (H m).2.2.2,
    ?_, ?_⟩
  · intro x hx
    exact antitone_nat_of_succ_le fun m => (Hsucc m x hx).trans (min_le_left _ _)
  · intro x hx
    apply le_antisymm
    · -- `⨅ T ≤ ⨅ i, ⨅ j, g i j` using surjectivity of `e` and arbitrary small `q`.
      refine le_iInf fun i => le_iInf fun j => ?_
      have hle : ∀ q : ℚ, 0 < q →
          (⨅ m, T (H m) x) ≤ g i j x + ((q : ℝ) : EReal) := by
        intro q hq
        obtain ⟨m, hm⟩ := he (i, j, ⟨q, hq⟩)
        refine (iInf_le _ m).trans ((Hle m x hx).trans ?_)
        rw [hm]
      change (⨅ m, T (H m) x) ≤ g i j x
      have hgb := hbot i j x
      have hgt := htop i j x
      lift g i j x to ℝ using ⟨hgt, hgb⟩ with a ha
      refine le_of_forall_gt fun c hc => ?_
      obtain ⟨q, hq, hqc⟩ : ∃ q : ℚ, 0 < q ∧ (a : EReal) + ((q : ℝ) : EReal) < c := by
        induction c using EReal.rec with
        | bot => exact absurd hc not_lt_bot
        | coe c =>
          rw [EReal.coe_lt_coe_iff] at hc
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_pos.2 hc)
          exact ⟨q, by exact_mod_cast hq1, by
            rw [← EReal.coe_add, EReal.coe_lt_coe_iff]; linarith⟩
        | top => exact ⟨1, one_pos, by rw [← EReal.coe_add]; exact EReal.coe_lt_top _⟩
      exact lt_of_le_of_lt (hle q hq) hqc
    · refine le_iInf fun m => ?_
      refine (iInf_le _ (H m).1).trans ((iInf_le _ (H m).2.1).trans ?_)
      have : (0 : EReal) ≤ (((H m).2.2 : ℚ) : ℝ) := by
        exact_mod_cast (H m).2.2.2.le
      simpa using add_le_add (le_refl (g (H m).1 (H m).2.1 x)) this

end EnvelopeProperty
