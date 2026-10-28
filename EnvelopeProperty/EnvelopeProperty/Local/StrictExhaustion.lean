/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.ExhaustionDef
import EnvelopeProperty.Local.Regularizable
import EnvelopeProperty.Local.SupportLine

/-!
# A strictly psh exhaustion (FHX Lemma 5.18)

Let `Y = Spec A` be a normal affine variety over a countable trivially valued field `k`. Following
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.18
(`lem:strict-exhaustion`), we construct a **strict exhaustion** (`IsStrictExhaustion`): a
nonnegative regularizable function `ρ` such that for every point `x` and neighbourhood `V` of `x`
there are a regularizable `ρ' ≤ ρ` with `ρ'(x) = ρ(x)` and `δ > 0` with `ρ' ≤ ρ - δ` off `V`.

The construction is a series of the functions `h_f = log (1 + |f|)`, `f ∈ A`, whose supporting
lines are explicit (`EnvelopeProperty.Local.SupportLine`).

* `isRegularizable_iInf_finsetSup_fsTerm`: a decreasing limit of finite maxima
  `max_i (a_i log|f_i| + b_i)` (`a_i ∈ ℚ_{>0}`, `b_i ∈ ℚ`) is regularizable unless it is `≡ -∞`.
  This is FHX Lemma 5.11(3) combined with an elementary case of 5.11(2): the FS functions
  `max{q_j, b/(j+1) - (j+1)}` decrease to the limit. It does not use the imported
  `WuRegularization`.
* `isRegularizable_logOneAddAbs` (step 1): `log (1 + |f|)` is regularizable. From
  `max_α binom(m,α) s^α ≤ (1 + s)^m ≤ (m+1) max_α binom(m,α) s^α`, the functions
  `max_{α ≤ m} ((1/m) log|f^α| + c_{m,α})` with rational `c_{m,α}` close to
  `(log binom(m,α) + log(m+1))/m` lie between `log(1+|f|)` and
  `log(1+|f|) + (log(m+1)+1)/m` (`binomial_bounds`).
* `isRegularizable_coe_mul_logAbs_add` (step 2): `p log|f| + C` is regularizable for real
  `p > 0` and `C` (if `f` does not vanish identically), as the decreasing limit of `max{a_m log|f| + C_m, a'_m log|f| + C_m}` with
  rationals `a_m ↑ p`, `a'_m ↓ p`, `C_m ↓ C`.
* `isRegularizable_tsum` (step 3): a series `∑_j w_j` of nonnegative real functions with
  `w_j ≤ 2^{-(j+1)} b`, `b = 1 + max{0, log|z_l|}`, each `w_j` regularizable or zero, is
  regularizable: the regularizable functions `∑_{j<N} w_j + 2^{-N} b` decrease to it
  (FHX Lemma 5.11(2), `IsRegularizable.of_antitone`, which uses the imported
  `WuRegularization`).
* `exists_supportFun` (supporting lines): for `x` and `f`, the function
  `ℓ = γ (log(1+s₀) + p (log|f| - log s₀))` (`s₀ = |f|_x > 0`, `p = s₀/(1+s₀)`), resp. `ℓ = 0`
  (`s₀ = 0`), is regularizable, `ℓ ≤ γ h_f`, `ℓ(x) = γ h_f(x)`, and `ℓ + δ ≤ γ h_f` where
  `| |f| - s₀ | ≥ ε`.
* `exists_isStrictExhaustion` (step 4, **FHX Lemma 5.18**): enumerate `A = {f_0, f_1, …}`
  (`A` is countable as `k` is), choose integers `C_j ≥ 1` with `h_{f_j} ≤ C_j b`
  (`exists_logOneAddAbs_le`, FHX Lemma 5.8) and put `ρ = ∑_j γ_j h_{f_j}`,
  `γ_j = 2^{-(j+1)}/C_j`. A neighbourhood `V` of `x` contains a set
  `{y : | |f|_y - |f|_x | < ε for f ∈ F}` with `F` finite (`exists_finset_of_mem_nhds`); with
  `J` the indices of `F`, `ρ' = ∑_{j ∉ J} γ_j h_{f_j} + ∑_{j ∈ J} ℓ_j` works.

We write the Berkovich points multiplicatively (`|f|_x = x.val f`), so the source's
`λ(-log|f|) = log(1 + e^{log|f|})` is `log (1 + |f|)`. The source assumes `k` algebraically
closed; the construction does not use it (only the imported `WuRegularization`, through FHX
Lemma 5.11(2), refers to the setting of the source).
-/

open scoped NNReal ENNReal Topology

open Filter Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Decreasing limits of finite maxima of terms -/

/-- **FHX Lemma 5.11(2),(3)**, elementary case: the limit of a decreasing sequence of finite
maxima `q_j = max_i (a_{j,i} log|f_{j,i}| + b_{j,i})` with `a_{j,i} ∈ ℚ_{>0}`, `b_{j,i} ∈ ℚ`, not
identically `-∞`, is regularizable: the FS functions `max{q_j, b/(j+1) - (j+1)}` decrease to it.
No imported statement is needed. -/
theorem isRegularizable_iInf_finsetSup_fsTerm [Algebra.FiniteType k A]
    {s : ℕ → Finset (A × ℚ × ℚ)} (hs : ∀ j, ∀ t ∈ s j, 0 < t.2.1)
    (hanti : ∀ x : Berk k A, Antitone fun j => (s j).sup fun t => fsTerm t x)
    (hne : ∃ x : Berk k A, (⨅ j, (s j).sup fun t => fsTerm t x) ≠ ⊥) :
    IsRegularizable fun x : Berk k A => ⨅ j, (s j).sup fun t => fsTerm t x := by
  refine ⟨hne, fun j => (FSData.truncStd k A j).addTerms (s j) (hs j), fun x i j hij => ?_,
    fun x => ?_⟩
  · simp only [FSData.eval_addTerms]
    exact max_le_max (FSData.antitone_truncStd k A x hij) (hanti x hij)
  · simp only [FSData.eval_addTerms]
    rw [iInf_max_of_antitone (FSData.antitone_truncStd k A x) (hanti x), FSData.iInf_truncStd,
      max_bot_left]

/-! ### Step 1: `log (1 + |f|)` is regularizable -/

/-- The real function `h_f = log (1 + |f|)` on the analytification. -/
def logOneAddAbs (f : A) (x : Berk k A) : ℝ := Real.log (1 + (x.val f : ℝ))

theorem logOneAddAbs_nonneg (f : A) (x : Berk k A) : 0 ≤ logOneAddAbs f x :=
  Real.log_nonneg (by linarith [NNReal.coe_nonneg (x.val f)])

/-- Some binomial term dominates: `(1 + s)^m ≤ (m + 1) binom(m, α) s^α` for some `α ≤ m`. -/
theorem exists_one_add_pow_le_succ_mul_choose {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    ∃ α ∈ Finset.range (m + 1), (1 + s) ^ m ≤ (m + 1 : ℝ) * ((m.choose α : ℝ) * s ^ α) := by
  obtain ⟨α, hα, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun α => (m.choose α : ℝ) * s ^ α)
  exact ⟨α, hα, (one_add_pow_le_succ_mul_sup hs m).trans_eq (by rw [he])⟩

/-- `(log (m + 1) + 1) / m` becomes arbitrarily small. -/
theorem exists_log_succ_add_one_div_le {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ (Real.log ((m : ℝ) + 1) + 1) / m ≤ ε := by
  have h1 : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 1) / m) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine this.congr fun m => ?_
    simp
  have h2 := h1.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h2
  obtain ⟨m, hm⟩ := ((h2.eventually (eventually_le_nhds hε)).and (eventually_ge_atTop 1)).exists
  exact ⟨m, hm.2, by rw [add_div]; exact hm.1⟩

/-- **Binomial bounds** (proof of FHX Lemma 5.18). If `m ≥ 1` and the rationals `c_α` satisfy
`(log binom(m,α) + log(m+1))/m + d ≤ c_α ≤ (log binom(m,α) + log(m+1) + 1)/m + d`, then
`Q = max_{α ≤ m} ((1/m) log|f^α| + c_α)` satisfies
`log(1+|f|) + d ≤ Q ≤ log(1+|f|) + d + (log(m+1)+1)/m`. -/
theorem binomial_bounds (f : A) (x : Berk k A) {m : ℕ} (hm : 1 ≤ m) (d : ℝ) (c : ℕ → ℚ)
    (hc₁ : ∀ α ∈ Finset.range (m + 1),
      (Real.log (m.choose α) + Real.log ((m : ℝ) + 1)) / m + d ≤ c α)
    (hc₂ : ∀ α ∈ Finset.range (m + 1),
      (c α : ℝ) ≤ (Real.log (m.choose α) + Real.log ((m : ℝ) + 1) + 1) / m + d) :
    ((logOneAddAbs f x + d : ℝ) : EReal) ≤
        (Finset.range (m + 1)).sup (fun α => fsTerm (k := k) (f ^ α, 1 / (m : ℚ), c α) x) ∧
      (Finset.range (m + 1)).sup (fun α => fsTerm (k := k) (f ^ α, 1 / (m : ℚ), c α) x) ≤
        ((logOneAddAbs f x + d + (Real.log ((m : ℝ) + 1) + 1) / m : ℝ) : EReal) := by
  unfold logOneAddAbs
  set s : ℝ := (x.val f : ℝ) with hs_def
  have hs : 0 ≤ s := NNReal.coe_nonneg _
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmq : (0 : ℚ) < 1 / (m : ℚ) := one_div_pos.2 (by exact_mod_cast hm)
  have habs : ∀ α : ℕ, ((x.val (f ^ α) : ℝ≥0) : ℝ) = s ^ α := fun α => by
    rw [map_pow, NNReal.coe_pow]
  have key : ∀ α : ℕ, x.val (f ^ α) ≠ 0 →
      fsTerm (k := k) (f ^ α, 1 / (m : ℚ), c α) x = ((α * Real.log s / m + c α : ℝ) : EReal) := by
    intro α hα
    rw [fsTerm_eq_coe hα]
    congr 1
    simp only [habs, Real.log_pow]
    push_cast
    ring
  have hchoose : ∀ α ∈ Finset.range (m + 1), (0 : ℝ) < m.choose α := fun α hα => by
    exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hα))
  have hlog1 : Real.log (1 + s) = Real.log ((1 + s) ^ m) / m := by
    rw [Real.log_pow]; field_simp
  constructor
  · obtain ⟨α, hα, hle⟩ := exists_one_add_pow_le_succ_mul_choose hs m
    have hC := hchoose α hα
    have h1 : (0 : ℝ) < (1 + s) ^ m := by positivity
    have hsα : 0 < s ^ α := by
      by_contra hcon
      have : s ^ α = 0 := le_antisymm (not_lt.1 hcon) (by positivity)
      rw [this, mul_zero, mul_zero] at hle
      linarith
    have hne : x.val (f ^ α) ≠ 0 := by
      intro h
      have h' := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
      simp only [habs, NNReal.coe_zero] at h'
      linarith
    refine le_trans ?_
      (Finset.le_sup (f := fun α => fsTerm (k := k) (f ^ α, 1 / (m : ℚ), c α) x) hα)
    rw [key α hne, EReal.coe_le_coe_iff]
    have h2 : Real.log ((1 + s) ^ m) ≤
        Real.log ((m : ℝ) + 1) + Real.log (m.choose α) + α * Real.log s := by
      calc Real.log ((1 + s) ^ m)
          ≤ Real.log (((m : ℝ) + 1) * ((m.choose α : ℝ) * s ^ α)) := Real.log_le_log h1 hle
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hC.ne' hsα.ne',
            Real.log_pow]
          ring
    have h3 := hc₁ α hα
    rw [hlog1]
    have h4 : Real.log ((1 + s) ^ m) / m ≤
        (Real.log ((m : ℝ) + 1) + Real.log (m.choose α) + α * Real.log s) / m :=
      div_le_div_of_nonneg_right h2 hm'.le
    have e : (Real.log ((m : ℝ) + 1) + Real.log (m.choose α) + α * Real.log s) / m =
        (Real.log (m.choose α) + Real.log ((m : ℝ) + 1)) / m + α * Real.log s / m := by ring
    linarith
  · refine Finset.sup_le fun α hα => ?_
    by_cases hne : x.val (f ^ α) = 0
    · rw [fsTerm_eq_bot hmq hne]; exact bot_le
    · rw [key α hne, EReal.coe_le_coe_iff]
      have hsα : 0 < s ^ α := by
        rw [← habs]; exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 hne)
      have hC := hchoose α hα
      have h2 : Real.log (m.choose α) + α * Real.log s ≤ Real.log ((1 + s) ^ m) := by
        rw [← Real.log_pow, ← Real.log_mul hC.ne' hsα.ne']
        exact Real.log_le_log (by positivity)
          (choose_mul_pow_le_one_add_pow hs (Nat.lt_succ_iff.1 (Finset.mem_range.1 hα)))
      have h3 := hc₂ α hα
      rw [hlog1]
      have h4 : (Real.log (m.choose α) + α * Real.log s) / m ≤ Real.log ((1 + s) ^ m) / m :=
        div_le_div_of_nonneg_right h2 hm'.le
      have e : (Real.log (m.choose α) + Real.log ((m : ℝ) + 1) + 1) / m =
          (Real.log (m.choose α) + α * Real.log s) / m - α * Real.log s / m +
            (Real.log ((m : ℝ) + 1) + 1) / m := by ring
      linarith

/-- **Step 1 of FHX Lemma 5.18**: `log (1 + |f|)` is regularizable. The functions
`max_{α ≤ m_j} ((1/m_j) log|f^α| + c_{j,α})`, with `c_{j,α}` rational approximations of
`(log binom(m_j,α) + log(m_j+1))/m_j + 2^{-j}`, decrease to it. -/
theorem isRegularizable_logOneAddAbs [Algebra.FiniteType k A] [Nonempty (Berk k A)] (f : A) :
    IsRegularizable fun x : Berk k A => ((logOneAddAbs f x : ℝ) : EReal) := by
  classical
  choose m hm1 hm2 using fun j : ℕ =>
    exists_log_succ_add_one_div_le (ε := (1 / 2 : ℝ) ^ (j + 1)) (by positivity)
  have hc : ∀ j α, ∃ c : ℚ,
      (Real.log ((m j).choose α) + Real.log ((m j : ℝ) + 1)) / m j + (1 / 2 : ℝ) ^ j ≤ c ∧
      (c : ℝ) ≤ (Real.log ((m j).choose α) + Real.log ((m j : ℝ) + 1) + 1) / m j +
        (1 / 2 : ℝ) ^ j := by
    intro j α
    have hm' : (0 : ℝ) < m j := by exact_mod_cast hm1 j
    obtain ⟨c, h1, h2⟩ := exists_rat_btwn (lt_add_of_pos_right
      ((Real.log ((m j).choose α) + Real.log ((m j : ℝ) + 1)) / m j + (1 / 2 : ℝ) ^ j)
      (one_div_pos.2 hm'))
    exact ⟨c, h1.le, h2.le.trans (le_of_eq (by ring))⟩
  choose c hc1 hc2 using hc
  set s : ℕ → Finset (A × ℚ × ℚ) := fun j =>
    (Finset.range (m j + 1)).image fun α => (f ^ α, 1 / (m j : ℚ), c j α) with hs_def
  have hsup : ∀ j x, ((s j).sup fun t => fsTerm t x) =
      (Finset.range (m j + 1)).sup fun α => fsTerm (k := k) (f ^ α, 1 / (m j : ℚ), c j α) x := by
    intro j x
    simp only [hs_def, Finset.sup_image]
    rfl
  have hb := fun j (x : Berk k A) => binomial_bounds f x (hm1 j) ((1 / 2 : ℝ) ^ j) (c j)
    (fun α _ => hc1 j α) (fun α _ => hc2 j α)
  have hpos : ∀ j, ∀ t ∈ s j, 0 < t.2.1 := by
    intro j t ht
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 ht
    exact one_div_pos.2 (by exact_mod_cast hm1 j)
  have hanti : ∀ x : Berk k A, Antitone fun j => (s j).sup fun t => fsTerm t x := by
    intro x
    refine antitone_nat_of_succ_le fun j => ?_
    rw [hsup, hsup]
    refine (hb (j + 1) x).2.trans (le_trans ?_ (hb j x).1)
    rw [EReal.coe_le_coe_iff]
    have := hm2 (j + 1)
    have e1 : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) ^ j / 2 := by ring
    have e2 : (1 / 2 : ℝ) ^ (j + 1 + 1) = (1 / 2) ^ j / 4 := by ring
    have : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
    linarith
  have hinf : ∀ x : Berk k A,
      (⨅ j, (s j).sup fun t => fsTerm t x) = ((logOneAddAbs f x : ℝ) : EReal) := by
    intro x
    refine le_antisymm ?_ (le_iInf fun j => ?_)
    · refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
      rw [EReal.coe_lt_coe_iff] at hz
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one
        (show 0 < (z - logOneAddAbs f x) / 2 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
      refine (iInf_le _ j).trans ?_
      rw [hsup]
      refine (hb j x).2.trans ?_
      rw [EReal.coe_le_coe_iff]
      have := hm2 j
      have e1 : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) ^ j / 2 := by ring
      have : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
      linarith
    · rw [hsup]
      refine le_trans ?_ (hb j x).1
      rw [EReal.coe_le_coe_iff]
      have : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
      linarith
  exact (isRegularizable_iInf_finsetSup_fsTerm hpos hanti
    ⟨Classical.arbitrary _, by rw [hinf]; exact EReal.coe_ne_bot _⟩).congr hinf

/-! ### Step 2: the supporting functions `p log|f| + C` -/

/-- A decreasing sequence of rationals converging to a given real number from above. -/
theorem exists_antitone_rat_tendsto (c : ℝ) :
    ∃ q : ℕ → ℚ, Antitone q ∧ (∀ j, c < q j) ∧ Tendsto (fun j => (q j : ℝ)) atTop (𝓝 c) := by
  obtain ⟨q, hq, hqc, hlim⟩ := exists_antitone_rat_iInf_eq c
  refine ⟨q, hq, hqc, EReal.tendsto_coe.1 ?_⟩
  rw [← hlim]
  exact tendsto_atTop_iInf fun i j hij => by
    show (((q j : ℚ) : ℝ) : EReal) ≤ ((q i : ℚ) : ℝ)
    exact_mod_cast hq hij

/-- An increasing sequence of positive rationals converging to a given positive real number
from below. -/
theorem exists_monotone_rat_tendsto {p : ℝ} (hp : 0 < p) :
    ∃ a : ℕ → ℚ, Monotone a ∧ (∀ j, 0 < a j) ∧ (∀ j, (a j : ℝ) < p) ∧
      Tendsto (fun j => (a j : ℝ)) atTop (𝓝 p) := by
  obtain ⟨q, hq, hqc, hlim⟩ := exists_antitone_rat_tendsto (-p)
  obtain ⟨r, hr0, hrp⟩ := exists_rat_btwn hp
  refine ⟨fun j => max r (-q j), fun i j hij => max_le_max le_rfl (neg_le_neg (hq hij)),
    fun j => lt_max_of_lt_left (by exact_mod_cast hr0), fun j => ?_, ?_⟩
  · push_cast
    exact max_lt hrp (by linarith [hqc j])
  · have := (tendsto_const_nhds (x := (r : ℝ))).max hlim.neg
    rw [neg_neg, max_eq_right hrp.le] at this
    refine this.congr fun j => ?_
    push_cast
    rfl

/-- **Step 2 of FHX Lemma 5.18**: for real `p > 0` and `C`, the function `p log|f| + C` is
regularizable if it is not identically `-∞`. It is the decreasing limit of
`max{a_m log|f| + C_m, a'_m log|f| + C_m}` with rationals `a_m ↑ p` (`a_m > 0`), `a'_m ↓ p`,
`C_m ↓ C`; these decrease since `max{a τ, a' τ}` decreases as `[a, a']` shrinks. -/
theorem isRegularizable_coe_mul_logAbs_add [Algebra.FiniteType k A] (f : A) {p : ℝ}
    (hp : 0 < p) (C : ℝ) (hne : ∃ x : Berk k A, x.val f ≠ 0) :
    IsRegularizable fun x : Berk k A => (p : EReal) * logAbs f x + (C : EReal) := by
  classical
  obtain ⟨a, ha, ha0, hap, halim⟩ := exists_monotone_rat_tendsto hp
  obtain ⟨a', ha', ha'p, ha'lim⟩ := exists_antitone_rat_tendsto p
  obtain ⟨c, hc, -, hclim⟩ := exists_antitone_rat_tendsto C
  have ha'0 : ∀ j, 0 < a' j := fun j => by exact_mod_cast hp.trans (ha'p j)
  set s : ℕ → Finset (A × ℚ × ℚ) := fun j => {(f, a j, c j), (f, a' j, c j)} with hs_def
  have hpos : ∀ j, ∀ t ∈ s j, 0 < t.2.1 := by
    intro j t ht
    simp only [hs_def, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    exacts [ha0 j, ha'0 j]
  have hsup : ∀ j (x : Berk k A), ((s j).sup fun t => fsTerm t x) =
      max (fsTerm (f, a j, c j) x) (fsTerm (f, a' j, c j) x) := by
    intro j x
    simp only [hs_def, Finset.sup_insert, Finset.sup_singleton]
  -- the real functions `max (a_j τ + c_j) (a'_j τ + c_j)`
  set F : ℕ → ℝ → ℝ := fun j τ => max ((a j : ℝ) * τ + c j) ((a' j : ℝ) * τ + c j) with hF
  have hFanti : ∀ τ, Antitone fun j => F j τ := by
    intro τ i j hij
    have hai : (a i : ℝ) ≤ a j := by exact_mod_cast ha hij
    have ha'i : (a' j : ℝ) ≤ a' i := by exact_mod_cast ha' hij
    have hci : (c j : ℝ) ≤ c i := by exact_mod_cast hc hij
    have hapj := hap j
    have ha'pi := ha'p i
    simp only [hF]
    rcases le_total 0 τ with hτ | hτ
    · refine max_le (le_max_of_le_right ?_) (le_max_of_le_right ?_)
      · nlinarith
      · nlinarith
    · refine max_le (le_max_of_le_left ?_) (le_max_of_le_left ?_)
      · nlinarith
      · nlinarith [ha'p j]
  have hFlim : ∀ τ, Tendsto (fun j => F j τ) atTop (𝓝 (p * τ + C)) := by
    intro τ
    have := ((halim.mul_const τ).add hclim).max ((ha'lim.mul_const τ).add hclim)
    rwa [max_self] at this
  -- pointwise description
  have hval : ∀ j (x : Berk k A), x.val f ≠ 0 →
      max (fsTerm (f, a j, c j) x) (fsTerm (f, a' j, c j) x) =
        ((F j (Real.log (x.val f : ℝ)) : ℝ) : EReal) := by
    intro j x hx
    rw [fsTerm_eq_coe hx, fsTerm_eq_coe hx]
    exact (EReal.coe_strictMono.monotone.map_max).symm
  have hbot : ∀ j (x : Berk k A), x.val f = 0 →
      max (fsTerm (f, a j, c j) x) (fsTerm (f, a' j, c j) x) = ⊥ := by
    intro j x hx
    rw [fsTerm_eq_bot (ha0 j) hx, fsTerm_eq_bot (ha'0 j) hx, max_self]
  have hanti : ∀ x : Berk k A, Antitone fun j => (s j).sup fun t => fsTerm t x := by
    intro x i j hij
    simp only [hsup]
    by_cases hx : x.val f = 0
    · rw [hbot i x hx, hbot j x hx]
    · rw [hval i x hx, hval j x hx, EReal.coe_le_coe_iff]
      exact hFanti _ hij
  have hinf : ∀ x : Berk k A, (⨅ j, (s j).sup fun t => fsTerm t x) =
      (p : EReal) * logAbs f x + (C : EReal) := by
    intro x
    simp only [hsup]
    by_cases hx : x.val f = 0
    · simp only [hbot _ x hx, iInf_const]
      rw [(logAbs_eq_bot_iff f x).2 hx, EReal.coe_mul_bot_of_pos hp, EReal.bot_add]
    · simp only [hval _ x hx]
      rw [logAbs_eq_coe_log hx, ← EReal.coe_mul, ← EReal.coe_add]
      refine iInf_eq_of_tendsto_of_antitone (fun i j hij => ?_) (EReal.tendsto_coe.2 (hFlim _))
      exact EReal.coe_le_coe_iff.2 (hFanti _ hij)
  obtain ⟨x₀, hx₀⟩ := hne
  refine (isRegularizable_iInf_finsetSup_fsTerm hpos hanti ⟨x₀, ?_⟩).congr hinf
  rw [hinf, logAbs_eq_coe_log hx₀, ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_ne_bot _

/-! ### Finite sums in `EReal` -/

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    ((∑ i ∈ s, b i : ℝ) : EReal) = ∑ i ∈ s, (b i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

/-- If `a_i ≤ b_i` for all `i ∈ s` and `a_{i₀} + δ ≤ b_{i₀}`, then `∑ a_i + δ ≤ ∑ b_i`. -/
theorem finset_sum_add_le_sum_coe {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → EReal}
    {b : ι → ℝ} (hab : ∀ i ∈ s, a i ≤ b i) {i₀ : ι} (hi₀ : i₀ ∈ s) {δ : ℝ}
    (h : a i₀ + δ ≤ b i₀) : ∑ i ∈ s, a i + δ ≤ ∑ i ∈ s, (b i : EReal) := by
  rw [← Finset.add_sum_erase s a hi₀, ← Finset.add_sum_erase s _ hi₀, add_right_comm]
  exact add_le_add h (Finset.sum_le_sum fun i hi => hab i (Finset.mem_of_mem_erase hi))

/-- A positive lower bound for finitely many positive reals. -/
theorem exists_pos_forall_le_of_finset {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ d i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  · exact ⟨s.inf' hs d, (Finset.lt_inf'_iff hs).2 hd, fun i hi => Finset.inf'_le d hi⟩

/-- `ℛ(Y)` is stable under finite sums (FHX Lemma 5.11(3)). -/
theorem IsRegularizable.finset_sum [IsDomain A] [Algebra.FiniteType k A] {ι : Type*}
    (s : Finset ι) {u : ι → Berk k A → EReal} (hu : ∀ i ∈ s, IsRegularizable (u i)) :
    IsRegularizable fun x => ∑ i ∈ s, u i x := by
  classical
  have : Nonempty (Berk k A) := ⟨triv⟩
  induction s using Finset.induction_on with
  | empty => exact (isRegularizable_const 0).congr fun x => by simp
  | insert i s hi ih =>
    exact ((hu i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))).congr fun x => by
        rw [Finset.sum_insert hi]

/-! ### Step 3: series of regularizable functions -/

/-- The real FS function `b = 1 + max{0, log|z_1|, …, log|z_n|}` is regularizable, and so are its
positive rational multiples. -/
theorem isRegularizable_mul_std_add_one [Algebra.FiniteType k A] [Nonempty (Berk k A)] {r : ℚ}
    (hr : 0 < r) :
    IsRegularizable fun x : Berk k A =>
      (((r : ℝ) * ((FSData.std k A).evalReal x + 1) : ℝ) : EReal) := by
  refine (((FSData.std k A).addConst 1).smul r hr).isRegularizable.congr fun x => ?_
  rw [FSData.eval_smul, FSData.eval_addConst, ← FSData.coe_evalReal, ← EReal.coe_add,
    ← EReal.coe_mul]
  norm_num

universe u v

/-- **Step 3 of FHX Lemma 5.18**: a series `∑_j w_j` of nonnegative real functions with
`w_j ≤ 2^{-(j+1)} b`, `b = 1 + max{0, log|z_l|}`, where each `w_j` is zero or regularizable, is
regularizable: the regularizable functions `R_N = ∑_{j<N} w_j + 2^{-N} b` decrease to it
(`R_{N+1} - R_N = w_N - 2^{-(N+1)} b ≤ 0`), and FHX Lemma 5.11(2) applies. -/
theorem isRegularizable_tsum {k : Type u} [Field k] [IsAlgClosed k] [WuRegularization.{u, v} k] {A : Type v}
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    (w : ℕ → Berk k A → ℝ) (hw0 : ∀ j x, 0 ≤ w j x)
    (hwle : ∀ j x, w j x ≤ (1 / 2) ^ (j + 1) * ((FSData.std k A).evalReal x + 1))
    (hreg : ∀ j, (∀ x, w j x = 0) ∨ IsRegularizable fun x => (w j x : EReal)) :
    IsRegularizable fun x => ((∑' j, w j x : ℝ) : EReal) := by
  have : Nonempty (Berk k A) := ⟨triv⟩
  set b : Berk k A → ℝ := fun x => (FSData.std k A).evalReal x + 1 with hb_def
  have hsum : ∀ x, Summable fun j => w j x := fun x =>
    Summable.of_nonneg_of_le (hw0 · x) (hwle · x)
      ((summable_geometric_two.mul_right ((1 / 2) * b x)).congr fun j => by ring)
  have hS : ∀ N, IsRegularizable fun x => ((∑ j ∈ Finset.range N, w j x : ℝ) : EReal) := by
    intro N
    induction N with
    | zero => exact (isRegularizable_const 0).congr fun x => by simp
    | succ N ih =>
      rcases hreg N with h0 | hN
      · exact ih.congr fun x => by rw [Finset.sum_range_succ, h0 x, add_zero]
      · exact (ih.add hN).congr fun x => by rw [Finset.sum_range_succ, EReal.coe_add]
  have hB : ∀ N, IsRegularizable fun x => (((1 / 2 : ℝ) ^ N * b x : ℝ) : EReal) := by
    intro N
    refine (isRegularizable_mul_std_add_one (k := k) (A := A)
      (show (0 : ℚ) < (1 / 2) ^ N by positivity)).congr fun x => ?_
    push_cast
    rfl
  set R : ℕ → Berk k A → EReal := fun N x =>
    ((∑ j ∈ Finset.range N, w j x + (1 / 2 : ℝ) ^ N * b x : ℝ) : EReal) with hR_def
  have hR : ∀ N, IsRegularizable (R N) := fun N =>
    ((hS N).add (hB N)).congr fun x => (EReal.coe_add _ _).symm
  have hanti : ∀ x, Antitone fun N => R N x := by
    intro x
    refine antitone_nat_of_succ_le fun N => ?_
    simp only [hR_def, EReal.coe_le_coe_iff, Finset.sum_range_succ]
    have h1 := hwle N x
    have e : (1 / 2 : ℝ) ^ (N + 1) * b x = (1 / 2) ^ N * b x / 2 := by ring
    rw [e] at h1 ⊢
    linarith
  have hinf : ∀ x, (⨅ N, R N x) = ((∑' j, w j x : ℝ) : EReal) := by
    intro x
    refine iInf_eq_of_tendsto_of_antitone (hanti x) (EReal.tendsto_coe.2 ?_)
    have := (hsum x).hasSum.tendsto_sum_nat.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).mul_const (b x))
    rwa [zero_mul, add_zero] at this
  exact (IsRegularizable.of_antitone hR hanti
    ⟨triv, by rw [hinf]; exact EReal.coe_ne_bot _⟩).congr hinf

/-! ### Step 4: supporting functions and strictness -/

/-- **Growth of `log (1 + |f|)`** (FHX Lemma 5.8(1)): there is an integer `C ≥ 1` with
`log (1 + |f|) ≤ C b`, `b = 1 + max{0, log|z_l|}`, since `|f| ≤ exp(K max{0, log|z_l|} + K')`
and `log (1 + e^R) ≤ log 2 + R ≤ 1 + R` for `R ≥ 0`. -/
theorem exists_logOneAddAbs_le [Algebra.FiniteType k A] (f : A) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ x : Berk k A, logOneAddAbs f x ≤ C * ((FSData.std k A).evalReal x + 1) := by
  obtain ⟨K, K', hK, hK', hb⟩ := (FSData.std k A).exists_abs_le_exp {f}
  refine ⟨⌈K + K'⌉₊ + 1, by omega, fun x => ?_⟩
  have h1 := hb f (Finset.mem_singleton_self f) x
  rw [FSData.const_std, Rat.cast_zero, sub_zero] at h1
  have ht : 0 ≤ (FSData.std k A).evalReal x := FSData.evalReal_std_nonneg k A x
  set t := (FSData.std k A).evalReal x
  have hR : 0 ≤ K * t + K' := by positivity
  have h2 : logOneAddAbs f x ≤ 1 + (K * t + K') := by
    unfold logOneAddAbs
    have hpos : 0 < 1 + (x.val f : ℝ) := by positivity
    calc Real.log (1 + x.val f) ≤ Real.log (2 * Real.exp (K * t + K')) :=
          Real.log_le_log hpos (by linarith [Real.one_le_exp hR])
      _ = Real.log 2 + (K * t + K') := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 1 + (K * t + K') := by linarith [Real.log_two_lt_d9]
  have hC : K + K' ≤ (⌈K + K'⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : K * t ≤ (⌈K + K'⌉₊ : ℝ) * t := mul_le_mul_of_nonneg_right (by linarith) ht
  push_cast
  nlinarith

/-- A neighbourhood of `x` contains a set `{y : | |f|_y - |f|_x | < ε for all f ∈ F}` with `F`
finite and `ε > 0`: the topology is induced by the evaluations `y ↦ |f|_y`. -/
theorem exists_finset_of_mem_nhds {x : Berk k A} {V : Set (Berk k A)} (hV : V ∈ 𝓝 x) :
    ∃ (F : Finset A) (ε : ℝ), 0 < ε ∧
      ∀ y : Berk k A, (∀ f ∈ F, |(y.val f : ℝ) - x.val f| < ε) → y ∈ V := by
  rw [isInducing_toFun.nhds_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.1 hV
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, hI, t, ht, hIt⟩ := hW
  choose ε hε hball using fun f => Metric.mem_nhds_iff.1 (ht f)
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_forall_le_of_finset hI.toFinset ε fun f _ => hε f
  refine ⟨hI.toFinset, δ, hδ, fun y hy => hWV ?_⟩
  show toFun y ∈ W
  refine hIt fun f hf => hball f ?_
  have hf' : f ∈ hI.toFinset := hI.mem_toFinset.2 hf
  rw [Metric.mem_ball, NNReal.dist_eq]
  exact (hy f hf').trans_le (hδε f hf')

/-- **Supporting functions** (proof of FHX Lemma 5.18). Let `γ > 0`, `ε > 0`, `f ∈ A` and `x` a
point, `s₀ = |f|_x`. There are a regularizable `ℓ` and `δ > 0` with `ℓ ≤ γ log(1+|f|)`, equality
at `x`, and `ℓ + δ ≤ γ log(1+|f|)` where `| |f| - s₀ | ≥ ε`: for `s₀ > 0` take
`ℓ = γ (log(1+s₀) + p (log|f| - log s₀))`, `p = s₀/(1+s₀)` (`exists_supportLine_gap`); for
`s₀ = 0` take `ℓ = 0` and `δ = γ log(1+ε)`. -/
theorem exists_supportFun [Algebra.FiniteType k A] [Nonempty (Berk k A)] (f : A)
    (x : Berk k A) {γ : ℝ} (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ℓ : Berk k A → EReal) (δ : ℝ), 0 < δ ∧ IsRegularizable ℓ ∧
      (∀ y, ℓ y ≤ ((γ * logOneAddAbs f y : ℝ) : EReal)) ∧
      ℓ x = ((γ * logOneAddAbs f x : ℝ) : EReal) ∧
      ∀ y, ε ≤ |(y.val f : ℝ) - x.val f| →
        ℓ y + (δ : EReal) ≤ ((γ * logOneAddAbs f y : ℝ) : EReal) := by
  rcases (NNReal.coe_nonneg (x.val f)).eq_or_lt with h0 | hpos
  · -- `|f|_x = 0`: the supporting function is `0`
    refine ⟨fun _ => 0, γ * Real.log (1 + ε), mul_pos hγ (log_one_add_pos hε),
      (isRegularizable_const 0).congr fun _ => by simp, fun y => ?_, ?_, fun y hy => ?_⟩
    · show (0 : EReal) ≤ _
      exact_mod_cast mul_nonneg hγ.le (logOneAddAbs_nonneg f y)
    · simp [logOneAddAbs, ← h0]
    · show (0 : EReal) + _ ≤ _
      rw [zero_add, EReal.coe_le_coe_iff]
      refine mul_le_mul_of_nonneg_left ?_ hγ.le
      rw [← h0, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] at hy
      exact log_one_add_ge_of_le hε hy
  · -- `|f|_x > 0`: the supporting line at `s₀ = |f|_x`
    set s₀ : ℝ := (x.val f : ℝ) with hs₀
    obtain ⟨δ₀, hδ₀, hgap⟩ := exists_supportLine_gap hpos hε
    set p := supportSlope s₀ with hp
    set C := Real.log (1 + s₀) - p * Real.log s₀ with hC
    have hγp : 0 < γ * p := mul_pos hγ (supportSlope_pos hpos)
    have hval : ∀ y : Berk k A, y.val f ≠ 0 →
        ((γ * p : ℝ) : EReal) * logAbs f y + ((γ * C : ℝ) : EReal) =
          ((γ * supportLine s₀ (y.val f) : ℝ) : EReal) := by
      intro y hy
      rw [logAbs_eq_coe_log hy, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      simp only [supportLine, hC, ← hp]
      ring
    have hbot : ∀ y : Berk k A, y.val f = 0 →
        ((γ * p : ℝ) : EReal) * logAbs f y + ((γ * C : ℝ) : EReal) = ⊥ := by
      intro y hy
      rw [(logAbs_eq_bot_iff f y).2 hy, EReal.coe_mul_bot_of_pos hγp, EReal.bot_add]
    have hy0 : ∀ y : Berk k A, y.val f ≠ 0 → (0 : ℝ) < y.val f := fun y hy =>
      NNReal.coe_pos.2 (pos_iff_ne_zero.2 hy)
    have hx0 : x.val f ≠ 0 := fun h => by simp [hs₀, h] at hpos
    refine ⟨fun y => ((γ * p : ℝ) : EReal) * logAbs f y + ((γ * C : ℝ) : EReal), γ * δ₀,
      mul_pos hγ hδ₀, isRegularizable_coe_mul_logAbs_add f hγp _ ⟨x, hx0⟩, fun y => ?_, ?_,
      fun y hy => ?_⟩ <;> beta_reduce
    · by_cases hy : y.val f = 0
      · rw [hbot y hy]; exact bot_le
      · rw [hval y hy, EReal.coe_le_coe_iff]
        exact mul_le_mul_of_nonneg_left (supportLine_le hpos (hy0 y hy)) hγ.le
    · rw [hval x hx0, ← hs₀, supportLine_self]
      rfl
    · by_cases hyf : y.val f = 0
      · rw [hbot y hyf, EReal.bot_add]; exact bot_le
      · rw [hval y hyf, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have := mul_le_mul_of_nonneg_left (hgap _ (hy0 y hyf) hy) hγ.le
        rw [mul_add] at this
        exact this

/-- **FHX Lemma 5.18** (`lem:strict-exhaustion`). On a normal affine variety over a countable
trivially valued field, there is a strict exhaustion: a nonnegative regularizable `ρ` such that
for every `x` and every neighbourhood `V` of `x` there are a regularizable `ρ' ≤ ρ` with
`ρ'(x) = ρ(x)` and `δ > 0` with `ρ' + δ ≤ ρ` off `V`.

Enumerate `A = {f_0, f_1, …}`, choose integers `C_j ≥ 1` with `log(1+|f_j|) ≤ C_j b` and put
`ρ = ∑_j γ_j log(1+|f_j|)`, `γ_j = 2^{-(j+1)}/C_j`. For `x` and `V`, pick finitely many indices
`J` and `ε > 0` such that `V` contains `{y : | |f_j|_y - |f_j|_x | < ε, j ∈ J}`, and put
`ρ' = ∑_{j ∉ J} γ_j log(1+|f_j|) + ∑_{j ∈ J} ℓ_j` with the supporting functions `ℓ_j` of
`exists_supportFun`. -/
theorem exists_isStrictExhaustion {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [WuRegularization.{u, v} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] :
    ∃ ρ : Berk k A → EReal, IsStrictExhaustion ρ := by
  classical
  have : Nonempty (Berk k A) := ⟨triv⟩
  have := countable_of_finiteType k A
  obtain ⟨e, he⟩ := exists_surjective_nat A
  choose Cg hCg1 hCg using fun f : A => exists_logOneAddAbs_le (k := k) f
  set γ : ℕ → ℚ := fun j => 1 / (2 ^ (j + 1) * (Cg (e j) : ℚ)) with hγ_def
  have hγpos : ∀ j, 0 < γ j := fun j => by
    have : (0 : ℚ) < Cg (e j) := by exact_mod_cast hCg1 (e j)
    simp only [hγ_def]
    positivity
  have hγpos' : ∀ j, (0 : ℝ) < γ j := fun j => by exact_mod_cast hγpos j
  set w : ℕ → Berk k A → ℝ := fun j x => (γ j : ℝ) * logOneAddAbs (e j) x with hw_def
  have hw0 : ∀ j x, 0 ≤ w j x := fun j x => mul_nonneg (hγpos' j).le (logOneAddAbs_nonneg _ _)
  have hwle : ∀ j x, w j x ≤ (1 / 2) ^ (j + 1) * ((FSData.std k A).evalReal x + 1) := by
    intro j x
    have hC : (0 : ℝ) < Cg (e j) := by exact_mod_cast hCg1 (e j)
    calc w j x ≤ (γ j : ℝ) * (Cg (e j) * ((FSData.std k A).evalReal x + 1)) :=
          mul_le_mul_of_nonneg_left (hCg (e j) x) (hγpos' j).le
      _ = (1 / 2) ^ (j + 1) * ((FSData.std k A).evalReal x + 1) := by
          simp only [hγ_def]
          push_cast
          rw [div_pow, one_pow]
          field_simp
  have hwreg : ∀ j, IsRegularizable fun x => (w j x : EReal) := fun j =>
    ((isRegularizable_logOneAddAbs (e j)).smul (hγpos j)).congr fun x =>
      (EReal.coe_mul _ _).symm
  have hsum : ∀ x, Summable fun j => w j x := fun x =>
    Summable.of_nonneg_of_le (hw0 · x) (hwle · x)
      ((summable_geometric_two.mul_right ((1 / 2) * ((FSData.std k A).evalReal x + 1))).congr
        fun j => by ring)
  refine ⟨fun x => ((∑' j, w j x : ℝ) : EReal), ?_⟩
  refine ⟨isRegularizable_tsum w hw0 hwle fun j => Or.inr (hwreg j),
    fun x => EReal.coe_nonneg.2 (tsum_nonneg (hw0 · x)), fun x V hV => ?_⟩
  obtain ⟨F, ε, hε, hFV⟩ := exists_finset_of_mem_nhds hV
  set J : Finset ℕ := F.image (Function.surjInv he) with hJ_def
  choose ℓ δ hδ hℓreg hℓle hℓx hℓgap using fun j => exists_supportFun (e j) x (hγpos' j) hε
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_forall_le_of_finset J δ fun j _ => hδ j
  -- the series without the indices in `J`
  set w' : ℕ → Berk k A → ℝ := fun j x => if j ∈ J then 0 else w j x with hw'_def
  have hw'0 : ∀ j x, 0 ≤ w' j x := fun j x => by
    simp only [hw'_def]; split_ifs; exacts [le_rfl, hw0 j x]
  have hw'le : ∀ j x, w' j x ≤ w j x := fun j x => by
    simp only [hw'_def]; split_ifs; exacts [hw0 j x, le_rfl]
  have hsplit : ∀ y, ∑' j, w j y = ∑' j, w' j y + ∑ j ∈ J, w j y := by
    intro y
    have hv0 : ∀ j, 0 ≤ (if j ∈ J then w j y else 0) := fun j => by
      split_ifs; exacts [hw0 j y, le_rfl]
    have hvle : ∀ j, (if j ∈ J then w j y else 0) ≤ w j y := fun j => by
      split_ifs; exacts [le_rfl, hw0 j y]
    have hv : ∑' j, (if j ∈ J then w j y else 0) = ∑ j ∈ J, w j y := by
      rw [tsum_eq_sum (s := J) fun j hj => if_neg hj]
      exact Finset.sum_congr rfl fun j hj => if_pos hj
    have hdecomp : ∀ j, w j y = w' j y + (if j ∈ J then w j y else 0) := fun j => by
      by_cases hj : j ∈ J <;> simp [hw'_def, hj]
    rw [tsum_congr hdecomp, Summable.tsum_add
      (Summable.of_nonneg_of_le (hw'0 · y) (hw'le · y) (hsum y))
      (Summable.of_nonneg_of_le hv0 hvle (hsum y)), hv]
  refine ⟨fun y => ((∑' j, w' j y : ℝ) : EReal) + ∑ j ∈ J, ℓ j y, δ₀, hδ₀, ?_, fun y => ?_, ?_,
    fun y hy => ?_⟩
  · -- `ρ'` is regularizable
    refine (isRegularizable_tsum w' hw'0 (fun j y => (hw'le j y).trans (hwle j y))
      fun j => ?_).add (IsRegularizable.finset_sum J fun j _ => hℓreg j)
    by_cases hj : j ∈ J
    · exact Or.inl fun y => by simp [hw'_def, hj]
    · exact Or.inr ((hwreg j).congr fun y => by simp [hw'_def, hj])
  · -- `ρ' ≤ ρ`
    show _ ≤ ((∑' j, w j y : ℝ) : EReal)
    rw [hsplit, EReal.coe_add, ereal_coe_finset_sum]
    exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => hℓle j y)
  · -- `ρ'(x) = ρ(x)`
    show _ = ((∑' j, w j x : ℝ) : EReal)
    rw [hsplit, EReal.coe_add, ereal_coe_finset_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => hℓx j)
  · -- `ρ' + δ ≤ ρ` off `V`
    obtain ⟨f, hf, hfε⟩ : ∃ f ∈ F, ε ≤ |(y.val f : ℝ) - x.val f| := by
      by_contra hcon
      push Not at hcon
      exact hy (hFV y hcon)
    have hj₀ : Function.surjInv he f ∈ J := Finset.mem_image_of_mem _ hf
    have hej₀ : e (Function.surjInv he f) = f := Function.surjInv_eq he f
    show ((∑' j, w' j y : ℝ) : EReal) + ∑ j ∈ J, ℓ j y + (δ₀ : EReal) ≤
      ((∑' j, w j y : ℝ) : EReal)
    rw [hsplit, EReal.coe_add, ereal_coe_finset_sum, add_assoc]
    refine add_le_add le_rfl (finset_sum_add_le_sum_coe (fun j _ => hℓle j y) hj₀ ?_)
    refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 (hδ₀le _ hj₀))) ?_
    exact hℓgap _ y (by rw [hej₀]; exact hfε)

end EnvelopeProperty
