import Mathlib.Analysis.Subadditive

/-! # Fekete convergence with subadditivity only beyond a fixed bound -/
open Set Filter Topology
noncomputable section
namespace EnvelopeProperty.TailSubadditive

variable {u : ℕ → ℝ} {N : ℕ}

/-- The original arithmetic progression stays entirely within the given tail. -/
theorem apply_mul_add_le
    (h : ∀ m n, N ≤ m → N ≤ n → u (m + n) ≤ u m + u n)
    {n r : ℕ} (hn : N ≤ n) (hr : N ≤ r) (k : ℕ) :
    u (k * n + r) ≤ k * u n + u r := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      u ((k + 1) * n + r) = u (n + (k * n + r)) := by congr 1; ring
      _ ≤ u n + u (k * n + r) := h _ _ hn (hr.trans (Nat.le_add_left _ _))
      _ ≤ u n + (k * u n + u r) := add_le_add le_rfl ih
      _ = (k + 1 : ℕ) * u n + u r := by push_cast; ring

/-- One strictly smaller normalized term in the tail bounds every later term. -/
theorem eventually_div_lt_of_div_lt
    (h : ∀ m n, N ≤ m → N ≤ n → u (m + n) ≤ u m + u n)
    {L : ℝ} {n : ℕ} (hn : N ≤ n) (hn0 : n ≠ 0) (hL : u n / n < L) :
    ∀ᶠ p in atTop, u p / p < L := by
  refine .atTop_of_arithmetic hn0 fun r _ => ?_
  let s := N * n + r
  have hs : N ≤ s := by dsimp [s]; nlinarith [Nat.pos_of_ne_zero hn0]
  have A : Tendsto (fun x : ℝ => (u n + u s / x) / (n + s / x))
      atTop (𝓝 ((u n + 0) / (n + 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)) (by exact_mod_cast hn0)
  have B : Tendsto (fun x : ℝ => (x * u n + u s) / (x * n + s))
      atTop (𝓝 (u n / n)) := by
    rw [add_zero, add_zero] at A
    refine A.congr' ((eventually_ne_atTop 0).mono fun x hx => ?_)
    simp only [add_div' _ _ _ hx, div_div_div_cancel_right₀ hx, mul_comm]
  have he : ∀ᶠ k : ℕ in atTop, u (k * n + s) / ((k * n + s : ℕ) : ℝ) < L := by
    refine ((B.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono fun k hk => ?_
    refine lt_of_le_of_lt ?_ hk
    simp only [Function.comp_def, ← Nat.cast_add, ← Nat.cast_mul]
    exact div_le_div_of_nonneg_right (apply_mul_add_le h hn hs k) (by positivity)
  have he' : ∀ᶠ k : ℕ in atTop,
      u (n * (k + N) + r) / ((n * (k + N) + r : ℕ) : ℝ) < L := by
    refine he.mono fun k hk => ?_
    have heq : n * (k + N) + r = k * n + s := by dsimp [s]; ring
    simpa only [heq] using hk
  rw [← map_add_atTop_eq_nat N]
  exact he'

/-- The genuine tail infimum, with no prescription of the early terms. -/
def limit (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  sInf ((fun n : ℕ => u n / n) '' Ici (max N 1))

/-- Nonnegative tail subadditivity implies full sequential Fekete convergence. -/
theorem tendsto_limit
    (h : ∀ m n, N ≤ m → N ≤ n → u (m + n) ≤ u m + u n)
    (hu : ∀ n, N ≤ n → 0 ≤ u n) :
    0 ≤ limit u N ∧ Tendsto (fun n => u n / n) atTop (𝓝 (limit u N)) := by
  have hb : BddBelow ((fun n : ℕ => u n / n) '' Ici (max N 1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact div_nonneg (hu n ((le_max_left _ _).trans hn)) (by positivity)
  have he : ((fun n : ℕ => u n / n) '' Ici (max N 1)).Nonempty :=
    ⟨_, mem_image_of_mem _ (mem_Ici.mpr (le_refl (max N 1)))⟩
  refine ⟨le_csInf he ?_, tendsto_order.2 ⟨?_, ?_⟩⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact div_nonneg (hu n ((le_max_left _ _).trans hn)) (by positivity)
  · intro l hl
    refine eventually_atTop.2 ⟨max N 1, fun n hn => hl.trans_le ?_⟩
    exact csInf_le hb ⟨n, hn, rfl⟩
  · intro L hL
    obtain ⟨x, hx, hxL⟩ := exists_lt_of_csInf_lt he hL
    obtain ⟨n, hn, rfl⟩ := hx
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    exact eventually_div_lt_of_div_lt h ((le_max_left N 1).trans hn)
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)) hxL

end EnvelopeProperty.TailSubadditive
