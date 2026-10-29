import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # The arithmetic iteration in positive Hodge-diagonal vanishing

The geometric diagonal inequality is an explicit premise of the criterion.
This file neither assumes nor proves a geometric Deligne--Illusie theorem.
-/

namespace EnvelopeProperty.Vanishing.FrobeniusIteration

/-- Exponential growth, including the zeroth iterate. -/
theorem succ_le_pow {p : ℕ} (hp : 2 ≤ p) (r : ℕ) : r + 1 ≤ p ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ]
    have hpos : 0 < p ^ r := pow_pos (by omega : 0 < p) r
    nlinarith

/-- A positive starting exponent can reach any prescribed threshold by
repeated Frobenius multiplication. -/
theorem exists_le_mul_pow {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∃ r : ℕ, N ≤ m * p ^ r := by
  refine ⟨N, ?_⟩
  have hpow := succ_le_pow hp N
  nlinarith

/-- Descend a proposition through finitely many amplification steps.
This works directly with zero-group assertions and needs no dimensions. -/
theorem of_mul_pow (P : ℕ → Prop) {p : ℕ} (hp : 0 < p)
    (hstep : ∀ m : ℕ, 0 < m → P (p * m) → P m)
    {m : ℕ} (hm : 0 < m) (r : ℕ) (h : P (m * p ^ r)) : P m := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    apply ih
    apply hstep (m * p ^ r) (Nat.mul_pos hm (pow_pos hp r))
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- Eventual truth descends to every positive exponent.  The one-step
descent must be supplied separately; it is not a Deligne--Illusie axiom. -/
theorem of_eventually (P : ℕ → Prop) {p : ℕ} (hp : 2 ≤ p)
    (hstep : ∀ m : ℕ, 0 < m → P (p * m) → P m)
    (heventual : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → P m)
    {m : ℕ} (hm : 0 < m) : P m := by
  obtain ⟨N, hN⟩ := heventual
  obtain ⟨r, hr⟩ := exists_le_mul_pow hp hm N
  exact of_mul_pow P (by omega : 0 < p) hstep hm r (hN _ hr)

/-- Iterate the one-step inequality without assuming monotonicity at
unrelated exponents. -/
theorem le_mul_pow (D : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hstep : ∀ m : ℕ, 0 < m → D m ≤ D (p * m))
    {m : ℕ} (hm : 0 < m) (r : ℕ) : D m ≤ D (m * p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hpos : 0 < m * p ^ r := Nat.mul_pos hm (pow_pos hp r)
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      ih.trans (hstep (m * p ^ r) hpos)

/-- Eventual zero propagates to every positive exponent along an
amplification inequality. No conclusion is asserted at exponent zero. -/
theorem eq_zero_of_eventually_eq_zero (D : ℕ → ℕ) {p : ℕ} (hp : 2 ≤ p)
    (hstep : ∀ m : ℕ, 0 < m → D m ≤ D (p * m))
    (heventual : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → D m = 0)
    {m : ℕ} (hm : 0 < m) : D m = 0 := by
  obtain ⟨N, hN⟩ := heventual
  obtain ⟨r, hr⟩ := exists_le_mul_pow hp hm N
  have hle := le_mul_pow D (by omega : 0 < p) hstep hm r
  rw [hN _ hr] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- A vanishing finite diagonal annihilates each of its summands. -/
theorem component_eq_zero_of_eventually_sum_eq_zero {ι : Type*} [Fintype ι]
    (d : ι → ℕ → ℕ) {p : ℕ} (hp : 2 ≤ p)
    (hstep : ∀ m : ℕ, 0 < m → (∑ i, d i m) ≤ ∑ i, d i (p * m))
    (heventual : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i, d i m = 0)
    {m : ℕ} (hm : 0 < m) (i : ι) : d i m = 0 := by
  classical
  have hsum : (∑ i, d i m) = 0 :=
    eq_zero_of_eventually_eq_zero (fun m => ∑ i, d i m) hp hstep (by
      obtain ⟨N, hN⟩ := heventual
      exact ⟨N, fun m hm => Finset.sum_eq_zero (fun i _ => hN m hm i)⟩) hm
  have hle : d i m ≤ ∑ j, d j m := Finset.single_le_sum (fun j _ => Nat.zero_le (d j m))
    (Finset.mem_univ i)
  rw [hsum] at hle
  exact Nat.eq_zero_of_le_zero hle

end EnvelopeProperty.Vanishing.FrobeniusIteration
