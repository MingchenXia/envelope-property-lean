/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Divisorial

/-!
# Divisibility from growth on `(ℙⁿ)^an`

Let `k` be a field with the trivial absolute value, `R = k[x₀, …, xₙ]` with `n ≥ 1`, and `σ` a
nonzero form. This file proves the divisibility lemma `lem:bj-divisibility` of the blueprint
chapter on Boucksom–Jonsson's global theory on `ℙⁿ` (`bj22.tex`, subsection "The compactification
lemma on projective space"), used in the proof of Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Lemma 5.10(2) (`lem:compactification`) on `ℙⁿ`
(`lem:bj-compactification-extend`):

> if `τ` is a form with `log|τ| - N log|σ| ≤ -β log|σ| + C` on `U_σ = {|σ| ≠ 0}`, then
> `σ^{⌊N - β⌋}` divides `τ` in `R`.

**Proof.** For a prime `p` of the factorial ring `R` and `s > 0`, the family
`N_s(f) = e^{-s ord_p(f)}` (with `e^{-∞} = 0`) satisfies the hypotheses of the graded extension
lemma `lem:bj-graded-extension` (`ProjBerk.IsGradedNorm`): it is multiplicative and ultrametric
because `ord_p` is a valuation, `1` on nonzero constants, and some `xᵢ` is not divisible by `p`
since `n ≥ 1` (`ProjBerk.exists_not_dvd_X`). The point `v_s = ProjBerk.ordPoint hp s` lies in
`U_σ`, and the hypothesis at `v_s` reads `-s ord_p(τ) + s N ord_p(σ) ≤ s β ord_p(σ) + C`; letting
`s → ∞` gives `ord_p(τ) ≥ (N - β) ord_p(σ) ≥ ⌊N - β⌋ ord_p(σ)` for every prime `p`, which is the
divisibility (`UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`).

## Deviations from the blueprint

* The blueprint factors `σ` into homogeneous primes. We use all primes `p` of `R` (homogeneity of
  `p` is not needed: the family `N_s` is evaluated on forms only), and
  `UniqueFactorizationMonoid.dvd_iff_emultiplicity_le` instead of an explicit factorization.
* The hypotheses `β ≥ 0`, `N ≥ β` and `deg τ = N e` are dropped: with the natural floor
  `⌊N - β⌋₊` (which is `0` when `N < β`) the statement holds for every form `τ` and every real
  `β`. The growth hypothesis is stated in real form at the points where `|σ| ≠ 0` and `|τ| ≠ 0`
  (`pow_floor_dvd_of_log_le`) and in the `EReal` form of the blueprint
  (`pow_floor_dvd_of_logAbs_le`).

We also record that a homogeneous divisor of a form has a homogeneous cofactor
(`EnvelopeProperty.exists_isHomogeneous_eq_mul_of_dvd`).

## Main results

* `homogeneousComponent_mul_of_isHomogeneous`, `exists_isHomogeneous_eq_mul_of_dvd`.
* `ProjBerk.exists_not_dvd_X`, `ProjBerk.isGradedNorm_ordNorm`, `ProjBerk.ordPoint`.
* `ProjBerk.pow_floor_dvd_of_log_le`, `ProjBerk.pow_floor_dvd_of_logAbs_le`
  (`lem:bj-divisibility`).
-/

open scoped NNReal ENNReal Topology

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Homogeneous cofactors -/

section Homogeneous

variable {R : Type*} [CommRing R] {ι : Type*}

/-- Multiplying by a form of degree `m` shifts homogeneous components by `m`:
`(φ ψ)_{m + d} = φ ψ_d`. -/
theorem homogeneousComponent_mul_of_isHomogeneous {m : ℕ} {φ : MvPolynomial ι R}
    (hφ : φ.IsHomogeneous m) (d : ℕ) (ψ : MvPolynomial ι R) :
    homogeneousComponent (m + d) (φ * ψ) = φ * homogeneousComponent d ψ := by
  rw [homogeneousComponent_mul, Finset.sum_eq_single (m, d)]
  · rw [homogeneousComponent_eq_self hφ]
  · rintro ⟨p₁, p₂⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h₁ : p₁ ≠ m := fun h => hne (Prod.ext h (by simp only at hp ⊢; omega))
    rw [homogeneousComponent_of_mem (m := p₁) hφ, if_neg h₁, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl : (m, d) ∈ _) h

/-- A form of degree `m` dividing a nonzero form `τ` of degree `D` has a homogeneous cofactor of
degree `D - m`, and `m ≤ D`. -/
theorem exists_isHomogeneous_eq_mul_of_dvd [IsDomain R] {m D : ℕ} {φ τ : MvPolynomial ι R}
    (hφ : φ.IsHomogeneous m) (hτ : τ.IsHomogeneous D) (hτ0 : τ ≠ 0) (h : φ ∣ τ) :
    m ≤ D ∧ ∃ ψ : MvPolynomial ι R, ψ.IsHomogeneous (D - m) ∧ τ = φ * ψ := by
  obtain ⟨ψ₀, rfl⟩ := h
  have hφ0 : φ ≠ 0 := left_ne_zero_of_mul hτ0
  have hψ0 : ψ₀ ≠ 0 := right_ne_zero_of_mul hτ0
  have hdeg := totalDegree_mul_of_isDomain hφ0 hψ0
  rw [hτ.totalDegree hτ0, hφ.totalDegree hφ0] at hdeg
  have hmD : m ≤ D := by omega
  refine ⟨hmD, homogeneousComponent (D - m) ψ₀, homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [← homogeneousComponent_mul_of_isHomogeneous hφ, Nat.add_sub_cancel' hmD,
    homogeneousComponent_eq_self hτ]

end Homogeneous

namespace ProjBerk

variable {k : Type u} [Field k] {n : ℕ}

/-! ### The points `v_s = e^{-s ord_p}` -/

/-- For `n ≥ 1`, no prime of `k[x₀, …, xₙ]` divides all the variables. -/
theorem exists_not_dvd_X (hn : n ≠ 0) {p : MvPolynomial (Fin (n + 1)) k} (hp : Prime p) :
    ∃ i, ¬ p ∣ X i := by
  by_contra! h
  have h₀ := hp.irreducible.associated_of_dvd (X_prime (i := (0 : Fin (n + 1)))).irreducible (h 0)
  have h₁ := hp.irreducible.associated_of_dvd (X_prime (i := Fin.last n)).irreducible
    (h (Fin.last n))
  have h01 := (h₀.symm.trans h₁).dvd
  rw [X_dvd_X] at h01
  exact hn (by simpa [Fin.ext_iff] using h01.symm)

variable {p : MvPolynomial (Fin (n + 1)) k}

/-- The family `N_s(f) = e^{-s ord_p(f)}` attached to a prime `p` and `s ∈ ℝ` (only its values on
forms matter). -/
def ordNorm (p : MvPolynomial (Fin (n + 1)) k) (s : ℝ) (_d : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k) : ℝ≥0 :=
  expOrd (expNeg s) (emultiplicity p f)

/-- For `s ≥ 0` and a prime `p` not dividing all variables, `e^{-s ord_p}` satisfies the
hypotheses of the graded extension lemma (`lem:bj-graded-extension`). -/
theorem isGradedNorm_ordNorm (hn : n ≠ 0) (hp : Prime p) {s : ℝ} (hs : 0 ≤ s) :
    IsGradedNorm (ordNorm p s) where
  map_zero d := by simp [ordNorm]
  map_C c hc := by
    have hu : IsUnit (C c : MvPolynomial (Fin (n + 1)) k) := (isUnit_iff_ne_zero.2 hc).map C
    have : ¬ p ∣ C c := fun hdvd => hp.not_isUnit (isUnit_of_dvd_unit hdvd hu)
    rw [ordNorm, emultiplicity_eq_zero.2 this, expOrd_zero]
  map_mul {d e} {f g} _ _ := by
    simp only [ordNorm, emultiplicity_mul hp, expOrd_add]
  map_add_le {d} {f g} _ _ := by
    simp only [ordNorm]
    rw [← (expOrd_antitone (expNeg_le_one hs)).map_min]
    exact expOrd_antitone (expNeg_le_one hs) min_le_emultiplicity_add
  sup_X := by
    obtain ⟨i, hi⟩ := exists_not_dvd_X hn hp
    refine le_antisymm (Finset.sup_le fun j _ => expOrd_le_one (expNeg_le_one hs) _) ?_
    refine le_trans ?_ (Finset.le_sup (f := fun j => ordNorm p s 1 (X j)) (Finset.mem_univ i))
    simp [ordNorm, emultiplicity_eq_zero.2 hi]

/-- The point `v_s ∈ (ℙⁿ)^an`, the graded extension of `|f| = e^{-s ord_p(f)}` on forms. -/
def ordPoint (hn : n ≠ 0) (hp : Prime p) {s : ℝ} (hs : 0 ≤ s) : ProjBerk k n :=
  ofGradedNorm (isGradedNorm_ordNorm hn hp hs)

theorem ordPoint_val_of_isHomogeneous (hn : n ≠ 0) (hp : Prime p) {s : ℝ} (hs : 0 ≤ s) {c : ℕ}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous c) :
    (ordPoint hn hp hs).1.val f = expNeg s ^ multiplicity p f ∨ f = 0 := by
  by_cases hf0 : f = 0
  · exact Or.inr hf0
  left
  rw [ordPoint, ofGradedNorm_val_of_isHomogeneous _ hf, ordNorm,
    (FiniteMultiplicity.of_prime_left hp hf0).emultiplicity_eq_multiplicity, expOrd_coe]

theorem _root_.EnvelopeProperty.expNeg_pos (s : ℝ) : 0 < expNeg s := by
  rw [← NNReal.coe_pos]
  exact Real.exp_pos _

theorem _root_.EnvelopeProperty.log_expNeg_pow (s : ℝ) (m : ℕ) :
    Real.log ((expNeg s ^ m : ℝ≥0) : ℝ) = -s * m := by
  rw [NNReal.coe_pow, Real.log_pow]
  change (m : ℝ) * Real.log (Real.exp (-s)) = _
  rw [Real.log_exp]
  ring

/-! ### Divisibility from growth (`lem:bj-divisibility`) -/

/-- A real number `K` with `s K ≤ C` for all `s > 0` is `≤ 0`. -/
theorem _root_.EnvelopeProperty.nonpos_of_forall_mul_le {K C : ℝ}
    (h : ∀ s : ℝ, 0 < s → s * K ≤ C) : K ≤ 0 := by
  by_contra! hK
  have hs : 0 < (|C| + 1) / K := div_pos (by positivity) hK
  have := h _ hs
  rw [div_mul_cancel₀ _ hK.ne'] at this
  linarith [le_abs_self C]

variable {σ : MvPolynomial (Fin (n + 1)) k}

/-- **Divisibility from growth** (`lem:bj-divisibility`), real form. Let `n ≥ 1`, `σ ≠ 0` a form
and `τ` a form such that `log|τ| - N log|σ| ≤ -β log|σ| + C` at every point where `|σ| ≠ 0` and
`|τ| ≠ 0`. Then `σ^{⌊N - β⌋₊}` divides `τ`. -/
theorem pow_floor_dvd_of_log_le (hn : n ≠ 0) {d c : ℕ} (hσ : σ.IsHomogeneous d) (hσ0 : σ ≠ 0)
    {τ : MvPolynomial (Fin (n + 1)) k} (hτ : τ.IsHomogeneous c) {N : ℕ} {β C : ℝ}
    (h : ∀ v : ProjBerk k n, v.1.val σ ≠ 0 → v.1.val τ ≠ 0 →
      Real.log (v.1.val τ) - N * Real.log (v.1.val σ) ≤ -β * Real.log (v.1.val σ) + C) :
    σ ^ ⌊(N : ℝ) - β⌋₊ ∣ τ := by
  by_cases hτ0 : τ = 0
  · rw [hτ0]; exact dvd_zero _
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (pow_ne_zero _ hσ0)]
  intro p hp
  rw [emultiplicity_pow hp, (FiniteMultiplicity.of_prime_left hp hσ0).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hp hτ0).emultiplicity_eq_multiplicity, ← Nat.cast_mul,
    Nat.cast_le]
  set mσ := multiplicity p σ
  set mτ := multiplicity p τ
  -- the growth bound at the points `v_s`
  have hK : ((N : ℝ) - β) * mσ - mτ ≤ 0 := by
    refine nonpos_of_forall_mul_le (C := C) fun s hs => ?_
    have hσv : (ordPoint hn hp hs.le).1.val σ = expNeg s ^ mσ :=
      (ordPoint_val_of_isHomogeneous hn hp hs.le hσ).resolve_right hσ0
    have hτv : (ordPoint hn hp hs.le).1.val τ = expNeg s ^ mτ :=
      (ordPoint_val_of_isHomogeneous hn hp hs.le hτ).resolve_right hτ0
    have h₁ := h (ordPoint hn hp hs.le) (by rw [hσv]; exact pow_ne_zero _ (expNeg_pos s).ne')
      (by rw [hτv]; exact pow_ne_zero _ (expNeg_pos s).ne')
    rw [hσv, hτv, log_expNeg_pow, log_expNeg_pow] at h₁
    nlinarith
  have hmσ : (0 : ℝ) ≤ mσ := Nat.cast_nonneg _
  have key : ((⌊(N : ℝ) - β⌋₊ * mσ : ℕ) : ℝ) ≤ mτ := by
    push_cast
    rcases le_or_gt 0 ((N : ℝ) - β) with hNβ | hNβ
    · calc (⌊(N : ℝ) - β⌋₊ : ℝ) * mσ ≤ ((N : ℝ) - β) * mσ :=
            mul_le_mul_of_nonneg_right (Nat.floor_le hNβ) hmσ
        _ ≤ mτ := by linarith
    · rw [Nat.floor_eq_zero.2 (hNβ.trans one_pos), Nat.cast_zero, zero_mul]
      exact Nat.cast_nonneg _
  exact_mod_cast key

/-- **Divisibility from growth** (`lem:bj-divisibility`), in the `EReal` form of the blueprint:
if `log|τ| - N log|σ| ≤ -β log|σ| + C` on `U_σ`, then `σ^{⌊N - β⌋₊}` divides `τ`. -/
theorem pow_floor_dvd_of_logAbs_le (hn : n ≠ 0) {d c : ℕ} (hσ : σ.IsHomogeneous d) (hσ0 : σ ≠ 0)
    {τ : MvPolynomial (Fin (n + 1)) k} (hτ : τ.IsHomogeneous c) {N : ℕ} {β C : ℝ}
    (h : ∀ v : ProjBerk k n, v.1.val σ ≠ 0 →
      logAbs τ v - (N : EReal) * logAbs σ v ≤ -(β : EReal) * logAbs σ v + (C : EReal)) :
    σ ^ ⌊(N : ℝ) - β⌋₊ ∣ τ := by
  refine pow_floor_dvd_of_log_le (C := C) hn hσ hσ0 hτ fun v hσv hτv => ?_
  have h₁ := h v hσv
  rw [logAbs_def, logAbs_def, ENNReal.log_of_nnreal hσv, ENNReal.log_of_nnreal hτv] at h₁
  rw [← EReal.coe_natCast, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h₁
  exact h₁

end ProjBerk

end EnvelopeProperty
